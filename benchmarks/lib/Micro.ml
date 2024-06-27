open Core
open ASTs
open List.Let_syntax

let ternary_match_gen ~table_id ~bitwidth ~num_ternary ~num_exact =
  let var (s : int -> string) (f : int -> int) (i : int) = Var.make (s @@ f i) bitwidth in
  let hdr = Printf.sprintf "hdr.t%d.h%d" table_id in
  let ternary_offset = (+) num_ternary in
  let exact_offset = (+) (2 * num_ternary) in
  let ctrl = Printf.sprintf "_symb$t%d$match_%d" table_id in
  let isValid hdr =
    Expr.var (Var.make (Printf.sprintf "%s.is_valid" @@ Var.str hdr) 1)
  in
  let x hdr = Expr.var (Var.map hdr ~f:(Printf.sprintf "%s.x")) in
  let dont_care match_ =
    Expr.var (Var.make (Printf.sprintf "%s$DONT_CARE" @@ Var.str match_) 1)
  in
  let (%.) a b = a |> b in
  let ternary_headers = List.init num_ternary ~f:(var hdr ternary_offset) in
  let exact_headers   = List.init num_exact   ~f:(var hdr exact_offset) in
  let ternary_matches = List.init num_ternary ~f:(var ctrl ternary_offset) in
  let exact_matches   = List.init num_exact   ~f:(var ctrl exact_offset) in
  let test b = BExpr.(eq_ b (Expr.bvi 1 1)) in
  let open GCL in
  sequence @@
  List.mapi ternary_headers ~f:(fun i hdr ->
      assume @@
      BExpr.eq_ (isValid hdr) @@
      Expr.var @@ Var.make (ctrl i) 1
    )
  @ List.map exact_headers ~f:(fun hdr ->
      assume @@
      BExpr.eq_ (isValid hdr) @@
      Expr.bvi 1 1
  ) @
  List.map2_exn ternary_headers ternary_matches ~f:(fun hdr match_x ->
      let open GCL in
      ite (test (dont_care match_x)) (
        skip
      ) (sequence [
          assert_ (test (hdr %. isValid));
          assume BExpr.(eq_ (hdr %. x) (Expr.var match_x));
        ] )
    ) @
  List.map2_exn exact_headers exact_matches ~f:(fun hdr match_x ->
      let open GCL in
      sequence [
        assert_ (test (hdr %. isValid));
        assume BExpr.(eq_ (hdr %. x) (Expr.var match_x));
      ]
    )

let partition ~n:n_things ~into:m_buckets =
  (* this ith element has the number of elements in bucket i *)
    List.init m_buckets ~f:(fun i ->
        (n_things / m_buckets) + if i < (n_things % m_buckets) then 1 else 0
    )


let ternary_match_benchmark ~bitwidth ~max_tables ~max_keys =
  let open DependentTypeChecker in
  Printf.printf "nternary,nexact,ntables,is_mono,time_ms,inferred_size,npaths\n%!";
  let num_keys = max_keys in (* let%map num_keys = List.init max_keys ~f:Int.succ in *)
  let%bind num_ternary = List.init (num_keys + 1) ~f:Fn.id in
  let num_exact = num_keys - num_ternary in
  let%bind mono = [true; false] in
  let%bind num_tables = 
      List.init (max_tables - 1) ~f:(fun t -> t + 1) 
  in
  if num_tables > num_keys then [] else
  let keys_per_table = partition ~n:num_keys ~into:num_tables in
  let ternary_per_table = partition ~n:num_ternary ~into:num_tables in
  let exp =
    List.init num_tables ~f:(fun table_id ->
        let num_keys = List.nth_exn keys_per_table table_id in
        let num_ternary = List.nth_exn ternary_per_table table_id in
        let num_exact = num_keys - num_ternary in
        let gcl = ternary_match_gen ~table_id ~bitwidth ~num_ternary ~num_exact in
        let hoare = HoareNet.of_gpl (GPL.of_gcl gcl) in
        (* if encap then
          HoareNet.triple BExpr.true_ hoare BExpr.true_
        else *)
          hoare
      )
    |> HoareNet.sequence
  in
  Log.debug "%s" @@ lazy (HoareNet.to_string exp);
  let c = Clock.start () in
  let exp = HoareNet.triple BExpr.true_ exp BExpr.true_ in
  let qe = if mono then `Conc else `Mono in
  let psi = HoareNet.infer ~qe exp None None in
  let runtime = Clock.stop c in
  Printf.printf "%d,%d,%d,%b,%f,%d,%d\n%!" num_ternary num_exact num_tables mono runtime (BExpr.size psi) Int.(2 ** num_ternary)
  |> return

(* BEGIN REPURPOSED AVENIR EXPERIMENTS *)
let gen_var fmt width idx =
  Var.make (fmt idx) width

let rec gen_vars fmt width curr max =
  if curr >= max then []
  else if curr < 0 then
    failwith
    @@ Printf.sprintf "Cannot generate variable with negative index %d" curr
  else gen_var fmt width curr :: gen_vars fmt width (curr + 1) max

let make_param table act_idx param_name =
  Printf.sprintf "_symb$%s$%d$arg$%s" table act_idx param_name

let gen_param table act_idx param_idx =
  Printf.sprintf "x%d" param_idx
  |> make_param table act_idx

let gen_arg table act_idx width arg_idx =
  gen_var (gen_param table act_idx) width arg_idx

let outvar = Var.make "standard_metadata.egress_spec" 9

let gen_out_act _ _ (*table act_idx*) =
  let open Primitives.Action in
  (* let a = gen_arg table act_idx 9 0 in *)
  (* ([a], [assign outvar @@ Expr.var a] ) *)
  [], [assign outvar @@ Expr.bvi 511 9]

let gen_nop = ([],[])

let gen_exact_table name data_plane_keys actions =
  let open GCL in
  let open BExpr in
  let open Expr in
  let symbify = Printf.sprintf "_symb$%s$match_%d" name in
  let cp_keys = List.mapi ~f:(fun idx x -> Var.make (symbify idx) (Var.size x)) data_plane_keys in
  sequence @@
  List.map2_exn data_plane_keys cp_keys ~f:(fun d c ->
      assume (eq_ (var d) (var c))
    )
  @ [
    GCL.table (name, cp_keys, actions)
  ]

let gen_assignable_table name width nacts nassigns =
  let key = Printf.sprintf "%s.key" name in
  let dp_keys = [Var.make key width] in
  let actions =
    List.init nassigns ~f:(gen_out_act name) @
    List.init (nacts - nassigns) ~f:(fun _ -> gen_nop)
  in
  gen_exact_table name dp_keys actions

let gen_assignable_pipeline width ntables nacts nassigns =
  ASTs.GCL.sequence @@
  List.init ntables ~f:(fun i ->
      let name = Printf.sprintf "table_%d" i in
      gen_assignable_table name width nacts nassigns
  )

let determined_forwarding ~bitwidth ~max_tables ~max_acts ~max_assigns =
  let%bind mono = [true; false] in 
  let%bind ntables = List.init max_tables ~f:(Int.succ) in
  let%bind nacts = List.init max_acts ~f:(Int.succ) in
  let max_assigns = Int.min nacts max_assigns in
  let%map nassigns = List.init max_assigns ~f:Int.succ in
  assert (nassigns > 0);
  let open ASTs.GCL in
  let open BExpr in
  let open Expr in
  let gcl = gen_assignable_pipeline bitwidth ntables nacts nassigns in
  let gcl = seq gcl @@ assert_ @@ not_ @@ eq_ (var outvar) (bvi 509 9) in
  let c = Clock.start () in
  let psi = if mono then Qe.mono gcl else Qe.concolic gcl in
  Log.qe "got %s" @@ lazy (BExpr.to_smtlib psi);
  let time = Clock.stop c in
  Printf.printf "%d,%d,%d,%b,%f,%d,%d\n%!" ntables nacts nassigns mono time (BExpr.size psi) Int.(nacts ** ntables)


(* Join Conditions Benchmark*)
let gen_meta name bitwidth i = Var.make (Printf.sprintf "%s.meta%d" name i) bitwidth
let gen_open name bitwidth nkeys nouts =
  let open Primitives in
  let xify = Printf.sprintf "%s.x%d" name in
  let dp_keys = gen_vars xify bitwidth 0 nkeys in
  let param act_id x =
    (* ACT IDX IS THE INDEX OF THE ACTION NOT THE PARAMETER *)
    Printf.sprintf "_symb$%s$%d$arg$%s" name act_id x |> Var.make
  in
  let hit = Var.make (Printf.sprintf "%s.hit" name) 1 in
  let meta i = gen_meta name bitwidth i in
  let m i = param 0 (Printf.sprintf "m%d" i) bitwidth in
  let actions = [
      (* Assign hit = 1; (metai := mi for 0 <= i < nouts) *)
      (List.init nouts ~f:m,
       Action.assign hit (Expr.bvi 1 1)
       :: List.init nouts ~f:(fun i -> Action.assign (meta i) Expr.(var (m i))))
      ;
      (* Assign hit = 0 *)
      [],[Action.assign hit (Expr.bvi 0 1)]
    ]
  in
  (gen_exact_table name dp_keys actions, Expr.var hit)

let gen_close close_name open_name bitwidth nouts =
  let open Primitives in
  let metaify i = gen_meta open_name bitwidth i |> Var.str in
  let dp_keys = gen_vars metaify bitwidth 0 nouts in
  let hit = Var.make (Printf.sprintf "%s.hit" close_name) 1 in
  let actions = [
    (* Assign hit = 1; *)
    [], [ Action.assign hit (Expr.bvi 1 1) ];
    (* Do nothing *)
    [], [ Action.assign hit (Expr.bvi 0 1) ]
    ]
  in
  (gen_exact_table close_name dp_keys actions, Expr.var hit)

let gen_join_pair bitwidth nvars pair_idx =
  (* nvars is the number of variables used to join two tables together *)
  let open DependentTypeChecker in
  let open ASTs in
  let open_name = Printf.sprintf "open_%d" pair_idx in
  let close_name = Printf.sprintf "close_%d" pair_idx in
  let open_table, open_hit = gen_open open_name bitwidth 1 nvars in
  let close_table, close_hit = gen_close close_name open_name bitwidth nvars in
  let pipe = GPL.of_gcl @@ GCL.seq open_table close_table in
  let phi = BExpr.(eq_ open_hit close_hit) in
  HoareNet.of_gpl pipe, phi


let join_conditions ~bitwidth ~max_joins ~max_join_vars =
  let open DependentTypeChecker in
  let%bind njoins = List.init max_joins ~f:(Int.succ) in
  let%bind nvars = List.init max_join_vars ~f:(Int.succ) in
  let%map mono = [true; false] in
  let exp, phi  = List.unzip @@ List.init njoins ~f:(gen_join_pair bitwidth nvars) in
  let exp = HoareNet.(triple BExpr.true_ (sequence exp) (BExpr.ands_ phi)) in
  Log.debug "%s" @@ lazy (HoareNet.to_string exp);
  let c = Clock.start () in
  let qe = if mono then `Mono else `Conc in 
  let psi = HoareNet.infer ~qe exp None None in
  let time_ms = Clock.stop c in
  Log.debug "Got %s" @@ lazy (BExpr.to_smtlib psi);
  Printf.printf "%d,%d,%b,%f,%d,%d\n%!" njoins nvars mono time_ms (BExpr.size psi) Int.(4 ** njoins)
