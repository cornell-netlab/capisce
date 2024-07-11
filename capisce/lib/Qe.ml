open Core
open ASTs

let solver_to_string = function
  | `Z3 -> "z3"
  | `CVC4 -> "CVC4"
  | `Princess -> "Princess"

let solve_wto solver ?(with_timeout:int option) cvs smt =
  match solver, with_timeout with
  | `Z3, Some timeout ->
    Solver.run_z3 (Smt.assert_apply ~timeout cvs smt)
  | `Z3, None ->
    Solver.run_z3 (Smt.assert_apply cvs smt)
  | `Z3Light,_ ->
    Solver.run_z3 (Smt.assert_apply_light cvs smt)
  | `Princess, _ ->
    Solver.run_princess (Smt.simplify cvs smt)

let dp_removed phi =
  let dvs, _ = BExpr.vars phi in
  List.is_empty dvs && BExpr.qf phi 

let z3_simplify cvs phi = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify phi)))

let solve_one ?(solver=`Z3) ~qe phi : (BExpr.t, BExpr.t) Result.t =
  let open Result.Let_syntax in
  Log.qe "solve_one(%s)" @@ lazy (solver_to_string solver);
  let (dvs, _) = BExpr.vars phi in
  List.iter dvs ~f:BExpr.incr_q;
  (* let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in *)
  let qphi = BExpr.(forall dvs phi) in
  let%bind qf_phi = qe (solve_wto solver) qphi in
  if dp_removed qf_phi then
    Result.Ok qf_phi
  else
    Result.Error qf_phi

let solve_one_option ?(solver=`Z3) ~qe phi =
  solve_one ~solver ~qe phi
  |> Result.ok

let nikolaj_please (solver : ?with_timeout:int -> Var.t list -> string -> string) phi : (BExpr.t, BExpr.t) Result.t =
  Log.qe_s "Nikolaj pleaseeeeeee";
  let _, cvs = BExpr.vars phi in
  let res = solver ~with_timeout:2000 cvs (BExpr.to_smtlib phi) in
  if BottomUpQe.check_success res then
    let phi' = Solver.of_smtlib ~dvs:[] ~cvs res in
    if BExpr.qf phi' then
      Result.Ok phi'
    else 
      Result.Error phi
  else
    let () = Log.smt "Solver failed with message:\n%s" @@ lazy res in
    if String.is_substring res ~substring:"canceled" then
      Result.Error phi
    else
      let partial_fee = Solver.of_smtlib ~dvs:[] ~cvs res in
      Result.Error partial_fee

let rec and_then tactics input =
  match tactics with
  | [] -> None
  | tactic::more_tactics ->
    match tactic input with
    | Result.Ok result -> Some result
    | Result.Error bad_result ->
      and_then more_tactics bad_result

let rec orelse thunks ~input =
  match thunks with
  | [] -> None
  | thunk::more_thunks ->
    match thunk input with
    | None -> orelse more_thunks ~input
    | Some x -> Some x

let implies phi1 phi2 =
  let cond = BExpr.(and_ phi1 (not_ phi2)) in
  let cvs = BExpr.vars cond |> Tuple2.uncurry (@) in
  Solver.check_unsat cvs cond
    ~timeout:(Some 2000)

let implies_model consts phi1 phi2 : Model.t option =
  Log.smt "PREMISE:\n%s\n------" @@ lazy (BExpr.to_smtlib phi1);
  Log.smt "CONSEQU:\n%s\n------" @@ lazy (BExpr.to_smtlib phi2);
  let cond = BExpr.(and_ phi1 (not_ phi2)) in
  Solver.check_sat_model consts cond
    ~timeout:(Some 2000)

let sufficient ~vc ~prog =
  let program_spec = vc prog in
  fun phi ->
  Log.qe_s "Checking sufficiency";
  implies phi program_spec

let nall_paths = ref 0

let hybrid_strategy vc = 
  orelse ~input:vc
  [
    and_then [
      solve_one ~solver:`Z3 ~qe:(nikolaj_please);
      solve_one ~solver:`Princess ~qe:(nikolaj_please);
      solve_one ~solver:`Z3 ~qe:(nikolaj_please);
    ];
   (* solve_one_option ~solver:`Princess ~qe:BottomUpQe.cnf_qe_result; *)
   ]

let check_sufficiency gcl =
  let _, psv = Psv.passify gcl in
  Log.qe "[cegqe] Passive :\n%s" @@ lazy (Psv.to_string psv);
  let all_passive_consts = Psv.vars psv in
  let safety_condition = Psv.vc psv in
  let normal_executions = Psv.(normal (remove_asserts psv)) in
  fun condition ->
    BExpr.ands_ [ 
      condition;
      normal_executions;
      BExpr.not_ safety_condition
    ]
    |> Solver.check_sat_model 
      ~timeout:(Some 20000)
      all_passive_consts

let path_generator gcl =
  let suffices = check_sufficiency gcl in
  fun condition ->
    match suffices condition with
    | None ->
      Log.qe_s "found a sufficiently strong formula";
      None
    | Some counterexample ->
      let input_packet = Model.project_inputs counterexample in
      Log.qe "%s" @@ lazy Model.(to_string input_packet);
      match Concrete.slice input_packet gcl with
      | None ->
        Log.error "Failed to slice(GCL):\n%s\n----------" @@ lazy (GCL.to_string gcl);
        failwith "Could not slice the counterexample"
      | Some pi -> Some pi
      

let num_cexs = ref Bigint.zero
let data = ref []      

let cegqe (gcl : GCL.t) : BExpr.t =
  let get_new_path = path_generator gcl in
  num_cexs := Bigint.zero;
  data := [Clock.now (), BExpr.true_];
  let rec loop phi_agg =
    Log.qe_s "checking implication...";
    match get_new_path phi_agg with
    | None -> 
      (* TERMINATION *)
      phi_agg
    | Some unsolved_path ->
      Bigint.incr num_cexs;
      Log.qe "found counterexample number %s" @@ lazy (Bigint.to_string !num_cexs);
      let simplified_unsolved_path = GCL.simplify_path unsolved_path in
      let path_condition = Psv.(vc @@ snd @@ passify simplified_unsolved_path) in
      match hybrid_strategy path_condition with
        | None ->
          Log.error "GCL:\n%s-------\n" @@ lazy (GCL.to_string unsolved_path);
          Log.error "VC:\n%s-------\n" @@ lazy (BExpr.to_smtlib path_condition);
          failwith "SOLVERS COULD NOT SOLVE PATH"
        | Some control_plane_of_path ->
	  data := !data @ [Clock.now(), control_plane_of_path];
          if not (BExpr.qf control_plane_of_path) then failwith "result was still quantified";
          let cvs = snd @@ BExpr.vars control_plane_of_path in
          Log.path_gen "%s" @@ lazy (Var.list_to_smtlib_decls cvs);
          Log.path_gen "%s" @@ lazy (BExpr.to_smtlib control_plane_of_path);
          let sat = Solver.check_sat cvs control_plane_of_path in
          if BExpr.(control_plane_of_path = true_) then begin
            Printf.printf "the following path gave true when cpfed:\n%s\n%!" (GCL.to_string unsolved_path);
            failwith "found false"
          end else if sat then
            loop (BExpr.and_ control_plane_of_path phi_agg)
          else begin
            Log.warn "Uncontrollable path:%s" @@ lazy (GCL.to_string unsolved_path);
            failwith "unsolveable"
          end
  in
  loop BExpr.true_

let replay data gcl : (Float.t * int) list =
  let paths = GCL.all_paths gcl in
  let _, data = 
  List.fold data ~init:(paths, []) ~f:(fun (unsolved, completion_data) (t, psi) -> 
      Printf.printf "Replaying data from time %f\n%!" t;
      let remain_unsolved = List.filter unsolved ~f:(fun pi -> Option.is_some (check_sufficiency pi psi)) in 
      let num_paths_solved = List.length unsolved - List.length remain_unsolved in 
      (remain_unsolved, completion_data @ [t, num_paths_solved])
  ) in 
  data

  
let check_for_parser prsr gpl_prsr =
  match prsr with
    | `Use  ->
      gpl_prsr
    | `Skip ->
      GPL.skip

let preprocess ~prsr gpl_pair =
  gpl_pair
  |> Tuple2.map_fst ~f:(check_for_parser prsr)
  |> Tuple2.map     ~f:(GPL.normalize_names)
