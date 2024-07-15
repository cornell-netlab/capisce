open Core

module DepPrim = struct
  module Cmd = ASTs.GPL

  type t = { precondition : BExpr.t option;
             cmd : Cmd.t;
             postcondition : BExpr.t option }
  [@@deriving quickcheck, sexp, eq, compare, hash]

  let assume phi =
    { precondition = None;
      cmd = Cmd.assume phi;
      postcondition = None}

  let assert_ phi =
    { precondition = None;
      cmd = Cmd.assert_ phi;
      postcondition = None; }

  let contra _ _ = false

  let to_smtlib {precondition; cmd; postcondition} =
    match precondition, postcondition with
    | Some pre, Some post ->
      Printf.sprintf "{ %s } %s { %s }"
        (BExpr.to_smtlib pre)
        (Cmd.to_string cmd)
        (BExpr.to_smtlib post)
    | None, None ->
      Cmd.to_string cmd
    | _, _ ->
      failwith "[DepPrim.to_smtlib] in {P} c {Q}, P or Q was None and the other, Some. "

  let size {precondition; cmd; postcondition} =
    Option.value_map ~f:BExpr.size precondition ~default:0
      + Cmd.size cmd
      + Option.value_map ~f:BExpr.size postcondition ~default:0

  let vars {precondition; cmd; postcondition} =
    let allvars phi = phi |> BExpr.vars |> Tuple2.uncurry (@) in
    Option.value_map ~f:allvars precondition ~default:[]
    @ Cmd.vars cmd
    @ Option.value_map ~f:allvars postcondition ~default:[]
    |> Var.dedup

  let vc {precondition; cmd; postcondition} =
    let open ASTs in
    let index_map, passive =
      cmd
      |> GPL.encode_tables
      |> Psv.passify
    in
    let precondition  = Option.map ~f:(BExpr.label Context.empty) precondition in
    let passive_phi   = Psv.vc passive in
    let postcondition = Option.map ~f:(BExpr.label index_map) postcondition in
    match precondition, postcondition with
    | None, None ->
      passive_phi
    | Some p, Some q ->
      BExpr.imps_ [p; passive_phi; q]
    | _, _ ->
      failwith "[DepPrim.to_smtlib] in {P} c {Q}, P or Q was None and the other, Some. "

  let normalize_names ({precondition; cmd; postcondition} : t) : t =
    { precondition = Option.map precondition ~f:BExpr.normalize_names;
      cmd = Cmd.normalize_names cmd;
      postcondition = Option.map postcondition ~f:BExpr.normalize_names;
    }

  let dead_code_elim {precondition; cmd; postcondition} reads : (Var.Set.t * t) option =
    match precondition, postcondition with
    | None, None ->
      let reads, cmd = Cmd.dead_code_elim reads cmd in
      Some (reads, {precondition; cmd; postcondition})
    | Some p, Some q ->
      (*just moves the some around, `Assert.dce` necessarily produces `Some` *)
      let typeshift opt = let (r,p) = Option.value_exn opt in (r, Some p) in
      let reads, postcondition = Primitives.Assert.dead_code_elim reads q |> typeshift in
      let reads, cmd = Cmd.dead_code_elim reads cmd in
      let reads, precondition  = Primitives.Assert.dead_code_elim reads p |> typeshift in
      Some (reads, {precondition; cmd; postcondition})
    | _, _ ->
      failwith "[DepPrim.to_smtlib] in {P} c {Q}, P or Q was None and the other, Some. "


  let const_prop facts {precondition; cmd; postcondition} : (t * Expr.t Var.Map.t) option =
    let open Option.Let_syntax in
    match precondition, postcondition with
    | None, None ->
      let%map cmd, facts = Cmd.const_prop facts cmd in
      ({precondition; cmd; postcondition}, facts)
    | Some p, Some q ->
      (*just moves the some around, `Assert.const_prop` necessarily produces `Some` *)
      let typeshift (p,f) = (Some p, f) in
      Log.compiler "Precondition is %s" @@ lazy (BExpr.to_smtlib p);
      let precondition, facts  = Primitives.Assert.const_prop facts p |> typeshift in
      Log.compiler "Precondition has become %s" @@ lazy (BExpr.to_smtlib @@ Option.value_exn precondition);
      let%map cmd, facts = Cmd.const_prop facts cmd in
      Log.compiler "Postcondition is %s" @@ lazy (BExpr.to_smtlib q);
      let postcondition, facts = Primitives.Assert.const_prop facts q |> typeshift in
      Log.compiler "Precondition has become %s" @@ lazy (BExpr.to_smtlib @@ Option.value_exn postcondition);
      ({precondition; cmd; postcondition}, facts)
    | _, _ ->
      failwith "[DepPrim.to_smtlib] in {P} c {Q}, P or Q was None and the other, Some. "


end

module HoareNet = struct
  module Pack = struct
    include Cmd.Make(DepPrim)
    open ASTs

    let assign x e =
      prim ({ precondition = None;
              cmd = GPL.assign x e;
              postcondition = None})

    let instr_table ?(pre = None) ?(post = None) (name, real_keys, actions) =
      prim({ precondition = pre;
             cmd = GPL.table name real_keys actions;
             postcondition = post})

    let rec assert_valids cmd =
      match cmd with
      | Prim triple ->
        let cmd = GPL.assert_valids triple.cmd in
        Prim {triple with cmd}
      | Seq cs ->
        List.map cs ~f:assert_valids
        |> sequence
      | Choice cxs ->
        List.map cxs ~f:assert_valids
        |> choices

    let rec track_assigns x cmd =
      match cmd with
      | Prim triple ->
        let cmd = GPL.track_assigns x triple.cmd in
        Prim {triple with cmd}
      | Seq cs ->
        sequence_map cs ~f:(track_assigns x)
      | Choice cxs ->
        choices_map cxs ~f:(track_assigns x)


    let of_gpl cmd =
      prim( {precondition = None;
             cmd;
             postcondition = None})

    let of_action (a : Primitives.Action.t) : t =
      Prim ({precondition = None;
            cmd = GPL.prim (Primitives.Pipeline.action a);
            postcondition = None})

    let rec safe_to_gpl_exn (cmd : t) =
      match cmd with
      | Prim triple ->
        begin match triple.precondition, triple.postcondition with
        | None, None ->
          triple.cmd
        | _, _ ->
          Log.error "Found hoare annotation in %s" @@ lazy (to_string cmd);
          failwithf "[HoareNet.flatten] Cannot flatten command wtih Hoare annotations" ()
        end
      | Seq cs ->
        List.map cs ~f:safe_to_gpl_exn |> GPL.sequence
      | Choice cxs ->
        List.map cxs ~f:safe_to_gpl_exn |> GPL.choices

    let rec annotated_to_gpl (cmd : t) =
      match cmd with
      | Prim triple ->
        GPL.sequence [Option.value_map ~f:GPL.assert_ triple.precondition ~default:GPL.skip;
                      triple.cmd;
                      Option.value_map ~f:GPL.assert_ triple.postcondition ~default:GPL.skip]
      | Seq cs ->
        List.map cs ~f:annotated_to_gpl |> GPL.sequence
      | Choice cxs ->
        List.map cxs ~f:annotated_to_gpl |> GPL.choices

    let triple (pre : BExpr.t) (cmd : t) (post : BExpr.t) =
      prim ({precondition = Some pre;
             cmd = safe_to_gpl_exn cmd;
             postcondition = Some post;
            })

    let rec check (cmd : t) =
      let all = List.for_all ~f:check in
      match cmd with
      | Prim triple ->
        let open BExpr in
        let phi = DepPrim.vc triple in
        let vars = vars phi |> Tuple2.uncurry (@) in
        Solver.check_unsat vars (not_ phi) ~timeout:(Some 2000)
      | Seq cs | Choice cs ->
        all cs

    let vc cmd =
      (* Computes the monolithic VC for this program *)
      let open ASTs in
      annotated_to_gpl cmd
      |> GPL.encode_tables
      |> Psv.passify
      |> snd
      |> Psv.vc

    let zero_init cmd =
      let vars = vars cmd |> List.filter ~f:(fun x -> (Var.str x) |> String.is_suffix ~suffix:".is_valid") in
      let inits =
        List.map vars ~f:(fun x ->
            assign x @@ Expr.bvi 0 1
        )
        |> sequence
      in
      seq inits cmd

    let check_annotations (cmd : t) : bool =
      let open ASTs in
      let validate phi =
        let vars = BExpr.vars phi |> Tuple2.uncurry (@) in
        Solver.check_unsat_cex vars phi
      in
      let rec annot_phi postcond cmd =
        match cmd with
        | Prim triple ->
          begin match triple.precondition, triple.postcondition with
            | None, None ->
              let postcond = GPL.wp triple.cmd postcond in
              postcond
            | Some p, Some q ->
              let phi = BExpr.(and_ q @@ not_ postcond) in
              begin match  validate phi with
                | None -> p
                | Some cex ->
                  Log.error "Could not validate postcondition for %s" @@ lazy (GPL.to_string triple.cmd);
                  Log.error "Counterexample %s" @@ lazy (Model.to_string cex);
                  Log.error "Annotated Post: %s" @@ lazy (BExpr.to_smtlib q);
                  Log.error "Computed  Post: %s" @@ lazy (BExpr.to_smtlib postcond);
                  failwith "Invalid Annotations"
              end
            | _, _ ->
              failwith "P & Q must be both some or both none"
          end
        | Seq cs ->
          List.fold_right cs
            ~init:postcond
            ~f:(Fn.flip annot_phi)
        | Choice cxs ->
          List.map cxs ~f:(annot_phi postcond)
          |> BExpr.ands_
      in
      match validate @@ BExpr.not_ @@ annot_phi BExpr.true_ cmd with
      | None -> true
      | Some cex ->
        Log.error_s "Could not validate precondition";
        Log.error "counterexample:\n%s" @@ lazy (Model.to_string cex);
        failwith "Invalid Annotations"


    let rec has_triple = function
      | Prim triple ->
        Option.is_some triple.precondition || Option.is_some triple.postcondition
      | Seq cs ->
        List.exists cs ~f:has_triple
      | Choice cxs ->
        List.exists cxs ~f:has_triple

    let ensure_triple c =
      if has_triple c then
        c
      else
        prim ({precondition = Some BExpr.true_;
               cmd = safe_to_gpl_exn c;
               postcondition = Some BExpr.true_})

    let ninfer = ref 0
    let infer ?(qe = `Cegqe) (cmd:t) nprocs pid =
      Int.incr ninfer;
      let seen = ref [] in
      let rec loop = function
        | Seq cs -> List.map ~f:loop cs |> BExpr.ands_
        | Choice cxs -> List.map ~f:loop cxs |> BExpr.ands_
        | Prim triple ->
          match triple.precondition, triple.postcondition with
          | Some p, Some q ->
            let open ASTs in
            let pre = GCL.assume p in
            let cmd = GPL.encode_tables triple.cmd in
            let post = GCL.assert_ q in
            let prog = GCL.sequence [ pre; cmd; post ] in
            if List.exists !seen ~f:(GCL.equal prog) then
              BExpr.true_
            else begin
              seen := prog::!seen;
              match qe with
              | `Cegqe -> Qe.cegqe prog
              | `Enum ->
                let s = function None -> "NONE" | Some i -> Printf.sprintf "%d" i in 
                failwithf "path enumeration (%s, %s) is no longer supported" (s nprocs) (s pid) ()
            end
          | _, _ ->
            BExpr.true_
      in
      loop cmd
  end

  module Normalizer = Transform.Normalize(struct
      include Pack
      module P = DepPrim
      let normalize_prim = DepPrim.normalize_names
    end)

  module Optimizer = Transform.Optimizer(struct
      include Pack
      module P = DepPrim
      let prim_dead_code_elim =
        DepPrim.dead_code_elim
      let prim_const_prop facts prim =
        DepPrim.const_prop facts prim
        |> Option.value_exn ~message:"DepPrim constant propagation failed"

    end)
  include Pack

  let normalize_names = Normalizer.normalize
  let optimize = Optimizer.optimize
end
