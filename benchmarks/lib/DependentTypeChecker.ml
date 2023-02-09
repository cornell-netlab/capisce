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

    let assign x e =
      prim ({ precondition = None;
              cmd = ASTs.GPL.assign x e;
              postcondition = None})

    let table ?(pre = None) ?(post = None) (name, keys, actions) =
      prim ({ precondition = pre;
              cmd = ASTs.GPL.table name keys actions;
              postcondition = post})

    let flatten cmd = bottom_up cmd
        ~sequence:ASTs.GPL.sequence
        ~choices:ASTs.GPL.choices
        ~prim:(fun p ->
            match p.precondition, p.postcondition with
            | None, None ->
              p.cmd
            | _, _ ->
              Log.error "Found hoare annotation in %s" @@ lazy (to_string cmd);
              failwithf "[HoareNet.flatten] Cannot flatten command wtih Hoare annotations" ())

    let triple (pre : BExpr.t) (cmd : t) (post : BExpr.t) =
      let gpl = flatten cmd in
      prim ({precondition = Some pre;
             cmd = gpl;
             postcondition = Some post;
            })


    let check (cmd : t) =
      let all = List.for_all ~f:Fn.id in
      bottom_up cmd ~sequence:all ~choices:all
        ~prim:(fun (triple : DepPrim.t) ->
            let phi = DepPrim.vc triple in
            let vars = BExpr.vars phi |> Tuple2.uncurry (@) in
            BExpr.not_ phi
            |> Solver.check_unsat vars ~timeout:(Some 2000))

    let vc cmd =
      let open ASTs in
      bottom_up cmd
        ~prim:(fun (triple : DepPrim.t) ->
            GPL.sequence [Option.value_map ~f:GPL.assert_ triple.precondition ~default:GPL.skip;
                          triple.cmd;
                          Option.value_map ~f:GPL.assert_ triple.postcondition ~default:GPL.skip]
          )
        ~sequence:GPL.sequence
        ~choices:GPL.choices
      |> GPL.encode_tables
      |> Psv.passify
      |> snd
      |> Psv.vc

    let check_annotations (cmd : t) : bool =
      let open ASTs in
      let validate phi =
        let vars = BExpr.vars phi |> Tuple2.uncurry (@) in
        Solver.check_unsat vars phi
      in
      let phi =
        top_down cmd
          ~init:BExpr.true_
          ~prim:(fun postcond prim ->
              match prim.precondition, prim.postcondition with
              | None, None ->
                GPL.wp prim.cmd postcond
              | Some p, Some q ->
                let phi = BExpr.(and_ q @@ not_ postcond) in
                if validate phi then
                  p
                else begin
                  Log.error "Could not validate postcondition for %s" @@ lazy (GPL.to_string prim.cmd);
                  Log.error "Annotated Post: %s" @@ lazy (BExpr.to_smtlib q);
                  Log.error "Computed  Post: %s" @@ lazy (BExpr.to_smtlib postcond);
                  failwith "Invalid Annotations"
                end
              | _, _ ->
                failwith "P & Q must be both some or both none"
            )
          ~sequence:(fun postcond cs check_backwards ->
              List.fold_right cs
                ~init:postcond
                ~f:(Fn.flip check_backwards)
            )
          ~choices:(fun postcond cs check_backwards ->
              BExpr.ands_ @@
              List.map cs ~f:(check_backwards postcond)
            )
      in
      if validate @@ BExpr.not_ phi then
        true
      else
        begin
          Log.error_s "Could not validate precondition";
          (* Log.error "Computed pre: %s" @@ lazy (BExpr.to_smtlib phi); *)
          (* let model = Solver.check_sat_model (BExpr.vars phi |> Tuple2.uncurry (@)) phi in *)
          (* Log.error "counterexample:\n%s" @@ lazy (Model.to_string @@ Option.value_exn model); *)
          failwith "Invalid Annotations"
        end



    (* let check_annotations cmd : bool = *)
    (*   let open Option.Let_syntax  in *)
    (*   (\* None represents failure, Some c represents that theres been no failure *)
    (*      so far and that `c` isthe prefix of the current command *\) *)
    (*   top_down cmd *)
    (*       ~init:(Some skip) *)
    (*       ~prim:(fun prefix_opt (triple : DepPrim.t) -> *)
    (*           Log.debug "PRIM: %s" @@ lazy (DepPrim.to_smtlib triple); *)
    (*           let%bind prefix = prefix_opt in *)
    (*           Log.debug "PREFIX: %s" @@ lazy (to_string prefix); *)
    (*           match triple.precondition, triple.postcondition with *)
    (*           | Some p, Some q -> *)
    (*             let prog = sequence [prefix; assert_ p] in *)
    (*             Log.debug "checking %s" @@ lazy (to_string prog); *)
    (*             let phi = vc prog in *)
    (*             let vars = BExpr.vars phi |> Tuple2.uncurry (@) in *)
    (*             let optional_model = *)
    (*               (\* Fn.flip Option.some_if Model.empty @@ *\) *)
    (*               (\* Solver.check_unsat *\) *)
    (*               Solver.check_sat_model vars ~timeout:(Some 2000) @@ *)
    (*               BExpr.not_ phi *)
    (*             in *)
    (*             begin match optional_model with *)
    (*               | None -> *)
    (*                 (\* ¬φ was not satisfiable so precondition is valid. assume postcondition q *\) *)
    (*                 Some (assume q) *)
    (*               | Some model -> *)
    (*                 Log.debug "Soundness check failed got model:\n%s" @@ lazy (Model.to_string model); *)
    (*                 None *)
    (*             end *)
    (*           | None, None -> *)
    (*             Log.debug_s "skipping... added it to prefix"; *)
    (*             Some (sequence [prefix; prim triple]) *)
    (*           | _, _ -> *)
    (*             failwith "[HoareNet.check_annotations] in {P} c {Q}, P or Q was None and the other, Some. " *)
    (*         ) *)
    (*       ~sequence:(fun prefix cs recursive_call -> *)
    (*           Log.debug "PREFIX: %s" @@ lazy (Option.value_map ~f:to_string prefix ~default:"None"); *)
    (*           Log.debug_s "Sequence:"; *)
    (*           List.iter cs ~f:(fun c -> *)
    (*               Log.debug "-\t %s" @@ lazy (to_string c); *)
    (*           ); *)
    (*           List.fold_left cs ~init:prefix *)
    (*             ~f:recursive_call *)
    (*         ) *)
    (*       ~choices:(fun prefix cs recursive_call -> *)
    (*           List.map ~f:(recursive_call prefix) cs *)
    (*           |> Util.commute *)
    (*           |> Option.map ~f:(choices) *)
    (*         ) *)
    (*   |> Option.is_some *)

    let ninfer = ref 0

    let infer (cmd:t) nprocs pid =
      Log.path_gen "INFER CALL #%d" @@ lazy (!ninfer);
      (* Breakpoint.set (!ninfer > 0); *)
      Int.incr ninfer;
      let seen = ref [] in
      top_down cmd
        ~init:BExpr.true_
        ~sequence:(fun _ cs infer -> BExpr.ands_ @@ List.map ~f:(infer BExpr.true_) cs)
        ~choices:(fun _ cs infer -> BExpr.ands_ @@ List.map ~f:(infer BExpr.true_) cs)
        ~prim:(fun _ (triple : DepPrim.t) ->
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
                (* Qe.concolic prog *)
                Qe.all_paths prog nprocs pid
              end
            | _, _ ->
              BExpr.true_
            )
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
