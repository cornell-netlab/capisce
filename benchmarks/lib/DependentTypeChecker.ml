open Core

module DepPrim = struct
  module Cmd = ASTs.GPL

  type t = { precondition : BExpr.t option;
             cmd : Cmd.t;
             postcondition : BExpr.t option }
  [@@deriving quickcheck, sexp, eq, compare, hash]

  let assume phi =
    { precondition = Some BExpr.true_;
      cmd = Cmd.assume phi;
      postcondition = Some BExpr.true_ }

  let assert_ phi =
    { precondition = Some BExpr.true_;
      cmd = Cmd.assert_ phi;
      postcondition = Some BExpr.true_ }

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

    let check_annotations cmd : bool =
      let open Option.Let_syntax  in
      (* None represents failure, Some c represents that theres been no failure
         so far and that `c` isthe prefix of the current command *)
      top_down cmd
          ~init:(Some skip)
          ~prim:(fun prefix_opt (triple : DepPrim.t) ->
              Log.debug "PRIM: %s" @@ lazy (DepPrim.to_smtlib triple);
              let%bind prefix = prefix_opt in
              Log.debug "PREFIX: %s" @@ lazy (to_string prefix);
              match triple.precondition, triple.postcondition with
              | Some p, Some q ->
                let prog = sequence [prefix; assert_ p] in
                Log.debug "checking %s" @@ lazy (to_string prog);
                let phi = vc prog in
                let vars = BExpr.vars phi |> Tuple2.uncurry (@) in
                BExpr.not_ phi
                |> Solver.check_unsat vars ~timeout:(Some 2000)
                |> Fn.flip Option.some_if @@
                assume q
              | None, None ->
                Log.debug_s "skipping... added it to prefix";
                Some (sequence [prefix; prim triple])
              | _, _ ->
                failwith "[HoareNet.check_annotations] in {P} c {Q}, P or Q was None and the other, Some. "
            )
          ~sequence:(fun prefix cs recursive_call ->
              Log.debug "PREFIX: %s" @@ lazy (Option.value_map ~f:to_string prefix ~default:"None");
              Log.debug_s "Sequence:";
              List.iter cs ~f:(fun c ->
                  Log.debug "-\t %s" @@ lazy (to_string c);
              );
              List.fold_left cs ~init:prefix
                ~f:recursive_call
            )
          ~choices:(fun prefix cs recursive_call ->
              List.map ~f:(recursive_call prefix) cs
              |> Util.commute
              |> Option.map ~f:(choices)
            )
      |> Option.is_some

    let infer (cmd:t) =
      bottom_up cmd ~sequence:BExpr.ands_ ~choices:BExpr.ands_
        ~prim:(fun (triple : DepPrim.t) ->
            match triple.precondition, triple.postcondition with
            | Some p, Some q ->
              let open ASTs in
              let pre = GCL.assume p in
              let cmd = GPL.encode_tables triple.cmd in
              let post = GCL.assert_ q in
              let prog = GCL.sequence [ pre; cmd; post ] in
              Log.debug "%s" @@ lazy (GCL.to_string prog);
              (* Qe.concolic prog *)
              Qe.all_paths prog
            | _, _ ->
              BExpr.true_
            )
  end
  include Pack
end
