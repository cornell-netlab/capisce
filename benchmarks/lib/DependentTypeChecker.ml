open Core

module DepPrim = struct
  module Cmd = ASTs.GPL

  type t = { precondition : BExpr.t;
             cmd : Cmd.t;
             postcondition : BExpr.t }
  [@@deriving quickcheck, sexp, eq, compare, hash]

  let assume phi =
    { precondition = BExpr.true_;
      cmd = Cmd.assume phi;
      postcondition = BExpr.true_ }

  let assert_ phi =
    { precondition = BExpr.true_;
      cmd = Cmd.assert_ phi;
      postcondition = BExpr.true_ }

  let contra _ _ = false

  let to_smtlib {precondition; cmd; postcondition} =
      Printf.sprintf "{ %s } %s { %s }"
        (BExpr.to_smtlib precondition)
        (Cmd.to_string cmd)
        (BExpr.to_smtlib postcondition)

  let size {precondition; cmd; postcondition} =
    BExpr.size precondition
      + Cmd.size cmd
      + BExpr.size postcondition

  let vars {precondition; cmd; postcondition} =
    let allvars phi = phi |> BExpr.vars |> Tuple2.uncurry (@) in
    allvars precondition
    @ Cmd.vars cmd
    @ allvars postcondition
    |> Var.dedup

  let vc {precondition; cmd; postcondition} =
    let open ASTs in
    let index_map, passive =
      cmd
      |> GPL.encode_tables
      |> Psv.passify
    in
    let precondition  = BExpr.label Context.empty precondition in
    let passive_phi   = Psv.vc passive in
    let postcondition = BExpr.label index_map postcondition in
    BExpr.imps_ [
      precondition;
      passive_phi;
      postcondition
    ]

end

module HoareNet = struct
  module Pack = struct
    include Cmd.Make(DepPrim)

    let assign x e =
      prim ({ precondition = BExpr.true_;
              cmd = ASTs.GPL.assign x e;
              postcondition = BExpr.true_})

    let table ?(pre = BExpr.true_) ?(post = BExpr.true_) (name, keys, actions) =
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

    let infer (cmd:t) =
      bottom_up cmd ~sequence:BExpr.ands_ ~choices:BExpr.ands_
        ~prim:(fun (triple : DepPrim.t) ->
            let open ASTs in
            let pre = GCL.assume triple.precondition in
            let cmd = GPL.encode_tables triple.cmd in
            let post = GCL.assert_ triple.postcondition in
            GCL.sequence [ pre; cmd; post ]
            |> Qe.concolic
          )
  end
  include Pack
end
