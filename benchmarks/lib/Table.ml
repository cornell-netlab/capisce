open Core

module ORG = struct
  (* Table built using simplified ORdered Guards representation from Grisette *)

  type action =
    { action : Bigint.t * int;
      data : (Bigint.t * int) list;
    }

  let action_to_smtlib {action; data} =
    let bv = Util.uncurry Expr.bv in
    List.fold data ~init:(bv action)
      ~f:(fun acc d ->
          Expr.bconcat acc (bv d)
        )
    |> Expr.to_smtlib

  type t =
    | Default of action
    | Guard of {
        key : BExpr.t;
        act : action;
        rst : t
      }

  let rec to_smtlib = function
    | Default action ->
      action_to_smtlib action
    | Guard {key; act; rst} ->
      Printf.sprintf "(if %s %s %s)"
        (BExpr.to_smtlib key)
        (action_to_smtlib act)
        (to_smtlib rst)

end

type t = {
  table : string;
  keys : Var.t list;
  body : ORG.t;
}
