open Core

module Action = struct

  type t =
    { id : Bigint.t * int;
      data : (Bigint.t * int) list;
    }

  let to_smtlib {id; data} =
    let bv = Util.uncurry Expr.bv in
    List.fold data ~init:(bv id)
      ~f:(fun acc d ->
          Expr.bconcat acc (bv d)
        )
    |> Expr.to_smtlib

  let typecheck {id; data} =
    List.fold data ~init:(snd id)
      ~f:(fun acc datum -> acc + snd datum)


end


module ORG = struct
  (* Table built using simplified ORdered Guards representation from Grisette *)

  type t =
    | Default of Action.t
    | Guard of {
        key : BExpr.t;
        act : Action.t;
        rst : t
      }

  let rec to_smtlib = function
    | Default action ->
      Action.to_smtlib action
    | Guard {key; act; rst} ->
      Printf.sprintf "(if %s \n  %s \n  %s)"
        (BExpr.to_smtlib key)
        (Action.to_smtlib act)
        (to_smtlib rst)

  let rec typecheck old org =
    match org with
    | Default action ->
      let new_width = Action.typecheck action in
      begin match old with
        | None -> Some new_width
        | Some old_width ->
          if Int.(old_width = new_width) then
            Some new_width
          else begin
            Printf.sprintf "Running total was %d, The following action had with %d:\n%s"
              old_width new_width (Action.to_smtlib action)
            |> Log.error_s;
            failwith "Type error"
          end
      end
    | Guard {key=_; act; rst} ->
      (* hack to reuse the default case *)
      let act_type_opt = typecheck old (Default act) in
      typecheck act_type_opt rst




end

type t = {
  table : string;
  keys : Var.t list;
  body : ORG.t;
}

let to_smtlib {table; keys; body} =
  let open Option.Let_syntax in
  let%map out_bits = ORG.typecheck None body in
  let smtlibstring = ORG.to_smtlib body in
  Printf.sprintf "(define-fun %s %s (BitVec %d)%s)\n %s)"
    table
    (Var.list_to_smtlib_quant keys)
    (out_bits)
    (smtlibstring)
