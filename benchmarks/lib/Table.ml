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

  let get_action_bits body : int option =
    let rec loop = function
      | Default action -> [snd action.id]
      | Guard {key=_; act; rst} ->
        (snd act.id) :: loop rst
    in
    loop body
    |> List.all_equal ~equal:Int.equal

end

type t = {
  schema : Primitives.Table.t;
  body : ORG.t;
}

let make_action_var table action_bits =
  let x = Primitives.Action.cp_action table action_bits in
  Var.index x 0

let align table action actionlist return_var =
  List.foldi actionlist ~init:(BExpr.true_)
    ~f:(fun act_idx phi (params, _) ->
        let open BExpr in
        let open Expr in
        and_ phi @@
        imp_ (eq_ (var action) (bvi act_idx (Var.size action - 1))) @@
        fst @@
        List.fold params ~init:(true_, (Var.size action ))
          ~f:(fun (phi, slicepoint) datum ->
              let symb = Primitives.Action.cp_data table act_idx datum in
              let slice_end = slicepoint + Var.size symb in
              (and_ phi @@
               eq_ (var symb) @@ bslice slicepoint slice_end @@ var return_var,
               slice_end + 1
              )
            )
      )

let to_smtlib {schema; body} =
  let open Option.Let_syntax in
  let table = schema.name in
  let keys = schema.keys in
  let%bind out_bits = ORG.typecheck None body in
  let%map action_bits = ORG.get_action_bits body in
  (* because of passive form ensure you index actionvar to 0*)
  let action_var = make_action_var table action_bits in
  let smtlibstring = ORG.to_smtlib body in
  let tableres = Var.make (Printf.sprintf "%s$res" table) out_bits in
  String.concat ~sep:"\n" [
    (* declare the table output variable *)
    Var.list_to_smtlib_decls [tableres];
    (* Define the function*)
    Printf.sprintf "(define-fun %s (%s) (_ BitVec %d)\n %s)"
      table (Var.list_to_smtlib_quant keys) out_bits smtlibstring;
    (* assert that the output variable is the function output when applied to the symbolic keys *)
    List.map keys ~f:Var.str
    |> String.concat ~sep:" "
    |> Printf.sprintf "(assert (= %s (%s %s)))"
      (Var.str tableres) table;
    (* extract the action bits *)
    Expr.(var tableres |> bslice 0 (action_bits - 1) |> to_smtlib)
    |> Printf.sprintf "(assert (= %s %s))" (Var.str action_var);
    (* compute the alignment for action_data *)
    align table action_var schema.actions tableres
    |> BExpr.to_smtlib
    |> Printf.sprintf "(assert %s)"
  ]

let zip (schemata : Primitives.Table.t list) map =
  List.map schemata ~f:(fun schema ->
      {schema;
       body = String.Map.find_exn map schema.name
      }
    )
