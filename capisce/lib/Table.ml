module P4Info = Info
open Core
module Info = P4Info

module Action = struct

  type t =
    { id : Bigint.t * int;
      data : (Bigint.t * int) list;
      dont_care : bool list;
    }

  let to_string a =
    let v_to_s (bi,i) = Printf.sprintf "(%s,%d)" (Bigint.to_string bi) i in
    Printf.sprintf "{id = %s; data = %s; dont_care = %s}"
      (v_to_s a.id)
      (List.to_string a.data ~f:v_to_s)
      (List.to_string a.dont_care ~f:Bool.to_string )

  let to_smtlib {id; data; dont_care} =
    let open Expr in
    let bv = Util.uncurry bv in
    let action_and_data =
      List.fold data
        ~init:(bv id)
        ~f:(fun acc d -> bconcat (bv d) acc)
    in
    let dont_care_bits =
      let open Bigint in
      List.rev dont_care
      |> List.foldi ~init:zero
        ~f:(fun i bv current_bit ->
            if current_bit then
              (one lsl i) lor bv
            else
              bv)
    in
    List.length dont_care
    |> Expr.bv dont_care_bits
    |> bconcat action_and_data (*DONT CARE BITS COME FIRST*)
    |> Expr.to_smtlib

  let typecheck {id; data; dont_care} =
    snd id
    + List.sum (module Int) data ~f:(snd)
    + List.length dont_care

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

  let rec to_string = function
    | Default action ->
      Action.to_string action
      |> Printf.sprintf "Default %s"
    | Guard {key; act; rst} ->
      Printf.sprintf "Guard {key = %s;\nact = %s;\nrst = %s}"
        (BExpr.to_smtlib key)
        (Action.to_string act)
        (to_string rst)

  let rec to_smtlib = function
    | Default action ->
      Action.to_smtlib action
    | Guard {key; act; rst} ->
      Printf.sprintf "(if %s \n  %s \n  %s)"
        (BExpr.to_smtlib key)
        (Action.to_smtlib act)
        (to_smtlib rst)

  let max_width (org : t) : int =
    let rec loop org old =
    match org with
    | Default action ->
      Action.typecheck action
      |> Int.max old
    | Guard {key=_;act;rst} ->
      Action.typecheck act
      |> Int.max old
      |> loop rst
    in
    loop org (-1)

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

  (* let get_action_bits body : int option = *)
  (*   let rec loop = function *)
  (*     | Default action -> [snd action.id] *)
  (*     | Guard {key=_; act; rst} -> *)
  (*       (snd act.id) :: loop rst *)
  (*   in *)
  (*   loop body *)
  (*   |> List.all_equal ~equal:Int.equal *)

  let monotonize org : t option =
    let open Option.Let_syntax in
    let and_ acc dcs =
      if List.is_empty acc then
        Some dcs
      else
      if List.length acc = List.length dcs then
        Some (List.map2_exn acc dcs ~f:( && ))
      else
        None
    in
    let rec loop acc = function
      | Default act ->
        let%map dont_care = and_ acc act.dont_care in
        Default {act with dont_care}

      | Guard {key; act; rst} ->
        let%bind dont_care = and_ acc act.dont_care in
        let act = {act with dont_care} in
        let%map rst = loop act.dont_care rst in
        Guard {key; act; rst; }
    in
    loop [] org

  let pad_action_data org =
    let max_width = max_width org in
    let pad_action action =
        let pad_width = max_width - Action.typecheck action in
        if pad_width > 0 then
          {action with data = action.data @ [Bigint.zero, pad_width]}
        else
           action
    in
    let rec pad = function
      | Default action ->
        Default (pad_action action)
      | Guard guard ->
        let act = pad_action guard.act in
        let rst = pad guard.rst in
        Guard {guard with act; rst}
    in
    pad org

  let rec update_default_action org default =
    match org with
    | Default _ -> Default default
    | Guard guard ->
      Guard {guard with rst = update_default_action guard.rst default }
end

type t = {
  schema : Primitives.Table.t;
  body : ORG.t;
}

let make_action_var table action_bits =
  let x = Primitives.Action.cp_action table action_bits in
  Var.index x 0

let align_dontcares offset keys return_var =
  let dont_care k =
    let open Var in
    match unindex k with
    | Some (x, i) when Int.(i = 0) ->
      let k_dont_care = make (str x ^ "$DONT_CARE") 1 in
      index k_dont_care 0
    | Some (_, i) ->
      failwithf "[Table.align_keys] key%s was indexed with nonzero index %d" (str k) i ()
    | None ->
      failwithf "[Table.align_keys] key %s unindexed" (str k) ()
  in
  List.foldi keys ~init:BExpr.true_
    ~f:(fun i acc key ->
        BExpr.and_ acc @@
        BExpr.eq_
          (Expr.(bslice (offset + i) (offset + i) @@ var return_var))
          (Expr.var @@ dont_care key)
    )

let align actionvar (actions : (Var.t list * Primitives.Action.t list) list) keys return_var =
  List.foldi actions
      ~init:(BExpr.true_)
      ~f:(fun act_idx phi (params,_) ->
          let open BExpr in
          let open Expr in
          and_ phi @@
          imp_ (eq_ (var actionvar) (bvi act_idx (Var.size actionvar))) @@
          fst @@ List.fold params ~init:(true_, (List.length keys + Var.size actionvar))
            ~f:(fun (phi, slicepoint) datum ->
                let datum = Var.index datum 0 in
                let slice_end = slicepoint + Var.size datum in
                if slice_end > Var.size return_var  then begin
                  (phi, slice_end)
                end else begin
                  (and_ phi @@
                   eq_ (var datum) @@ bslice slicepoint (slice_end - 1) @@ var return_var,
                   slice_end
                  )
                end
              )
        )

let rename_keys table keys =
  {table with schema = {table.schema with keys}}

let to_smtlib {schema; body} info =
  let open Option.Let_syntax in
  let table = schema.name in
  let symbolic_keys = List.map ~f:fst schema.keys in
  let semantic_keys =
    let table_info = Info.find_one_table_by_name info schema.name in
    List.map table_info.match_fields ~f:(fun f -> Var.make f.name f.bitwidth)
  in
  let%map out_bits = ORG.typecheck None body in
  let action_bits = Util.bits_to_encode_n_things (List.length schema.actions) in
  (* because of passive form ensure you index actionvar to 0*)
  let action_var = make_action_var table action_bits in
  let smtlibstring = ORG.to_smtlib body in
  let tableres = Var.make (Printf.sprintf "%s$res" table) out_bits in
  String.concat ~sep:"\n" [
    (* declare the table output variable *)
    Var.list_to_smtlib_decls [tableres];
    (* Define the function*)
    Printf.sprintf "(define-fun %s (%s) (_ BitVec %d)\n %s)"
      table (Var.list_to_smtlib_quant semantic_keys) out_bits smtlibstring;
    (* assert that the output variable is the function output when applied to the symbolic keys *)
    List.map symbolic_keys ~f:Var.str
    |> String.concat ~sep:" "
    |> Printf.sprintf "(assert (= %s (%s %s)))"
      (Var.str tableres) table;
    (* Extract the dont_care bits *)
    Printf.sprintf "(assert %s)" @@ BExpr.to_smtlib @@ align_dontcares 0 symbolic_keys tableres;
    (* extract the action bits *)
    Expr.(var tableres |> bslice (List.length symbolic_keys) (List.length symbolic_keys + Var.size action_var - 1) |> to_smtlib)
    |> Printf.sprintf "(assert (= %s %s))" (Var.str action_var);
    let () = assert (List.length schema.actions > 0) in
    align action_var schema.actions schema.keys tableres
    |> BExpr.to_smtlib
    |> Printf.sprintf "(assert %s)"
  ]

let zip (schemata : Primitives.Table.t list) map =
  List.map schemata ~f:(fun schema ->
      {schema;
       body = String.Map.find_exn map schema.name
      }
    )
