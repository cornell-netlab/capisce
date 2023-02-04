module P4Info = Info
open Core
module Info = P4Info
open Pbench

type match_key =
  | Exact of { value : Bigint.t }
  | Ternary of { value : Bigint.t ; mask : Bigint.t}

type field = {
  field_id : int;
  match_key : match_key;
}

type arg = {
  arg_id : int;
  value : Bigint.t
}

type app = {
  action_id : int;
  args : arg list;
}

type action_profile_member = {
  member_id : int;
  action : app;
}

type action_profile = {
  id : int;
  members : action_profile_member list;
}

type action =
  | Action of app
  | Profile of {action_profile_member_id : int }

type t =
  | TableEntry of {
      table_id : int;
      matches : field list;
      action : action;
      priority : int;
    }
  | ActionProfileMember of {
      action_profile_id : int;
      member_id : int;
      action_id : int;
      args : arg list
    }

let exact_mac str =
  Ternary { value = Bigint.of_string str;
            mask = Bigint.of_string "281474976710655"; (*"\377\377\377\377\377\377"*)
          }

let rec to_table_action dont_care info (table : Info.table) profiles = function
  | Action {action_id; args} ->
    let action_decl = Info.find_action info action_id in
    (* translate from [id]entifier to [i]n[d]ex *)
    let index,_ = List.findi_exn table.action_refs ~f:(fun _ aref -> aref.id = action_id) in
    let act_size = Util.bits_to_encode_n (List.length table.action_refs) in
    let data =
      match
        List.map2 action_decl.params args ~f:(fun param args ->
          (args.value, param.bitwidth))
      with
      | Ok x -> x
      | Unequal_lengths ->
        failwithf "translating actiondata for %s.%s id %d. Got %d args, expected %d params"
          table.name action_decl.name action_id
          (List.length args)
          (List.length action_decl.params)
          ()
    in
    Table.Action.{
      id = (Bigint.of_int index, act_size);
      data;
      dont_care;
    }
  | Profile { action_profile_member_id } ->
    let action_profile_decl = Info.find_profile_for_table info table in
    let action_profile = Int.Map.find_exn profiles action_profile_decl.id in
    let member = List.find_exn action_profile.members
        ~f:(fun {member_id;_} -> member_id = action_profile_member_id) in
    (* make a recursive call to process the action *)
    to_table_action dont_care info table profiles (Action member.action)


let to_row (info : Info.t) profiles op : action_profile Int.Map.t * (Table.ORG.t String.Map.t -> Table.ORG.t String.Map.t) =
  match op with
  | TableEntry { table_id; matches; action; priority=_} ->
    (*lookup table, get key info from schema *)
    let table = Info.find_table info table_id in
    (* fold over match fields and values *)
    (* This loop does two things. (1) Computes the match expression for this
       [op], and (2) over-approximates whether a key has been "read" in this
       match-expression. By "read" we mean that the expression is used in any
       non-trivial match expression. *)
    let dont_care, key =
      let open BExpr in
      Log.debug_s table.name;
      List.fold table.match_fields
        ~init:([], BExpr.true_ )
        ~f:(fun (dont_cares, phi) match_field ->
          let match_value_opt = List.find matches
              ~f:(fun match_value -> Int.(match_value.field_id = match_field.id)) in
          let match_value =
            match match_value_opt, match_field.match_type with
            | Some m,_ -> m
            | None, TERNARY | None, LPM | None, OPTIONAL ->
              {field_id = match_field.id;
               match_key =
                 Ternary { value = Bigint.zero;
                           mask = Bigint.((of_int 2 ** of_int match_field.bitwidth) - one)
                         }
              }
            | None, EXACT ->
              failwithf "Could not find match for exact-match field %s in table %s" match_field.name table.name  ()
          in
          let match_var = Expr.var @@ Var.make match_field.name match_field.bitwidth in
          match match_value.match_key with
          | Exact {value} ->
            Tuple2.create (dont_cares @ [false]) @@
            and_ phi @@
            eq_ match_var @@ Expr.bv value match_field.bitwidth
          | Ternary {value; mask} ->
            let mask_expr = Expr.bv mask  match_field.bitwidth in
            let match_val = Expr.bv value match_field.bitwidth in
            (* if the mask is trivial, we don't cars *)
            Tuple2.create (dont_cares @ [Bigint.(zero = mask)]) @@
            and_ phi @@
            eq_
              Expr.(band match_var mask_expr)
              Expr.(band match_val mask_expr))
    in
    (* translate action *)
    let act = to_table_action dont_care info table profiles action in
    (profiles,
     fun control_plane ->
     String.Map.update control_plane table.name
       ~f:(function
           | None -> failwithf "Couldn't find table %s in control plane" table.name ()
           | Some rst -> Table.ORG.(Guard { key; act; rst })
         )
    )
  | ActionProfileMember {action_profile_id; member_id; action_id; args} ->
    let new_member = {member_id; action = {action_id; args}} in
    let profiles =
      Int.Map.update profiles action_profile_id ~f:(function
          | None ->
            { id = action_profile_id;
              members = [new_member]
            }
          | Some action_profile ->
            let diff_member_id (member : action_profile_member) = new_member.member_id <> member.member_id in
            assert (action_profile.id = action_profile_id);
            assert (List.for_all action_profile.members ~f:(diff_member_id));
            {
              action_profile with
              members = action_profile.members @ [ new_member ]
            }
        ) in
    (profiles, Fn.id)

let to_control_plane info default ops =
  (* will need to post-process for monotonicity of dont_cares and typechecking*)
  List.fold ops ~init:(Int.Map.empty, default)
    ~f:(fun (profiles, control_plane) op ->
        let profiles, add_row = to_row info profiles op in
        (profiles, add_row control_plane)
      )
  |> snd
  |> String.Map.map ~f:(Table.ORG.monotonize)
  |> String.Map.map ~f:(Table.ORG.pad_action_data)
