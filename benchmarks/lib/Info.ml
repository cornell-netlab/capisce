open Core

type param = {
  id : int;
  name : string;
  bitwidth : int
}

type action = {
  name : string;
  id : int;
  params : param list;
}

type action_ref = {
  id : int
}

type match_type =
    EXACT | LPM | OPTIONAL | TERNARY

type match_field = {
  id : int;
  name : string;
  bitwidth : int;
  match_type : match_type;
}

type table = {
  name : string;
  id : int;
  match_fields : match_field list;
  action_refs : action_ref list;
}

type action_profile = {
  id : int;
  name : string;
  table_ids : int list
}

type t = {
  tables : table list;
  actions : action list;
  action_profiles : action_profile list;
}

let find_profile_for_table (info : t) (table : table) : action_profile =
  List.find info.action_profiles
    ~f:(fun prof ->
        List.exists prof.table_ids ~f:((=) table.id)
      )
  |> Option.value_exn
       ~message:(Printf.sprintf "table %s with id %d had no action profile" table.name table.id)
  

let find_table (info:t) (id :int) : table =
  List.find info.tables ~f:(fun t -> t.id = id)
  |> Option.value_exn
       ~message:(Printf.sprintf "Could not find table %d" id)

let find_tables_by_name (info:t) (name:string) : table list =
  List.filter info.tables ~f:(fun t -> String.(t.name = name))

let find_one_table_by_name (info:t) (name:string) : table =
  match find_tables_by_name info name with
  | [table] -> table
  | [] -> failwithf "Couldnt find any tables matching %s" name ()
  | ts -> failwithf "found %d tables matching %s" (List.length ts) name ()


let find_action (info : t) (action_id : int) : action =
  List.find info.actions ~f:(fun a -> a.id = action_id)
  |> Option.value_exn
       ~message:(Printf.sprintf "could not find action %d" action_id)
