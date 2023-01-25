open Core


module V = struct
  type t = String.t * int [@@deriving hash, compare, sexp]

  let make s i : t =
    if String.length s = 0 then
      failwith "Variable cannot have length 0"
    else (s,i)
  let rename (_,i) s  = (s,i)
  let str ((s,_) : t) = s
  let size ((_,i) : t) = i

  let well_formed ((s,i) : t) = String.length s > 0 && i > 0
  let normalize_name (s,i) =
    let open String in
    let s' = substr_replace_all s ~pattern:"'" ~with_:"$" in
    (s', i)

  let dedup = List.dedup_and_sort ~compare

  let ghost = "$"
  let is_ghost (s,_) = String.is_prefix s ~prefix:ghost
  let make_ghost id k =
    Log.warn "%s" @@ lazy ("WARNING [make_symbRow] IS DEPRECATED");
    let x = Printf.sprintf "%s%s_%d" ghost (str k) id in
    let w = size k in
    make x w

  let symbRow = "_symb"
  let is_symbRow (s,_) = String.is_substring s ~substring:symbRow
  let make_symbRow id k =
    Log.warn "%s" @@ lazy ("WARNING [make_symbRow] IS DEPRECATED");
    let x = Printf.sprintf "%s%s_%d" symbRow (str k) id in
    let w = size k in
    make x w

  let make_symbRow_str id k =
    Log.warn "%s" @@ lazy ("WARNING [make_symbRow_str] IS DEPRECATED");
    let x = Printf.sprintf "%s%s_%s" symbRow (str k) id in
    let w = size k in
    make x w

  let is_sym_of ~sym ~data =
    is_symbRow sym && String.is_suffix (str sym) ~suffix:(str data)


  let (=) ((s1,n1) : t) ((s2,n2) : t) =
    if String.(s1 = s2) then
      if n1 = n2 then
        true
      else if n1 = -1 || n2 = -1 then
        true
      else
        failwith (Printf.sprintf "[%s]_%d and [%s]_%d had equal string values but different width values" s1 n1 s2 n2)
    else
      false

  let equal = (=)

  let to_smtlib_quant ((s,i) : t ) : string =
    Printf.sprintf "(%s (_ BitVec %d))" s i

  let list_to_smtlib_quant : t list -> string =
    List.fold ~init:""
      ~f:(fun acc v -> Printf.sprintf "%s%s " acc (to_smtlib_quant v))

  let to_smtlib_decl ((s, i) : t) : string =
    Printf.sprintf "(declare-const %s (_ BitVec %d))\n" s i

  let list_to_smtlib_decls : t list -> string =
    List.fold ~init:"\n"
      ~f:(fun acc v -> Printf.sprintf "%s%s" acc (to_smtlib_decl v))

  let index ((s,w) : t) (i : int) =
    (* if String.is_substring s ~substring:"$_$" then *)
    (*   failwithf "Variable %s has already been indexed" s () *)
    (* else *)
    (Printf.sprintf "%s$_$%d" s i, w)

  let unindex (indexed : t) =
    let s = str indexed in
    match String.rsplit2 s ~on:'$' with
    | None ->
      None
    | Some (l, idx) ->
      (*the suffix here is only "$_" instead of $_$ because the rightmost [$] is
        removed by rsplit *)
      match String.chop_suffix l ~suffix:"$_" with
      | None -> None
      | Some bare ->
        try
          Some (rename indexed bare, Int.of_string idx)
        with Failure _ ->
          None

  let is_indexed x =
    unindex x |> Option.is_some

  let sort = List.dedup_and_sort ~compare

  let quickcheck_generator =
    let open Base_quickcheck.Generator in
    let open Quickcheck.Generator in
    let open Let_syntax in
    let%map v = string_with_length_of ~length:2 char_lowercase |> filter ~f:(Fn.non (String.(=) "or")) in
    make v 32


  let quickcheck_observer =
    let open Quickcheck.Observer in
    tuple2 String.quickcheck_observer Int.quickcheck_observer

  let quickcheck_shrinker = Base_quickcheck.Shrinker.atomic

end

include V
module Set : Set.S with type Elt.t = t = Set.Make (V)
module Map : Map.S with type Key.t = t = Map.Make (V)
