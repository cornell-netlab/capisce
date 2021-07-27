open Core
   
type t = String.t * int [@@deriving compare, sexp]

let make s i : t =
  if String.length s = 0 then
    failwith "Variable cannot have length 0"
  else (s,i)
let str ((s,_) : t) = s
let size ((_,i) : t) = i

let well_formed ((s,i) : t) = String.length s > 0 && i > 0
                     
let dedup = List.dedup_and_sort ~compare
                     
let ghost = "ghost"
let is_ghost (s,_) = String.is_prefix s ~prefix:ghost           
let make_ghost id k =
  let x = Printf.sprintf "%s_%d__%s" ghost id (str k) in
  let w = size k in
  make x w

let symbRow = "row"
let is_symbRow (s,_) = String.is_prefix s ~prefix:symbRow
let make_symbRow id k =            
  let x = Printf.sprintf "%s_%d__%s" symbRow id (str k) in
  let w = size k in
  make x w
let is_sym_of ~sym ~data =
  is_symbRow sym && String.is_suffix (str sym) ~suffix:(str data)
  

let (=) ((s1,n1) : t) ((s2,n2) : t) =
  if String.(s1 = s2) then
    if n1 = n2 then
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

let quickcheck_generator =
  let open Quickcheck.Generator in
  let open Let_syntax in
  (* let networklike_size i = i < 48 && i > 1 in   *)
  let%map v = of_list ["x";"y";"z";"a";"b";"c";"n";"m";"h";"i";"j";"k";"l"] in
  (* let%map n = filter Int.quickcheck_generator ~f:(networklike_size) in *)
  Printf.printf "GENERATING %s#%i\n%!" v 32;
  make v 32
  

let quickcheck_observer =
  let open Quickcheck.Observer in
  tuple2 String.quickcheck_observer Int.quickcheck_observer

let quickcheck_shrinker = Base_quickcheck.Shrinker.atomic
  
