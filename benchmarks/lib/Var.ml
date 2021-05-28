open Core
   
type t = String.t * int [@@deriving compare, equal]

let make s i : t = (s,i)
let str ((s,_) : t) = s
let size ((_,i) : t) = i

let dedup = List.dedup_and_sort ~compare
                     
let ghost = "gamma"
let is_ghost (s,_) = String.is_prefix s ~prefix:ghost           
let ghost_var id k =
  let x = Printf.sprintf "%s_%d__%s" ghost id (str k) in
  let w = size k in
  make x w

let symbRow = "rho"
let is_symbRow (s,_) = String.is_prefix s ~prefix:symbRow
let symbRow_var id k =            
  let x = Printf.sprintf "%s_%d__%s" symbRow id (str k)in
  let w = size k in
  make x w

let (=) ((s1,n1) : t) ((s2,n2) : t) =
  if String.(s1 = s2) then
    if n1 = n2 then
      true
    else
      failwith (Printf.sprintf "[%s]_%d and [%s]_%d had equal string values but different width values" s1 n1 s2 n2)
  else
    false

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
