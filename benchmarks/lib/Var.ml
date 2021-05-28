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
      
