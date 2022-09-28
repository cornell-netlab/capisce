open Core

let pairs_app_dedup ~dedup (d1,c1) (d2,c2) =
  (dedup(d1 @ d2), dedup (c1 @ c2))

let uncurry f (x,y) = f x y
let curry f x y = f (x,y)

let rec space n =
  if n <= 0 then
    ""
  else
    Printf.sprintf " %s" (space (n-1))

let rec range n = if n < 0 then [] else range (n-1)@[n]

(** List helpers *)
let smaller_outer xs ys =
  let xs_is_smaller = List.(length xs < length ys) in
  let outer = if xs_is_smaller then xs else ys in
  let inner = if xs_is_smaller then ys else xs in
  (outer, inner)
                
let linter ~equal xs ys =
  let outer, inner = smaller_outer xs ys in
  List.filter outer ~f:(fun o -> List.exists inner ~f:(equal o))

let ldiff ~equal xs ys =
  List.filter xs ~f:(fun x -> not(List.exists ys ~f:(equal x)))

let lmem ~equal x xs = List.exists xs ~f:(equal x)

let projMap ~put ~get ~f xs =
  List.map xs ~f:(fun x -> put x (f (get x)))

let inj2 (x, _) y = (x,y)
