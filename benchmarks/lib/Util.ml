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

let rec fix ~equal f x =
  let x' = f x in
  if equal x' x then
    x
  else
    fix ~equal f x'


let concat (x,y) = x @ y

let commute (xs : 'a option list) : 'a list option  =
  let open Option.Let_syntax in
  List.fold xs ~init:(Some [])
    ~f:(fun acc_opt x_opt ->
        let%bind acc = acc_opt in
        let%map x = x_opt in
        acc @ [x]
      )


let option_map ~f =
  let open Option.Let_syntax in
  let rec loop xs =
    match xs with
    | [] -> Some []
    | x :: xs ->
      let%bind y = f x in
      let%map ys = loop xs in
      y :: ys
  in
  loop

let choose xs =
  let n = List.length xs in
  if n <= 0 then
    None
  else
    Random.int n
    |> List.nth xs

let choose_exn xs =
  if List.is_empty xs then
    failwith "[choose_exn] cannot choose an element from an empty list"
  else
    let n = Random.int (List.length xs) in
    List.nth_exn xs n

let mapmap ~f xss =
  let open List.Let_syntax in
  let%map xs = xss in
  let%map x = xs in
  f x


let fold_right1 ~init ~f xs =
  match List.rev xs with
  | [] -> failwith "Cannot fold_right1 on an empty list"
  | x::xs ->
    List.fold_right (List.rev xs) ~f ~init:(init x)

let app_on ~f x =
  (x, f x)



let bits_to_encode_n n =
  Int.succ n
  |> Float.of_int
  |> Stdlib.Float.log2
  |> Float.round_up
  |> Int.of_float
