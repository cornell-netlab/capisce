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
                  
  
