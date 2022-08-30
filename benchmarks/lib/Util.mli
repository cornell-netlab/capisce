val pairs_app_dedup : dedup:('a list -> 'b) -> ('a list * 'a list) -> ('a list * 'a list) -> ('b * 'b)
(** [pairs_app_dedup ~dedup (xs,ys) (zs,ws)] concatenates elementwise and calls [dedup] on each result *)

val uncurry : ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
(** [uncurry f (a,b)] = [f a b]*)

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
(** [curry f a b] = [f (a,b)]*)  

val space : int -> string
(** [space n] is a string of [n] spaces*)

val range : int -> int list
(** [range n] is [0;...;n]*)                       
 
val linter : equal:('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list 
(** [linter ~equal xs ys] is a list of the elements that are in both [xs] and [ys]. May contain duplicates.*)
                                                                   
val ldiff : equal:('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list 
(** [ldiff ~equal xs ys] is a list of the elements of [xs] that are not in [ys]. Contains duplicates iff ldiff contains duplicates.*)
                                                                  
                    
val lmem : equal:('a -> 'a -> bool) -> 'a -> 'a list -> bool
(** [lmem ~equal x xs] returns true if [x] occurs in [xs]  *)

