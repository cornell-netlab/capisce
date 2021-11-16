open Core
   
let debug = ref false

let print s = if !debug then Printf.printf "\n%s\n%!" (Lazy.force s)
let print_tap s = let s' = Lazy.force s in print s';s'                                
