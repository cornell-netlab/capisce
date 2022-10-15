open Core
   
let debug = ref false
let measure = ref false          

let print s = if !debug then Printf.printf "\n%s\n%!" (Lazy.force s)
let print_tap s = let s' = Lazy.force s in print s';s'                                

let enable_measurement () =
  print @@ lazy "Enabling measurement";
  measure := true
let measure s = if !measure then  Printf.eprintf "%s\n%!" s              

let size d = measure (Printf.sprintf "size,%f,%d" (Clock.now()) d)

let dot f = Printf.sprintf "dot -Tps %s.dot -o %s.pdf; xdg-open %s.pdf;" f f f
