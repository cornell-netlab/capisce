let debug = ref false

let print s = if !debug then Printf.printf "\n%s\n%!" s
let print_tap s = print s;s                                