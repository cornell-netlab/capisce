open Core
   
let set b =
  if b then (
    Printf.printf "[Press Enter to Continue]\n%!";
    ignore (Stdio.In_channel.(input_char stdin) : char option) )
