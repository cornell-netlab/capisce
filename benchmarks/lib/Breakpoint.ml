open Core
   
let set ?(colors=[]) b =
  if b then (
    ANSITerminal.printf colors "[Press Enter to Continue]\n%!"; Out_channel.flush stdout;
    ignore (Stdio.In_channel.(input_char stdin) : char option) )
