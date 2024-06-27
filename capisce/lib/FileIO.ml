open Core

let tmp () =
  Printf.sprintf "/tmp/tmp_%d.smt2" (Random.int 1000)

let write data ~to_ =
  let outc = Out_channel.create to_ in
  try
    fprintf outc "%s\n%!" data;
    Out_channel.close outc
  with e ->
    Out_channel.close outc;
    raise e

let append data ~to_ =
  let outc = Out_channel.create ~append:true to_ in
  try
    fprintf outc "%s\n%!" data;
    Out_channel.close outc
  with e ->
    Out_channel.close outc;
    raise e

let tmp_write str =
  let file = tmp () in
  write str ~to_:file;
  file
