open Core

let tmp () =
  Printf.sprintf "/tmp/tmp_%d.smt2" (Random.int 1000)

let write data ~to_ =
  Out_channel.write_all to_ ~data

let append data ~to_ =
  let outc = Out_channel.create ~append:true to_ in
  fprintf outc "%s" data;
  Out_channel.close outc

let tmp_write str =
  let file = tmp () in
  write str ~to_:file;
  file
