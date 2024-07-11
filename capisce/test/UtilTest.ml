open Core
open Capisce


let number_cases =
  [ (* [(n,b)] you need [b] bits to encode the number [n] *)
    0,1;
    1,1;
    2,2;
    3,2;
    4,3;
    5,3;
    6,3;
    7,3
  ]


let things_cases =
  [ (* [(n,b)] you need [b] bits to encode a set of with [n] elements *)
    0,1; (* can't have empty bitwidths *)
    1,1; (*1*)
    2,1; (* 0 1 *)
    3,2; (* 00 01 10 *)
    4,2; (* 00 01 10 11 *)
    5,3; (* 000 001 010 011 1000 *)
    6,3; (* 000 001 010 011 1000 1001 *)
    7,3; (* 000 001 010 011 1000 1001 1010 *)
  ]

let tests =
  List.map things_cases ~f:(fun (n, expected_bits) ->
      let test () =
        Util.bits_to_encode_n_things n |> Alcotest.(check int) "equal" expected_bits
      in
      Alcotest.test_case (Printf.sprintf "%d bits to encode %d things" expected_bits n) `Quick test)
  @
  List.map number_cases ~f:(fun (n, expected_bits) ->
      let test () =
        Util.bits_to_encode_number_n n |> Alcotest.(check int) "equal" expected_bits
      in
      Alcotest.test_case (Printf.sprintf "%d bits to encode the number %d" expected_bits n) `Quick test)
