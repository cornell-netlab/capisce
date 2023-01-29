open Core
open ASTs

let ternary_match_gen ~bitwidth ~num_ternary ~num_exact =
  let var (s : int -> string) (f : int -> int) (i : int) = Var.make (s @@ f i) bitwidth in
  let hdr = Printf.sprintf "hdr.h%d" in
  let offset = (+) num_ternary in
  let ctrl = Printf.sprintf "_symb$t$match_%d" in
  let isValid hdr =
    Expr.var (Var.make (Printf.sprintf "%s.is_valid" @@ Var.str hdr) 1)
  in
  let x hdr = Expr.var (Var.map hdr ~f:(Printf.sprintf "%s.x")) in
  let dont_care match_ =
    Expr.var (Var.make (Printf.sprintf "%s$DONT_CARE" @@ Var.str match_) 1)
  in
  let (%.) a b = a |> b in
  let ternary_headers = List.init num_ternary ~f:(var hdr Fn.id) in
  let exact_headers   = List.init num_exact   ~f:(var hdr offset) in
  let ternary_matches = List.init num_ternary ~f:(var ctrl Fn.id) in
  let exact_matches   = List.init num_exact   ~f:(var ctrl offset) in
  let test b = BExpr.(eq_ b (Expr.bvi 1 1)) in
  GCL.sequence @@
  List.map2_exn ternary_headers ternary_matches ~f:(fun hdr match_x ->
      let open GCL in
      ite (test (dont_care match_x)) (
        skip
      ) (sequence [
          assert_ (test (hdr %. isValid));
          assume BExpr.(eq_ (hdr %. x) (Expr.var match_x));
        ] )
    ) @
  List.map2_exn exact_headers exact_matches ~f:(fun hdr match_x ->
      let open GCL in
      sequence [
        assert_ (test (hdr %. isValid));
        assume BExpr.(eq_ (hdr %. x) (Expr.var match_x));
      ]
    )

let ternary_match_benchmark () =
  let open List.Let_syntax in
  let ternary_max = 20 in
  let exact_max = 20 in
  let bitwidth = 32 in
  let%map num_ternary = List.init (ternary_max + 1) ~f:Fn.id in
  let%map num_exact = List.init (exact_max + 1) ~f:Fn.id in
  let exp = ternary_match_gen ~bitwidth ~num_ternary ~num_exact in
  let c = Clock.start () in
  let psi = Qe.all_paths exp None None in
  let runtime = Clock.stop c in
  (num_ternary, num_exact, runtime, BExpr.size psi)
