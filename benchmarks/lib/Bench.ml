open Core

let bitwidth = 1
let k tid = Var.make (Printf.sprintf "k%d" tid) bitwidth
let x tid = Var.make (Printf.sprintf "x%d" tid) bitwidth

let tablegen n : Cmd.t =
  let open Cmd in
  let keys = [k n] in
  let d = Var.make_symbRow n (Var.make "d" bitwidth) in
  let actions = [
      Some d,
      assign (x n) (Expr.var d);
      None, skip
    ]
  in
  table n keys actions

let rec gen_asst n : BExpr.t =
  let open BExpr in
  if n <= 0 then
    true_
  else
    and_
      (not_ (eq_ (Expr.var (x n)) (Expr.var (k (n+1)))))
      (gen_asst (n-1))

let rec gen_benchmark ntables cs =
  if ntables <= 0 then
    cs
  else
    tablegen ntables :: cs
    |> gen_benchmark (ntables - 1)

let benchmark ntables =
  let prog = Cmd.sequence (gen_benchmark ntables []) in
  let asst = gen_asst (ntables - 1) in
  (prog, asst)

let rec benchmark_list max_tables =
  if max_tables <= 1 then
    []
  else
    benchmark_list (max_tables - 1) @ [benchmark max_tables]

let exp ~f simpl one max_tables =
  benchmark_list max_tables
  |> (if one then List.(Fn.compose return last_exn) else Fn.id)
  |> List.map ~f:(f simpl)

let doesnt_contain_any s subs =
  List.for_all subs ~f:(fun substring -> not (String.is_substring s ~substring))

let success s =
  doesnt_contain_any s ["error"; "unknown"; "UNKNOWN"; "timeout"; "Killed"]

let qf s = doesnt_contain_any s ["forall"; "exists"]
 
let answer_ok s =
  Smt.success s
  && Smt.qf s
  && String.length s > 0
  
let log_row dur str size use_solver =
  Printf.eprintf "%f,%b,%d,%b\n%!" (Time.Span.to_ms dur) (answer_ok str) size use_solver

let princess = exp ~f:Qe.princess_infer
let z3 = exp ~f:Qe.z3_infer
let cvc4 = exp ~f:Qe.cvc4_infer
    
