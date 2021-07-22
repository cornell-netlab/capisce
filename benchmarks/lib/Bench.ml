open Core

let bitwidth = 1
let k tid = Var.make (Printf.sprintf "k%d" tid) bitwidth
let x tid = Var.make (Printf.sprintf "x%d" tid) bitwidth

let tablegen n : Cmd.t =
  let open Cmd in
  let keys = [k n] in
  let d = Var.make "d" bitwidth in
  let actions = [
      d,
      assign (x n) (Expr.var d)
    ]
  in
  let def = assume BExpr.true_ in
  table n keys actions def

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
  let phi = Cmd.wp prog asst in
  let (dvs,cvs) = BExpr.vars phi in
  (cvs, BExpr.forall dvs phi)  
  
let rec benchmark_list max_tables =
  if max_tables <= 1 then
    []
  else
    benchmark_list (max_tables - 1) @ [benchmark max_tables]

let exp ~f one max_tables =
  benchmark_list max_tables
  |> (if one then List.(Fn.compose return last_exn) else Fn.id) 
  |> List.map ~f 

let doesnt_contain_any s subs =
  List.for_all subs ~f:(fun substring -> not (String.is_substring s ~substring))
             
let answer_ok s =
  doesnt_contain_any s ["forall"; "exists"; "error"; "unknown"; "UNKNOWN"]
  && String.length s > 0
             

let log_row dur str =
  Printf.printf "%f,%b\n%!" (Time.Span.to_ms dur) (answer_ok str)
  
  
let princess_inner (cvs, phi) =
  let c = Clock.start () in
  let phi_str = Smt.simplify cvs phi in
  let res = Solver.run_princess phi_str in
  let dur = Clock.stop c in
  log_row dur res;
  (dur, res)
  

let z3_inner (cvs, phi) =
  let c = Clock.start () in
  let phi_str = Smt.assert_apply cvs phi in
  let res = Solver.run_z3 phi_str in
  let dur = Clock.stop c in
  log_row dur res;
  (dur, res)
    

let z3_princess_inner (cvs,phi) =
  let c = Clock.start () in
  let phi_str = Smt.simplify cvs phi in
  let simpl_phi = Solver.run_z3 phi_str in
  let simpl_phi_str = Smt.simplify_str cvs simpl_phi in
  let res = Solver.run_princess simpl_phi_str in
  let dur = Clock.stop c in
  log_row dur res;
  (dur, res)

  
  
let princess = exp ~f:princess_inner   
let z3 = exp ~f:z3_inner
let z3_princess = exp ~f:z3_princess_inner
