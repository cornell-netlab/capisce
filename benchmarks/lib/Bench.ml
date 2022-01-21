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
  success s
  && qf s
  && String.length s > 0


let log_row dur str size use_solver =
  Printf.eprintf "%f,%b,%d,%b\n%!" (Time.Span.to_ms dur) (answer_ok str) size use_solver

let vc prog asst =
  Cmd.(vc (seq prog (assert_ asst)))

let qe solver simpl body c =
  Log.print @@ lazy ("getting vars");
  let (dvs,cvs) = BExpr.vars body in
  Log.print @@ lazy ("adding smart? forall");
  let phi =  BExpr.forall dvs body in
  Log.print @@ lazy ("simplifying");
  let phi = if simpl then BExpr.simplify phi else phi in
  let size = -1 in
  Log.print @@ lazy ("checking if phi is qf");
  if BExpr.qf phi then
    let () = Log.print @@ lazy ("it is, stringify") in
    let res = BExpr.to_smtlib phi in
    let dur = Clock.stop c in
    log_row dur res size false;
    (dur, res, size, false)
  else    
    (* let phi_str = BExpr.to_smtlib phi in *)
    let () = Log.print @@ lazy ("it aint, call solver") in    
    let res = solver dvs cvs phi in
    let dur = Clock.stop c in
    let () = Log.print @@ lazy (Printf.sprintf "called, %fms" (Time.Span.to_ms dur)) in
    log_row dur res size true;
    (dur, res, size, true)

let exp_inner stringifier runner simpl (prog, asst) =
  let c = Clock.start () in
  let body = vc prog asst in
  let solver _ cvs phi = runner (stringifier cvs phi) in
  qe solver simpl body c

let cvc4_infer = exp_inner Smt.simplify Solver.run_cvc4
let cvc4_check = exp_inner Smt.check_sat Solver.run_cvc4 
let z3_check = exp_inner Smt.check_sat Solver.run_z3              
let z3_infer = exp_inner Smt.assert_apply Solver.run_z3
let princess_infer = exp_inner Smt.simplify Solver.run_princess

let cvc4_z3_infer simpl (prog, asst) =
  let (dur, res, size, use_solver) = cvc4_infer simpl (prog, asst) in
  let (dvs,cvs) = BExpr.vars (vc prog asst) in  
  if doesnt_contain_any res ["forall"; "exists"] then
    (dur,res,size,use_solver)
  else
    let () = Log.print @@ lazy (Printf.sprintf "CVC4 computed gave\n%s" res) in
    let c = Clock.start () in
    let uneliminated_dvs = List.filter dvs ~f:(fun v -> String.is_substring res ~substring:(Var.str v)) in
    let quantified_res = Printf.sprintf "(forall (%s) %s)" (Var.list_to_smtlib_quant uneliminated_dvs) res in 
    let res = Solver.run_z3 (Smt.assert_apply_str cvs quantified_res) in
    let z3_dur = Clock.stop c in 
    (Time.Span.(dur + z3_dur), res, size, true)

let var_still_used smtstring var =
  String.is_substring smtstring ~substring:(Var.str var)

let solve solver cvs smt =
  match solver with
  | `Z3 ->
     Log.print @@ lazy "Z3";
     Solver.run_z3 (Smt.assert_apply_str cvs smt)
  | `Z3Light ->
     Log.print @@ lazy "Z3";
     Solver.run_z3 (Smt.assert_apply_light_str cvs smt)
  | `CVC4 ->
     Log.print @@ lazy "CVC4";
     Solver.run_cvc4 (Smt.simplify_str cvs smt)

let normalize solver dvs res =
  if success res then
      match solver with
      | `Z3 | `Z3Light ->
         let goals = Solver.extract_z3_goals res in
         if String.is_substring goals ~substring:":precision" then
           "true"
         else
           goals
      | `CVC4 ->
         let dvs' = List.filter dvs ~f:(var_still_used res) in
         if List.is_empty dvs' then
           res
         else
           Printf.sprintf "(forall (%s) %s)" (Var.list_to_smtlib_quant dvs') res
  else
    begin
      Printf.eprintf "Solver failed:\n %s" res;
      exit (-1)
    end
      
let rec solver_fixpoint_str gas solvers dvs cvs (smt : string) : string =
  if gas <= 0 then smt else
    let () = Log.print @@ lazy (Printf.sprintf "checking if vars %i are used in string of size %i" (List.length (dvs @ cvs)) (String.length smt)) in
    let dvs' = List.filter dvs ~f:(var_still_used smt) in
    let cvs' = List.filter cvs ~f:(var_still_used smt) in
    let () = Log.print @@ lazy "\tdone" in 
    match solvers with
    | [] ->
       failwith "Ran out of solvers to try"
    | solver :: solvers' ->
       let res = normalize solver dvs (solve solver cvs' smt) in
       if qf res then
         res
       else
         solver_fixpoint_str (gas-1) (solvers'@[solver]) dvs' cvs' res

let solver_fixpoint gas solvers dvs cvs phi =
  let () = Log.print @@ lazy "serializing to smt" in
  BExpr.to_smtlib phi
  |> solver_fixpoint_str gas solvers dvs cvs        

let cvc4_z3_fix gas solvers simpl (prog, asst) =
  let c = Clock.start () in
  Log.print @@ lazy "computing wp...";
  let body = vc prog asst in
  Log.print @@ lazy "solving";
  qe (solver_fixpoint gas solvers) simpl body c

let cnf_fix_infer gas solvers simpl (prog, asst) =
  let c = Clock.start () in
  Log.print @@ lazy "computing wps";
  (* let bodies = BExpr.get_conjuncts (vc prog asst) in *)
  let bodies = List.map (Cmd.pathify prog) ~f:(fun p -> vc p asst) in 
  let count = ref 0 in
  let total = List.length bodies in
  let qe_bodies =
    List.fold bodies ~init:"" ~f:(fun acc body ->        
        let (_,res,_,_) = qe (solver_fixpoint gas solvers) simpl body (Clock.start()) in
        count := !count + 1;
        Printf.printf "%d out of %d analyzed\r%!" !count total;        
        Printf.sprintf "%s\n\t%s" acc res
      ) in
  Printf.printf "\n%!";
  (Clock.stop c,
   Printf.sprintf "(and %s)" qe_bodies,
   -1,
   true)
  

let princess = exp ~f:princess_infer
let z3 = exp ~f:z3_infer
let cvc4 = exp ~f:cvc4_infer
