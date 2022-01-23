open Core

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
    (dur, res, size, false)
  else    
    (* let phi_str = BExpr.to_smtlib phi in *)
    let () = Log.print @@ lazy ("it aint, call solver") in    
    let res = solver dvs cvs phi in
    let dur = Clock.stop c in
    let () = Log.print @@ lazy (Printf.sprintf "called, %fms" (Time.Span.to_ms dur)) in
    (dur, res, size, true)

let exp_inner stringifier runner simpl (prog, asst) =
  let c = Clock.start () in
  let body = vc prog asst in
  let solver _ cvs phi = runner (stringifier cvs (BExpr.to_smtlib phi)) in
  qe solver simpl body c

let cvc4_infer = exp_inner Smt.simplify Solver.run_cvc4
let cvc4_check = exp_inner Smt.check_sat Solver.run_cvc4 
let z3_check = exp_inner Smt.check_sat Solver.run_z3              
let z3_infer = exp_inner Smt.assert_apply Solver.run_z3
let princess_infer = exp_inner Smt.simplify Solver.run_princess

let cvc4_z3_infer simpl (prog, asst) =
  let (dur, res, size, use_solver) = cvc4_infer simpl (prog, asst) in
  let (dvs,cvs) = BExpr.vars (vc prog asst) in  
  if Smt.qf res then
    (dur,res,size,use_solver)
  else
    let () = Log.print @@ lazy (Printf.sprintf "CVC4 computed gave\n%s" res) in
    let c = Clock.start () in
    let uneliminated_dvs = List.filter dvs ~f:(fun v -> String.is_substring res ~substring:(Var.str v)) in
    let quantified_res = Printf.sprintf "(forall (%s) %s)" (Var.list_to_smtlib_quant uneliminated_dvs) res in 
    let res = Solver.run_z3 (Smt.assert_apply cvs quantified_res) in
    let z3_dur = Clock.stop c in 
    (Time.Span.(dur + z3_dur), res, size, true)

let var_still_used smtstring var =
  String.is_substring smtstring ~substring:(Var.str var)

let solve solver cvs smt =
  match solver with
  | `Z3 ->
     Log.print @@ lazy "Z3";
     Solver.run_z3 (Smt.assert_apply cvs smt)
  | `Z3Light ->
     Log.print @@ lazy "Z3";
     Solver.run_z3 (Smt.assert_apply_light cvs smt)
  | `CVC4 ->
     Log.print @@ lazy "CVC4";
     Solver.run_cvc4 (Smt.simplify cvs smt)

let normalize solver dvs cvs res =
  if Smt.success res then
      match solver with
      | `Z3 | `Z3Light ->
         let goals = BExpr.to_smtlib (BExpr.of_smtlib ~cvs res) in
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
       let res = normalize solver dvs cvs' (solve solver cvs' smt) in
       if Smt.qf res then
         res
       else
         solver_fixpoint_str (gas-1) (solvers'@[solver]) dvs' cvs' res

let solver_fixpoint gas solvers dvs cvs phi =
  let () = Log.print @@ lazy "serializing to smt" in
  if false then  
    let phi = BExpr.predicate_abstraction phi in
    let str = Printf.sprintf "(forall (%s) %s)" (BExpr.abstract_qvars phi) (BExpr.to_smtlib phi) in
    solver_fixpoint_str gas solvers [] cvs str
  else
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

let subsolving (prog, asst) =
  let c = Clock.start () in
  let phi = vc prog asst in
  let (dvs, _) = BExpr.vars phi in
  let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in
  let qf_phi = BExpr.bottom_up_qe (solve `Z3) qphi in
  (Clock.stop c, BExpr.to_smtlib qf_phi, -1, true)
