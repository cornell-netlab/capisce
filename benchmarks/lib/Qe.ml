open Core
open Cmd

let vc prog asst =
  vc (GCL.(seq prog (assert_ asst)))

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

let solve_wto solver ?(with_timeout:int option) cvs smt =
  match solver, with_timeout with
  | `Z3, Some timeout ->
     Log.print @@ lazy (Printf.sprintf "Z3 with timeout %d" timeout);
     Solver.run_z3 (Smt.assert_apply ~timeout cvs smt)
  | `Z3, None ->
    Log.print @@ lazy "Z3";
    Solver.run_z3 (Smt.assert_apply cvs smt)
  | `Z3Light,_ ->
     Log.print @@ lazy "Z3";
     Solver.run_z3 (Smt.assert_apply_light cvs smt)
  | `CVC4,_ ->
     Log.print @@ lazy "CVC4";
     Solver.run_cvc4 (Smt.simplify cvs smt)

let solve solver cvs smt = solve_wto solver cvs smt     

let normalize solver dvs cvs res =
  if Smt.success res then
      match solver with
      | `Z3 | `Z3Light ->
         let goals = BExpr.to_smtlib (Solver.of_smtlib ~dvs ~cvs res) in
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

let subsolving (prog, asst) =
  let c = Clock.start () in
  Log.print @@ lazy "computing vc";
  let phi = vc prog asst in
  Log.print @@ lazy "getting vars";
  let (dvs, _) = BExpr.vars phi in
  (* let dvs = List.dedup_and_sort dvs ~compare:(fun a b -> Int.compare (Var.size b) (Var.size a)) in *)
  Log.print @@ lazy "Counting Vars";
  Log.enable_measurement ();  
  List.iter dvs ~f:BExpr.incr_q;
  Log.print @@ lazy "smart constructors";
  (* let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in *)
  let compare v1 v2 = Int.compare (Var.size v1) (Var.size v2) in
  let sorted_dvs = List.sort dvs ~compare in
  Log.print @@ lazy (Printf.sprintf "The sorted dataplane variables:%s\n" (List.to_string sorted_dvs ~f:Var.str));
  (* sort and re-sort by number of occurences *)
  let qf_phi = List.fold_left sorted_dvs ~init:phi
                 ~f:(fun qf_phi x -> 
                   Log.print @@ lazy (Printf.sprintf "running the bottom up solver for %s#%d" (Var.str x) (Var.size x));
                   let soln = BottomUpQe.qe (solve_wto `Z3) (BExpr.forall [x] qf_phi) in
                   if List.exists (fst (BExpr.vars soln)) ~f:(fun y -> String.(Var.str x = Var.str y)) then begin
                       Printf.printf "Didn't elim %s from \n %s\n\n GOT \n %s\n %!" (Var.str x) (BExpr.to_smtlib qf_phi) (BExpr.to_smtlib soln);
                       assert false
                     end
                   else begin
                       Printf.printf "REMOVED %s\n%!" (Var.str x);
                     end;
                   soln
                 ) in
  Log.print @@ lazy "getting the vars of the result";  
  let dvs', cvs = BExpr.vars qf_phi in
  Log.print @@ lazy (Printf.sprintf "checking all dataplane variables have been eliminated from %s" (BExpr.to_smtlib qf_phi));    
  if not (List.is_empty dvs') then begin
      Printf.printf "started with:\n vars: %s \n form: %s\n%!" (List.to_string dvs ~f:(Var.str)) (BExpr.to_smtlib phi);
      Printf.printf "ERROR Not QF:\n vars: %s \n form: %s\n%!" (List.to_string dvs' ~f:(Var.str)) (BExpr.to_smtlib qf_phi);
      failwith "QF Failed when it said it succeeded"
    end
  else 
    Log.print @@ lazy (Printf.sprintf "No dataplane variables, only control vars: %s" (List.to_string cvs ~f:(Var.str)));
  Log.print @@ lazy "using z3 to simplify";    
  let qf_phi_str = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify qf_phi))) in
  Log.print @@ lazy "done";    
  (Clock.stop c, qf_phi_str, -1, true)


let check_no_quantified_vars dvs phi dvs' qf_phi =
  Log.print @@ lazy (Printf.sprintf "checking all dataplane variables have been eliminated from %s" (BExpr.to_smtlib qf_phi));
  if not (List.is_empty dvs') then
    failwithf "QF Failed when it said it succeeded.\n\tstarted with:\n vars: %s \n form: %s\n%!\tERROR Not QF:\n vars: %s \n form: %s\n%!"
      (List.to_string dvs ~f:(Var.str))
      (BExpr.to_smtlib phi)
      (List.to_string dvs' ~f:(Var.str))
      (BExpr.to_smtlib qf_phi)
      ()


let solve_one asserted_prog =
  let phi = PassiveGCL.vc asserted_prog in
  let (dvs, _) = BExpr.vars phi in
  List.iter dvs ~f:BExpr.incr_q;
  Log.print @@ lazy "smart constructors";
  let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in
  let qf_phi = BottomUpQe.qe (solve_wto `Z3) qphi in
  Log.print @@ lazy "getting the vars of the result";
  let dvs', cvs = BExpr.vars qf_phi in
  check_no_quantified_vars dvs phi dvs' qf_phi;
  Log.print @@ lazy "using z3 to simplify";
  let qf_phi_str = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify qf_phi))) in
  Log.print @@ lazy "done";
  (cvs, qf_phi_str)


let solving_all_paths_inner (prog, asst) =
  let (_, passive) = PassiveGCL.passify GCL.(seq prog (assume asst))  in
  let path_optimized = PassiveGCL.assume_disjuncts passive in
  Breakpoint.set true;
  let pis = PassiveGCL.paths path_optimized in
  let completed = ref Bigint.zero in
  Sequence.fold pis ~init:[] ~f:(fun acc pi ->
      Log.print @@ lazy (Printf.sprintf "Solving path:\n%s \n" (PassiveGCL.to_string pi));
      let _, qf_phi_str = solve_one pi in
      Bigint.incr completed;
      acc @ [qf_phi_str])

(* let solving_all_paths_inner (prog, asst) = *)
(*   let prog = GCL.(seq prog (assume asst)) in *)
(*   let passive = PassiveGCL.passify prog in *)
(*   let path_optimized = PassiveGCL.assume_disjuncts passive in *)
(*   Breakpoint.set true; *)
(*   let pis = PassiveGCL.paths path_optimized in *)
(*   let completed = ref Bigint.zero in *)
(*   Sequence.fold pis ~init:[] ~f:(fun acc pi -> *)
(*       Log.print @@ lazy (Printf.sprintf "Computing WP for path:\n%s \n" (PassiveGCL.to_string pi)); *)
(*       let phi = PassiveGCL.(wrong (seq pi (assert_ asst))) in *)
(*       let (dvs, _) = BExpr.vars phi in *)
(*       List.iter dvs ~f:BExpr.incr_q; *)
(*       Log.print @@ lazy "smart constructors"; *)
(*       let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in *)
(*       let qf_phi = BottomUpQe.qe (solve_wto `Z3) qphi in *)
(*       Log.print @@ lazy "getting the vars of the result"; *)
(*       let dvs', cvs = BExpr.vars qf_phi in *)
(*       Log.print @@ lazy (Printf.sprintf "checking all dataplane variables have been eliminated from %s" (BExpr.to_smtlib qf_phi)); *)
(*       if not (List.is_empty dvs') then begin *)
(*         Printf.printf "started with:\n vars: %s \n form: %s\n%!" (List.to_string dvs ~f:(Var.str)) (BExpr.to_smtlib phi); *)
(*         Printf.printf "ERROR Not QF:\n vars: %s \n form: %s\n%!" (List.to_string dvs' ~f:(Var.str)) (BExpr.to_smtlib qf_phi); *)
(*         failwith "QF Failed when it said it succeeded" *)
(*       end *)
(*       else *)
(*         Log.print @@ lazy (Printf.sprintf "No dataplane variables, only control vars: %s" (List.to_string cvs ~f:(Var.str))); *)
(*       Log.print @@ lazy "using z3 to simplify"; *)
(*       let qf_phi_str = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify qf_phi))) in *)
(*       Log.print @@ lazy "done"; *)
(*       Bigint.incr completed; *)
(*       Printf.printf "%s paths solved\n" (Bigint.to_string !completed); *)
(*       acc @ [qf_phi_str]) *)


let solving_all_paths (prog,asst) =
  let c    = Clock.start () in
  let phis = solving_all_paths_inner (prog, asst) in
  let time = Clock.stop c in
  let phi_str = String.concat ~sep:"\n\n" phis in
  (time, phi_str, -1, true)


let table_path_to_string (pi : TFG.Vertex.t list) : string =
  List.rev pi
  |> List.map ~f:(fun (pipeline, idx ) -> Printf.sprintf "%s@%d" (Pipeline.to_smtlib pipeline) idx)
  |> String.concat ~sep:" --> "

let dot f = Printf.sprintf "dot -Tps %s.dot -o %s.pdf; xdg-open %s.pdf;" f f f


let table_paths ((prog, asst) : TFG.t * BExpr.t) =
  let asserted_prog = TFG.(seq prog (assert_ asst)) in
  let gpl_prog = TFG.inject asserted_prog in
  Log.print @@ lazy (Printf.sprintf "Constructing Graph For Gpl:%s\n%!\n\n" (GPL.to_string gpl_prog));
  let gpl_graph = GPL.construct_graph gpl_prog in
  if !Log.debug then GPL.print_graph (Some "gpl.dot") gpl_graph;
  Generator.create asserted_prog;
  let rec loop phi =
    (* TODO CHECK SUFFICIENCY of phi*)
    match Generator.get_next () with
    | None -> phi
    | Some pi ->
      let induced_program = GPL.induce gpl_graph pi in
      GPL.print_graph (Some "induced_program.dot") induced_program;
      let gpl = GPL.of_graph induced_program in
      Log.print @@ lazy (Printf.sprintf "GPL:\n%s\n%!" (GPL.to_string gpl));
      let gcl = GPL.encode_tables gpl in
      Log.print @@ lazy (Printf.sprintf "GCL:\n%s\n%!" (GCL.to_string gcl));
      let gcl = GCL.optimize gcl in
      let (_, psv) = PassiveGCL.passify gcl in
      let (cvs, qf_psi_str) = solve_one psv in
      let qf_psi = Solver.of_smtlib ~dvs:[] ~cvs qf_psi_str in
      let sat = Solver.check_sat cvs qf_psi in
      if sat then Printf.printf "SAT\n%!" else Printf.printf "UNSAT\n%!";
      if sat then
        assert (not (BExpr.(equal qf_psi false_)))
      else begin
        Printf.printf "Table list:\n\t%s\n" (table_path_to_string pi);
        Printf.printf "TFG:%s\n%!" (TFG.to_string asserted_prog);
        Printf.printf "GPL:\n%s\n\nGCL:%s\n\nPSV:%s\n\n"
          (GPL.to_string gpl) (GCL.to_string gcl) (PassiveGCL.to_string psv);
        Printf.printf "%s\n%s\n%s\n%!" (dot "induced_program") (dot "tfg") (dot "gpl");
        raise (Failure "Found unsolveable path")
      end;
      loop (BExpr.and_ qf_psi phi)
  in
  loop BExpr.true_

let preprocess gpl_prsr gpl_pipeline =
  Log.print @@ lazy (Printf.sprintf "parser:\n%s\n%!" (GPL.to_string gpl_prsr));
  let symbolic_parser = GPL.symbolize gpl_prsr in
  Log.print @@ lazy (Printf.sprintf "symbolic parser:\n%s\n%!" (GPL.to_string symbolic_parser));
  let gpl = GPL.seq symbolic_parser gpl_pipeline in
  let tfg = TFG.project gpl in
  tfg


let table_infer (gpl_prsr, gpl_pipeline) =
  let tfg = preprocess gpl_prsr gpl_pipeline in
  let cpf = table_paths (tfg, BExpr.true_) in
  cpf
