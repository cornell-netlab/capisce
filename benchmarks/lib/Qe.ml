open Core
open Cmd

let vc prog asst =
  vc (GCL.(seq prog (assert_ asst)))

let qe solver simpl body c =
  let (dvs,cvs) = BExpr.vars body in
  let phi =  BExpr.forall dvs body in
  let phi = if simpl then BExpr.simplify phi else phi in
  let size = -1 in
  if BExpr.qf phi then
    let res = BExpr.to_smtlib phi in
    let dur = Clock.stop c in
    (dur, res, size, false)
  else    
    (* let phi_str = BExpr.to_smtlib phi in *)
    let res = solver dvs cvs phi in
    let dur = Clock.stop c in
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
    let c = Clock.start () in
    let uneliminated_dvs = List.filter dvs ~f:(fun v -> String.is_substring res ~substring:(Var.str v)) in
    let quantified_res = Printf.sprintf "(forall (%s) %s)" (Var.list_to_smtlib_quant uneliminated_dvs) res in 
    let res = Solver.run_z3 (Smt.assert_apply cvs quantified_res) in
    let z3_dur = Clock.stop c in 
    (Float.(dur + z3_dur), res, size, true)

let var_still_used smtstring var =
  String.is_substring smtstring ~substring:(Var.str var)

let solve_wto solver ?(with_timeout:int option) cvs smt =
  match solver, with_timeout with
  | `Z3, Some timeout ->
    Solver.run_z3 (Smt.assert_apply ~timeout cvs smt)
  | `Z3, None ->
    Solver.run_z3 (Smt.assert_apply cvs smt)
  | `Z3Light,_ ->
    Solver.run_z3 (Smt.assert_apply_light cvs smt)
  | `CVC4,_ ->
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
    let dvs' = List.filter dvs ~f:(var_still_used smt) in
    let cvs' = List.filter cvs ~f:(var_still_used smt) in
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
  BExpr.to_smtlib phi
  |> solver_fixpoint_str gas solvers dvs cvs

let cvc4_z3_fix gas solvers simpl (prog, asst) =
  let c = Clock.start () in
  let body = vc prog asst in
  qe (solver_fixpoint gas solvers) simpl body c

let subsolving (prog, asst) =
  let c = Clock.start () in
  Log.qe "%s" @@ lazy "computing vc";
  let phi = vc prog asst in
  Log.qe "%s" @@ lazy "getting vars";
  let (dvs, _) = BExpr.vars phi in
  (* let dvs = List.dedup_and_sort dvs ~compare:(fun a b -> Int.compare (Var.size b) (Var.size a)) in *)
  Log.qe "%s" @@ lazy "Counting Vars";
  List.iter dvs ~f:BExpr.incr_q;
  Log.qe "%s" @@ lazy "smart constructors";
  (* let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in *)
  let compare v1 v2 = Int.compare (Var.size v1) (Var.size v2) in
  let sorted_dvs = List.sort dvs ~compare in
  Log.qe "The sorted dataplane variables:%s\n" @@ lazy (List.to_string sorted_dvs ~f:Var.str);
  (* sort and re-sort by number of occurences *)
  let qf_phi = List.fold_left sorted_dvs ~init:phi
                 ~f:(fun qf_phi x -> 
                   Log.qe "running the bottom up solver for %s" @@ lazy (Var.str x);
                   let soln = BottomUpQe.cnf_qe (solve_wto `Z3) (BExpr.forall [x] qf_phi) |> Option.value_exn in
                   if List.exists (fst (BExpr.vars soln)) ~f:(fun y -> String.(Var.str x = Var.str y)) then begin
                       Printf.printf "Didn't elim %s from \n %s\n\n GOT \n %s\n %!" (Var.str x) (BExpr.to_smtlib qf_phi) (BExpr.to_smtlib soln);
                       assert false
                     end;
                  soln
                 ) in
  Log.qe "%s" @@ lazy "getting the vars of the result";
  let dvs', cvs = BExpr.vars qf_phi in
  Log.qe "%s" @@ lazy (Printf.sprintf "checking all dataplane variables have been eliminated from %s" (BExpr.to_smtlib qf_phi));
  if not (List.is_empty dvs') then begin
      Printf.printf "started with:\n vars: %s \n form: %s\n%!" (List.to_string dvs ~f:(Var.str)) (BExpr.to_smtlib phi);
      Printf.printf "ERROR Not QF:\n vars: %s \n form: %s\n%!" (List.to_string dvs' ~f:(Var.str)) (BExpr.to_smtlib qf_phi);
      failwith "QF Failed when it said it succeeded"
    end
  else 
    Log.qe "No dataplane variables, only control vars: %s" @@ lazy (List.to_string cvs ~f:(Var.str));
  Log.qe "%s" @@ lazy "using z3 to simplify";
  let qf_phi_str = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify qf_phi))) in
  Log.qe "%s" @@ lazy "done";
  (Clock.stop c, qf_phi_str, -1, true)


let check_no_quantified_vars dvs phi dvs' qf_phi =
  Log.qe "checking all dataplane variables have been eliminated from %s" @@ lazy (BExpr.to_smtlib qf_phi);
  if not (List.is_empty dvs') then
    failwithf "QF Failed when it said it succeeded.\n\tstarted with:\n vars: %s \n form: %s\n%!\tERROR Not QF:\n vars: %s \n form: %s\n%!"
      (List.to_string dvs ~f:(Var.str))
      (BExpr.to_smtlib phi)
      (List.to_string dvs' ~f:(Var.str))
      (BExpr.to_smtlib qf_phi)
      ()


let solve_one ~qe phi : (Var.t list * string) option =
  let open Option.Let_syntax in
  let (dvs, _) = BExpr.vars phi in
  List.iter dvs ~f:BExpr.incr_q;
  Log.qe "%s" @@ lazy "smart constructors";
  let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in
  let%map qf_phi = qe (solve_wto `Z3) qphi in
  Log.qe "%s" @@ lazy "getting the vars of the result";
  let dvs', cvs = BExpr.vars qf_phi in
  check_no_quantified_vars dvs phi dvs' qf_phi;
  Log.qe "%s" @@ lazy "using z3 to simplify";
  let qf_phi_str = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify qf_phi))) in
  Log.qe "%s" @@ lazy "done";
  (cvs, qf_phi_str)


let solving_all_paths_inner (prog, asst) =
  let (_, passive) = PassiveGCL.passify GCL.(seq prog (assume asst))  in
  let path_optimized = PassiveGCL.assume_disjuncts passive in
  let pis = PassiveGCL.paths path_optimized in
  let completed = ref Bigint.zero in
  Sequence.fold pis ~init:[] ~f:(fun acc pi ->
      let _, qf_phi_str = PassiveGCL.vc pi |> solve_one ~qe:BottomUpQe.cnf_qe |> Option.value_exn in
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

module TablePathGenerator =
  Generator.Make (TFG.V) (struct
    include TFG.G
    let find_source = TFG.find_source
    let count_cfg_paths = TFG.count_cfg_paths
  end)

module PathGenerator =
  Generator.Make (GCL.V) (struct
    include GCL.G
    let find_source = GCL.find_source
    let count_cfg_paths = GCL.count_cfg_paths
  end
  )

let table_path_to_string (pi : TFG.V.t list) : string =
  List.rev pi
  |> List.map ~f:TFG.V.to_string
  |> String.concat ~sep:" --> "

let handle_failure ~pi ~prog ~gpl ~gcl ~psv ~gpl_graph ~induced_graph =
  Log.path_gen "Table list:\n\t%s\n" @@ lazy (table_path_to_string pi);
  Log.irs "OGGPL:%s\n%!" @@ lazy (GPL.to_string prog);
  Log.irs "GPL:%s\n%!" @@ lazy (GPL.to_string gpl);
  Log.irs "GCL:%s\n%!" @@ lazy (GCL.to_string gcl);
  Log.irs "PSV:%s\n%!" @@ lazy (PassiveGCL.to_string psv);
  Log.graph_dot (TFG.print_graph (Option.value_exn !TablePathGenerator.graph)) "tfg";
  Log.graph_dot (GPL.print_graph gpl_graph) "gpl";
  Log.path_gen_dot (GPL.print_graph induced_graph) "induced_graph";
  raise (Failure "Found unsolveable path")

let passive_vc prog =
  GPL.encode_tables prog
  |> PassiveGCL.passify
  |> snd
  |> PassiveGCL.vc

let paths_per_second paths time_s =  Float.((Bigint.to_float !paths) / time_s)

let completion_time total paths time  =
  let open Float in
  let completed_f = Bigint.to_float !paths in
  let seconds = ((total - completed_f) / (paths_per_second paths time)) in
  let msg f units = Printf.sprintf "%f %s" f units in
  let seconds_per_minute = 60.0 in
  let minutes_per_hour = 60.0 in
  let hours_per_day = 24.0 in
  let days_per_week = 7.0 in
  let weeks_per_year = 52.0 in
  if seconds <= seconds_per_minute then
    msg seconds "seconds"
  else
    let minutes = seconds / seconds_per_minute in
    if minutes <= minutes_per_hour then
      msg minutes "minutes"
    else
      let hours = minutes / minutes_per_hour in
      if hours <= hours_per_day then
        msg hours "hours"
      else
        let days = hours / hours_per_day in
        if days <= days_per_week then
          msg days "days"
        else
          let weeks = days / days_per_week in
          if weeks <= weeks_per_year then
            msg weeks "weeks"
          else
            let years = weeks / weeks_per_year in
            msg years "years"

let write_path_results_to_file ~fn pi dur =
  match fn with
  | None -> ()
  | Some file ->
    let path = List.map pi ~f:(fun vtx ->
        let cmd = TFG.vertex_to_cmd vtx in
        let idx = TFG.V.get_id vtx in
        Printf.sprintf "{\"cmd\": \"%s\", \"idx\": %d}"
          (TFG.to_string cmd) idx
      ) |> String.concat ~sep:"," in
    let path_json = Printf.sprintf "{\"path\": [%s], \"time\":%f}\n%!" path dur in
    FileIO.append path_json ~to_:file

let all_paths gcl =
  let gcl_graph = GCL.construct_graph gcl in          Log.graph_dot (GCL.print_graph gcl_graph) "broken_cfg";
  let tot_paths = PathGenerator.create gcl_graph in   Log.path_gen "couldn't solve table-path, path-exploding the %s paths" @@ lazy (Bigint.to_string tot_paths);
  let paths = ref 0 in
  let rec loop phi_agg =
    match PathGenerator.get_next () with
    | None ->
      Log.debug_s "inner paths done";
      phi_agg
    | Some pi ->
      let pi = List.rev pi in
      Log.debug "Inner Path #%d" @@ lazy !paths;
      Log.debug "Paths to go %d" @@ lazy (Bigint.to_int_exn tot_paths - !paths);
      let gcl = List.map pi ~f:(GCL.vertex_to_cmd) |> GCL.sequence in           (* Log.path_gen "solving path %s" @@ lazy (GCL.to_string gcl);*)
      let phi = GCL.wp gcl BExpr.true_ in  (* Would be efficient with WP *)
      match solve_one phi ~qe:BottomUpQe.optimistic_qe with
      | None ->
        failwithf "Couldn't solve path %s" (GCL.to_string gcl) ()
      | Some (cvs,res) ->
        let qf_psi = Solver.of_smtlib ~dvs:[] ~cvs res in Log.debug "Got %s" @@ lazy res;
        if Solver.check_unsat ~timeout:(Some 1000) cvs qf_psi then begin
          Printf.eprintf "Inner path Failed %s\n%!"  (GCL.to_string gcl);
          Printf.eprintf "Formulae was %s\n%!" res;
          failwith "unsolveable"
        end else begin
          Int.incr paths;
          loop (BExpr.and_ phi_agg qf_psi)
        end
  in
  let phi = loop BExpr.true_ in
  BExpr.simplify phi




let table_paths ~sfreq:_ ~fn ((prsr, prog) : GPL.t * GPL.t) =

  (* Initialize the program state*)                        Log.compiler "Unoptimized GPL parser:\n%s\n" @@ lazy (GPL.to_string prsr);
  let (prsr, prog) = GPL.optimize_seq_pair (prsr, prog) in
  let gcl_prsr = GPL.encode_tables prsr in                 Log.compiler "Optimized GCL parser:\n%s\n" @@ lazy (GCL.to_string gcl_prsr);
  let gpl_graph = GPL.construct_graph prog in              Log.graph "Constructing Graph For Optimized GPL:%s\n%!\n\n" @@ lazy (GPL.to_string prog);
  let tfg_prog = TFG.project prog in                       Log.graph "%s" @@ lazy (GPL.print_key gpl_graph); Log.graph_dot (GPL.print_graph gpl_graph) "gpl";
  let tfg_graph = TFG.construct_graph tfg_prog in          Log.graph_dot (TFG.print_graph tfg_graph) "tfg";
  let tot_paths = TablePathGenerator.create tfg_graph in
  (* track the number of paths *)
  let paths = ref Bigint.zero  in
  (* Only check sufficiency when countdown reaches [sfreq] *)
  (* let countdown = ref 0 in *)
  (* let sufficient phi phi_prog = *)
  (*   (\* check that phi => phi_prog is valid *\) *)
  (*   let vars = BExpr.vars phi_prog |> Tuple2.uncurry (@) in *)
  (*   if !countdown > 0 then begin *)
  (*     Int.decr countdown; *)
  (*     false *)
  (*   end else begin *)
  (*     countdown := sfreq; *)
  (*     Solver.check_unsat vars *)
  (*       BExpr.(and_ phi (not_ phi_prog)) *)
  (*       ~timeout:(Some 1000) *)
  (*   end *)
  (* in *)
  (* DO NOT INLINE --- Pre Computations for performance reasons *)
  let inducer = induce_gpl_from_tfg_path gpl_graph in
  let parser_optimize gcl = GCL.(optimize (seq gcl_prsr gcl)) in
  (* let phi_prog = passive_vc GPL.(seq prsr prog) in *)

  (* Start the timer *)
  let clock = Clock.start () in

  (** THE MAIN LOOP *)
  let rec loop phi_agg =
    (* if sufficient phi_agg phi_prog then *)
    (*   phi_agg *)
    (* else *)
      match TablePathGenerator.get_next () with
      | None -> phi_agg
      | Some pi ->
        (* Failed path #33747 *)
        (*	assume true@0 --> ingress_port_mapping.apply()@2 --> ingress_port_properties.apply()@4 --> switch_config_params.apply()@5 --> port_vlan_mapping.apply()@13 --> spanning_tree.apply()@18 --> assume true@19 --> assume true@40 --> assume true@46 --> assume true@76 --> assume true@80 --> assume true@84 --> assume true@88 --> assume true@92 --> assume true@96 --> assume true@100 --> assume true@104 --> qos.apply()@105 --> rmac.apply()@108 --> assume true@121 --> assume true@125 --> assume true@129 --> assume true@133 --> assume true@137 --> assume true@141 --> ipv4_racl.apply()@142 --> ipv4_urpf.apply()@147 --> assume true@156 --> assume true@157 --> ipv4_fib.apply()@160 --> assume true@167 --> ipv4_fib_lpm.apply()@168 --> assume true@169 --> assume true@170 --> assume true@176 --> assume true@177 --> assume true@178 --> assume true@179 --> compute_non_ip_hashes.apply()@182 --> assume true@186 --> compute_other_hashes.apply()@188 --> assume true@246 --> ecmp_group.apply()@253 --> assume true@254 --> assume true@261 --> assume true@267 --> assume true@271 --> assume true@275 --> learn_notify.apply()@276 --> assume true@277 --> assume true@278 --> assume true@286 --> assume true@290 --> assume true@294 --> assume true@298 --> assume true@302 --> assume true@306 --> assume true@310 --> assume true@314 --> assume true@318 --> assume true@322 --> assume true@326 --> assume true@330 --> assume true@334 --> assume true@338 --> system_acl.apply()@339 --> drop_stats_0.apply()@342 --> assume true@343 --> assume true@344 --> assume true@345 --> assume true@346*)
        (* if Bigint.(!paths < of_int 33747) then begin        Log.debug "Skipping Path %s" (lazy (Bigint.to_string !paths)); *)
        (*   Bigint.incr paths; *)
        (*   loop phi *)
        (* end else *)
        let pi_clock = Clock.start () in
        let time_s = Float.(Clock.stop clock / 1000.0) in   Log.debug "Table list:\n\t%s\n" @@ lazy (table_path_to_string pi);
                                                            Log.debug_s (Printf.sprintf "[%fs] ^Path #%s" time_s (Bigint.to_string !paths));
                                                            Log.debug "There are %s paths" @@ lazy (Bigint.to_string tot_paths);
                                                            Log.debug "current rate is %f paths per second" @@ lazy (paths_per_second paths time_s);
                                                            Log.debug "estimated time to completion: %s" @@ lazy (completion_time (Bigint.to_float tot_paths) paths time_s);
        let induced_graph = inducer pi in                   Log.path_gen_dot (GPL.print_graph induced_graph) "induced_graph";
        let gpl = GPL.of_graph induced_graph in             Log.irs "GPL:\n%s\n%!" @@ lazy (GPL.to_string gpl);
        let gcl = GPL.encode_tables gpl in                  Log.irs "GCL:\n%s\n%!" @@ lazy (GCL.to_string gcl);
        let full_gcl = parser_optimize gcl in                    Log.irs "GCL w/ Parser (Optimized):\n%s\n%!" @@ lazy (GCL.to_string gcl);
        let psv = PassiveGCL.(passify full_gcl) |> snd in
        let phi = PassiveGCL.vc psv in
        (* if sufficient phi_agg phi then                      let () = Log.debug_s "\tSkipped for sufficiency!;\n%!" in *)
        (*   loop phi_agg *)
        (* else                                                let () = Log.debug_s "solving" in *)
          match solve_one phi ~qe:BottomUpQe.optimistic_qe with
          | None ->
            Log.compiler "couldn't solve %s\n" @@ lazy (GCL.to_string full_gcl);
            all_paths gcl
          | Some (cvs, res) ->
            let qf_psi = Solver.of_smtlib ~dvs:[] ~cvs res in
            let sat = Solver.check_sat cvs qf_psi in
            if not sat then handle_failure
                ~pi  ~prog ~gpl ~gcl ~psv
                ~gpl_graph ~induced_graph;
            Bigint.incr paths;                                Log.smt "Path condition: \n%s\n%!" @@ lazy (BExpr.to_smtlib phi);
            let dur = Clock.stop pi_clock in
            write_path_results_to_file ~fn pi dur;
            loop (BExpr.and_ qf_psi phi_agg)
  in
  loop BExpr.true_


let check_for_parser prsr gpl_prsr=
  match prsr with
    | `Use  ->
      gpl_prsr
    | `Skip ->
      GPL.skip

let preprocess ~prsr gpl_pair =
  gpl_pair
  |> Tuple2.map_fst ~f:(check_for_parser prsr)
  |> Tuple2.map     ~f:(GPL.normalize_names)

let table_infer ~sfreq ~prsr ~fn gpl_pair =
  preprocess ~prsr gpl_pair
  |> table_paths ~sfreq ~fn
