open Core
open ASTs


(* let vc prog asst = *)
(*   vc (GCL.(seq prog (assert_ asst))) *)

(* let qe solver simpl body c = *)
(*   let (dvs,cvs) = BExpr.vars body in *)
(*   let phi =  BExpr.forall dvs body in *)
(*   let phi = if simpl then BExpr.simplify phi else phi in *)
(*   let size = -1 in *)
(*   if BExpr.qf phi then *)
(*     let res = BExpr.to_smtlib phi in *)
(*     let dur = Clock.stop c in *)
(*     (dur, res, size, false) *)
(*   else     *)
(*     (\* let phi_str = BExpr.to_smtlib phi in *\) *)
(*     let res = solver dvs cvs phi in *)
(*     let dur = Clock.stop c in *)
(*     (dur, res, size, true) *)

(* let exp_inner stringifier runner simpl (prog, asst) = *)
(*   let c = Clock.start () in *)
(*   let body = vc prog asst in *)
(*   let solver _ cvs phi = runner (stringifier cvs (BExpr.to_smtlib phi)) in *)
(*   qe solver simpl body c *)

(* let cvc4_infer = exp_inner Smt.simplify Solver.run_cvc4 *)
(* let cvc4_check = exp_inner Smt.check_sat Solver.run_cvc4  *)
(* let z3_check = exp_inner Smt.check_sat Solver.run_z3               *)
(* let z3_infer = exp_inner Smt.assert_apply Solver.run_z3 *)
(* let princess_infer = exp_inner Smt.simplify Solver.run_princess *)

(* let cvc4_z3_infer simpl (prog, asst) = *)
(*   let (dur, res, size, use_solver) = cvc4_infer simpl (prog, asst) in *)
(*   let (dvs,cvs) = BExpr.vars (vc prog asst) in   *)
(*   if Smt.qf res then *)
(*     (dur,res,size,use_solver) *)
(*   else *)
(*     let c = Clock.start () in *)
(*     let uneliminated_dvs = List.filter dvs ~f:(fun v -> String.is_substring res ~substring:(Var.str v)) in *)
(*     let quantified_res = Printf.sprintf "(forall (%s) %s)" (Var.list_to_smtlib_quant uneliminated_dvs) res in  *)
(*     let res = Solver.run_z3 (Smt.assert_apply cvs quantified_res) in *)
(*     let z3_dur = Clock.stop c in  *)
(*     (Float.(dur + z3_dur), res, size, true) *)

(* let var_still_used smtstring var = *)
(*   String.is_substring smtstring ~substring:(Var.str var) *)

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

(* let solve solver cvs smt = solve_wto solver cvs smt      *)

(* let normalize solver dvs cvs res = *)
(*   if Smt.success res then *)
(*       match solver with *)
(*       | `Z3 | `Z3Light -> *)
(*          let goals = BExpr.to_smtlib (Solver.of_smtlib ~dvs ~cvs res) in *)
(*          if String.is_substring goals ~substring:":precision" then *)
(*            "true" *)
(*          else *)
(*            goals *)
(*       | `CVC4 -> *)
(*          let dvs' = List.filter dvs ~f:(var_still_used res) in *)
(*          if List.is_empty dvs' then *)
(*            res *)
(*          else *)
(*            Printf.sprintf "(forall (%s) %s)" (Var.list_to_smtlib_quant dvs') res *)
(*   else *)
(*     begin *)
(*       Printf.eprintf "Solver failed:\n %s" res; *)
(*       exit (-1) *)
(*     end *)

(* let rec solver_fixpoint_str gas solvers dvs cvs (smt : string) : string = *)
(*   if gas <= 0 then smt else *)
(*     let dvs' = List.filter dvs ~f:(var_still_used smt) in *)
(*     let cvs' = List.filter cvs ~f:(var_still_used smt) in *)
(*     match solvers with *)
(*     | [] -> *)
(*        failwith "Ran out of solvers to try" *)
(*     | solver :: solvers' -> *)
(*        let res = normalize solver dvs cvs' (solve solver cvs' smt) in *)
(*        if Smt.qf res then *)
(*          res *)
(*        else *)
(*          solver_fixpoint_str (gas-1) (solvers'@[solver]) dvs' cvs' res *)

(* let solver_fixpoint gas solvers dvs cvs phi = *)
(*   BExpr.to_smtlib phi *)
(*   |> solver_fixpoint_str gas solvers dvs cvs *)

(* let cvc4_z3_fix gas solvers simpl (prog, asst) = *)
(*   let c = Clock.start () in *)
(*   let body = vc prog asst in *)
(*   qe (solver_fixpoint gas solvers) simpl body c *)

let subsolving (prog, asst) =
  let c = Clock.start () in
  Log.qe "%s" @@ lazy "computing vc";
  let phi = passive_vc (GCL.(seq prog (assert_ asst))) in
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
  Log.qe "%s" @@ lazy "subsolving done";
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
  Log.qe "%s" @@ lazy ("Solve_one");
  let (dvs, _) = BExpr.vars phi in
  List.iter dvs ~f:BExpr.incr_q;
  Log.qe "%s" @@ lazy "smart constructors";
  let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in
  Log.qe "%s" @@ lazy "solver";
  let%map qf_phi = qe (solve_wto `Z3) qphi in
  Log.qe "%s" @@ lazy "getting the vars of the result";
  let dvs', cvs = BExpr.vars qf_phi in
  check_no_quantified_vars dvs phi dvs' qf_phi;
  Log.qe "%s" @@ lazy "using z3 to simplify";
  let qf_phi_str = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify qf_phi))) in
  Log.qe "%s" @@ lazy "[solve_one} done";
  (cvs, qf_phi_str)

let abstract_expressionism (solver : ?with_timeout:int -> Var.t list -> string -> string) phi : BExpr.t option =
  let rec solve_loop threshold =
    Log.debug "ABSTRACT EXPRESSIONISM %d" @@ lazy threshold;
    let phi = BExpr.abstract_expressionism ~threshold phi in
    Log.debug "%s\n" @@ lazy (BExpr.to_smtlib phi);
    let _, cvs = BExpr.vars phi in
    let res = solver ~with_timeout:2000 cvs (BExpr.to_smtlib phi) in
    if BottomUpQe.check_success res then
      Some (Solver.of_smtlib ~dvs:[] ~cvs res)
    else begin
      Log.smt "Solver failed with message:\n%s" @@ lazy res;
      if threshold <= 5 then
        None
      else begin
        Log.debug "DECREMENTING THRESHOLD: %d" @@ lazy threshold;
        solve_loop (threshold - 1)
      end
    end
  in
  solve_loop 10


let nikolaj_please (solver : ?with_timeout:int -> Var.t list -> string -> string) phi : BExpr.t option =
  Log.debug_s "Nikolaj pleaseeeeeee";
  let _, cvs = BExpr.vars phi in
  let res = solver ~with_timeout:2000 cvs (BExpr.to_smtlib phi) in
  if BottomUpQe.check_success res then
    Some (Solver.of_smtlib ~dvs:[] ~cvs res)
  else
    let () = Log.smt "Solver failed with message:\n%s" @@ lazy res in
    None


let rec orelse thunks ~input =
  match thunks with
  | [] -> None
  | thunk::more_thunks ->
    match thunk input with
    | None -> orelse more_thunks ~input
    | Some x -> Some x

module GPL_G =
  CFG.Make (struct
    module Prim = Primitives.Pipeline
    module S = GPL
  end)

module GCL_G =
  CFG.Make (struct
    module Prim = Primitives.Active
    module S = GCL
  end)

module TFG_G =
  CFG.Make (struct
    module Prim = TFG.T
    module S = TFG
  end)


module RandomStack (V : sig type t [@@deriving sexp, compare] end) =
  RandomBag.Make (struct
    type t = V.t list * V.t list
    [@@deriving sexp, compare]
  end)

module VStack (VV : sig type t [@@deriving sexp, compare] end) = struct
  type t = (VV.t list * VV.t list) Stack.t
  let create () : t = Stack.create ()
  let push (stck : t) (elt : VV.t list * VV.t list) : unit = Stack.push stck elt
  let pop (stck : t) : (VV.t list * VV.t list) option = Stack.pop stck
end

module GPLGen =
  Generator.Make
    (VStack)
    (GPL_G.V)
    (GPL_G)

module PathGenerator =
  Generator.Make
    (* (RandomStack) *)
    (VStack)
    (GCL_G.V)
    (GCL_G)

let table_path_to_string (pi : GPL_G.V.t list) : string =
  List.rev pi
  |> List.map ~f:GPL_G.V.to_string
  |> String.concat ~sep:" --> "

let handle_failure ~pi ~gpl ~gcl ~psv ~gpl_graph ~induced_graph =
  Log.path_gen "Table list:\n\t%s\n" @@ lazy (table_path_to_string pi);
  Log.irs "GPL:%s\n%!" @@ lazy (GPL.to_string gpl);
  Log.irs "GCL:%s\n%!" @@ lazy (GCL.to_string gcl);
  Log.irs "PSV:%s\n%!" @@ lazy (Psv.to_string psv);
  Log.graph_dot (GPL_G.print_graph gpl_graph) "gpl";
  Log.path_gen_dot (GPL_G.print_graph induced_graph) "induced_graph";
  raise (Failure "Found unsolveable path")

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
        let cmd = TFG_G.vertex_to_cmd vtx in
        let idx = TFG_G.V.get_id vtx in
        Printf.sprintf "{\"cmd\": \"%s\", \"idx\": %d}"
          (TFG.to_string cmd) idx
      ) |> String.concat ~sep:"," in
    let path_json = Printf.sprintf "{\"path\": [%s], \"time\":%f}\n%!" path dur in
    FileIO.append path_json ~to_:file

let implies phi1 phi2 =
  let cond = BExpr.(and_ phi1 (not_ phi2)) in
  let cvs = BExpr.vars cond |> Tuple2.uncurry (@) in
  Solver.check_unsat cvs cond
    ~timeout:(Some 2000)

let implies_model consts phi1 phi2 : Model.t option =
  Log.debug "PREMISE:\n%s\n------" @@ lazy (BExpr.to_smtlib phi1);
  Log.debug "CONSEQU:\n%s\n------" @@ lazy (BExpr.to_smtlib phi2);
  let cond = BExpr.(and_ phi1 (not_ phi2)) in
  Solver.check_sat_model consts cond
    ~timeout:(Some 2000)

let sufficient ~vc ~prog =
  let program_spec = vc prog in
  fun phi ->
  Log.debug_s "Checking sufficiency";
  implies phi program_spec

let nall_paths = ref 0

let all_paths gcl nprocs pid =
  (* Log.path_gen "all_paths call #%d" @@ (lazy !nall_paths); Breakpoint.set (!nall_paths > 0);  Int.incr nall_paths; *)
  Log.graph_s "Constructing graph";
  Log.debug "GCL program to explore:\n%s\n-------------" @@ lazy (GCL.to_string gcl);
  let gcl_graph = GCL_G.construct_graph gcl in            Log.graph_dot (GCL_G.print_graph gcl_graph) "broken_cfg";
  let gen = PathGenerator.create gcl_graph in             Log.path_gen "path-exploding the %s paths" @@ lazy (Bigint.to_string @@ PathGenerator.total_paths gen);
  (* Breakpoint.set Bigint.(one < PathGenerator.total_paths gen); *)
  let paths = ref 0 in
  let sufficient = sufficient ~vc:passive_vc ~prog:gcl in
  let rec loop phi_agg =
    let clock = Clock.start () in
    (* Log.path_gen_s "----------------looping--------------------"; *)
    match nprocs, pid with
    | Some nprocs, Some pid when Int.(pid <> !paths mod nprocs) ->
      begin match PathGenerator.get_next gen with
        | None ->
          phi_agg
        | _ ->
          (* Log.path_gen_s @@ Printf.sprintf "skipping path since %d <> %d mod %d" pid !paths nprocs; *)
          Int.incr paths;
          loop phi_agg
      end
    | _ when sufficient phi_agg ->

      Log.debug_s "sufficient!";
      phi_agg
    | _ ->
      begin match pid, nprocs with
        | Some pid, Some nprocs ->
          Log.path_gen_s @@ Printf.sprintf "running path since %d == %d mod %d" pid !paths nprocs;
        | _ -> ()
      end;
      let next_path = PathGenerator.get_next gen in
      match next_path with
      | None ->
        Log.exploder_s "inner paths done";
        phi_agg
      | Some pi ->
        (* Log.path_gen "Inner Path #%d" @@ lazy !paths; *)
        (* Log.path_gen "Paths to go %s" @@ lazy Bigint.(to_string (PathGenerator.total_paths gen -  of_int !paths)); *)
        Log.path_gen "%f" @@ lazy (Float.((Clock.stop clock * 1000.0)/ of_int !paths));
        let pi = List.rev pi in
        let gcl = List.map pi ~f:(GCL_G.vertex_to_cmd) |> GCL.sequence in
        let phi = passive_vc gcl (*|> BExpr.nnf*) in
        Log.path_gen_s "Checking whether current path is covered";
        if implies phi_agg phi
        then begin
          Log.path_gen_s "Skipped; already covered!";
          Int.incr paths;
          loop phi_agg
        end
        else
          let () =
            Log.exploder "solving path %s" @@ lazy (GCL.to_string gcl);
            (* Log.exploder "Gotta analyze:\n%s" @@ lazy (GCL.to_string gcl); *)
            (* Log.exploder "Formula is: \n%s" @@ lazy (BExpr.to_smtlib phi); *)
          in
          (* match Some ([], BExpr.true_) with *)
          match orelse ~input:phi [
              solve_one ~qe:nikolaj_please;
              (* solve_one ~qe:abstract_expressionism; *)
              solve_one ~qe:BottomUpQe.cnf_qe;
            ] with
          | None ->
            Log.error "%s" @@ lazy (GCL.to_string gcl);
            Log.error "%s" @@ lazy (BExpr.to_smtlib phi);
            failwith "Couldn't solve path"
          | Some (cvs, res) ->
            let qf_psi = Solver.of_smtlib ~dvs:[] ~cvs res in
            Log.debug "got %s" @@ lazy (BExpr.to_smtlib qf_psi);
            if not (implies qf_psi phi) then begin
              Log.error "CPF is %s" @@ lazy res;
              Log.error "PHI is %s" @@ lazy (BExpr.to_smtlib phi);
              failwith "CPF did not impliy PHI"
            end;
            if Solver.check_unsat ~timeout:(Some 1000) cvs qf_psi then begin
              Printf.eprintf "Inner path Failed %s\n%!"  (GCL.to_string gcl);
              Printf.eprintf "Formulae was %s\n%!" res;
              failwith "unsolveable"
            end else begin
              Int.incr paths;
              loop (BExpr.and_ phi_agg qf_psi)
            end
  in
  Log.path_gen_s "starting loop";
  let phi = loop BExpr.true_ in
  BExpr.simplify phi

let concolic (gcl : GCL.t) : BExpr.t =
  let _, psv = Psv.passify gcl in
  Log.debug "[concolic] Passive :\n%s" @@ lazy (Psv.to_string psv);
  let all_passive_consts = Psv.vars psv in
  let safety_condition = Psv.vc psv in
  let normal_executions = Psv.(normal (remove_asserts psv)) in
  let num_cexs = ref Bigint.zero in
  let rec loop phi_agg =
    Log.debug_s "checking implication...";
    match
      Solver.check_sat_model
        all_passive_consts
        (BExpr.ands_ [phi_agg;
                      normal_executions;
                      BExpr.not_ safety_condition])
        ~timeout:(Some 20000)
    with
    | None ->
      Log.debug_s "found a sufficiently strong formula";
      phi_agg
    | Some counterexample ->
      (* Log.path_gen_s "failed"; *)
      Bigint.incr num_cexs;
      let input_packet = Model.project_inputs counterexample in
      Log.path_gen "found counterexample no. %s" @@ lazy (Bigint.to_string !num_cexs);
      Log.debug "%s" @@ lazy Model.(to_string input_packet);
      match Concrete.slice input_packet gcl with
      | None ->
        Log.error "Failed to slice(GCL):\n%s\n----------" @@ lazy (GCL.to_string gcl);
        failwith "Could not slice the counterexample"
      | Some pi ->
        Log.debug "Slice:\n%s------/" @@ lazy (GCL.to_string pi);
        let pi = GCL.simplify_path pi in
        let pi_vc = Psv.(vc @@ snd @@ passify pi) in
        match
          orelse ~input:pi_vc
            [solve_one ~qe:nikolaj_please;
             (* solve_one ~qe:abstract_expressionism; *)
             solve_one ~qe:BottomUpQe.cnf_qe]
        with
        | None ->
          Log.error "GCL:\n%s-------\n" @@ lazy (GCL.to_string pi);
          Log.error "VC:\n%s-------\n" @@ lazy (BExpr.to_smtlib pi_vc);
          failwith "COULD NOT SOLVE PATH"
        | Some (cvs, cpf_str) ->
          let cpf = Solver.of_smtlib ~dvs:[] ~cvs cpf_str in
          let sat = Solver.check_sat cvs cpf in
          if BExpr.(cpf = true_) then begin
            Printf.printf "the following path gave true when cpfed:%s" (GCL.to_string pi);
            failwith "found false"
          end else if sat then
            loop (BExpr.and_ cpf phi_agg)
          else begin
            Log.warn "Uncontrollable path:%s" @@ lazy (GCL.to_string pi);
            failwith "unsolveable"
          end
  in
  loop BExpr.true_

(** THE MAIN LOOP *)
let search_generator ~sufficient:_ ~parserify ~statusbar gpl_graph gen phi_agg =
  let rec loop gen gpl_graph (phi_agg : BExpr.t) =
    (* if sufficient phi_agg *)
    (* then phi_agg *)
    (* else *)
      let inducer = GPL_G.induce gpl_graph in
      (* if sufficient phi_agg phi_prog then *)
      (*   phi_agg *)
      (* else *)
      let paths = ref Bigint.zero in
      match GPLGen.get_next gen with
      | None -> phi_agg
      | Some pi ->                                          Log.debug "STATUS: %s" @@ statusbar gen pi paths;
        let induced_graph = inducer pi in                   Log.path_gen_dot (GPL_G.print_graph induced_graph) "induced_graph";
        let gpl = GPL_G.to_prog induced_graph in            Log.irs "GPL:\n%s\n%!" @@ lazy (GPL.to_string gpl);
        let gcl = GPL.encode_tables gpl in                  Log.irs "GCL:\n%s\n%!" @@ lazy (GCL.to_string gcl);
        let full_gcl = parserify gcl in                     Log.irs "GCL w/ Parser (Optimized):\n%s\n%!" @@ lazy (GCL.to_string gcl);
        let psv = Psv.(passify full_gcl) |> snd in
        let phi = Psv.vc psv in
        (* if implies phi_agg phi then                         let () = Log.debug_s "\tSkipped for sufficiency!;\n%!" in *)
        (*   loop gen gpl_graph phi_agg *)
        (* else begin                                          let () = Log.debug_s "solving" in *)
          Log.path_gen_s "solving...";
          match solve_one phi ~qe:BottomUpQe.optimistic_qe with
          (* match None with *)
          | None ->
            (* concolic full_gcl *)
            all_paths full_gcl None None
            (* Log.path_gen_s "couldn't solve path!\n"; Log.irs "%s\n" @@ lazy (GCL.to_string full_gcl); *)
            (* phi_agg *)
            (* |> explode_tables ~sufficient:(Fn.flip implies phi) ~parserify (Exploder.create ()) gpl *)
            (* |> loop gen gpl_graph *)
          | Some (cvs, res) ->
            let qf_psi = Solver.of_smtlib ~dvs:[] ~cvs res in
            let sat = Solver.check_sat cvs qf_psi in
            if not sat then handle_failure
                ~pi ~gpl ~gcl ~psv
                ~gpl_graph ~induced_graph;
            Bigint.incr paths;                                Log.smt "Path condition: \n%s\n%!" @@ lazy (BExpr.to_smtlib phi);
            loop gen gpl_graph (BExpr.and_ qf_psi phi_agg)
        (* end *)
  in
  loop gen gpl_graph phi_agg

(* let table_paths ~sfreq:_ ~fn:_ ((prsr, prog) : GPL.t * GPL.t) = *)
(*   (\* Initialize the program state*\)                        Log.irs "Unoptimized GPL parser:\n%s\n" @@ lazy (GPL.to_string prsr); *)
(*   let (prsr, prog) = GPL.optimize_seq_pair (prsr, prog) in *)
(*   let gcl_prsr = GPL.encode_tables prsr in                 Log.irs "Optimized GCL parser:\n%s\n" @@ lazy (GCL.to_string gcl_prsr); *)
(*   let gpl_graph = GPL_G.construct_graph prog in              Log.graph "Constructing Graph For Optimized GPL:%s\n%!\n\n" @@ lazy (GPL.to_string prog); *)
(*   let tfg_prog = TFG.project prog in                       Log.graph "%s" @@ lazy (GPL_G.print_key gpl_graph); Log.graph_dot (GPL_G.print_graph gpl_graph) "gpl"; *)
(*   let tfg_graph = TFG_G.construct_graph tfg_prog in          Log.graph_dot (TFG_G.print_graph tfg_graph) "tfg"; *)
(*   let gen = GPLGen.create (TFG_G.cast_to_gpl_graph tfg_graph) in *)
(*   (\* let paths = ref Bigint.zero  in *\) *)
(*   (\* let parserify gcl = GCL.(optimize (seq gcl_prsr gcl)) in *\) *)
(*   let parserify gcl = *)
(*     GCL.seq gcl_prsr gcl *)
(*   in *)
(*   let clock = Clock.start () in *)
(*   let statusbar gen pi paths  = lazy ( *)
(*     let time_s = Float.(Clock.stop clock / 1000.0) in *)
(*     let tot_paths = GPLGen.total_paths gen in *)
(*     Printf.sprintf "\n %s\n" (table_path_to_string pi) *)
(*     ^ *)
(*     Printf.sprintf "[%fs] ^Path #%s\n" time_s (Bigint.to_string !paths) *)
(*     ^ *)
(*     Printf.sprintf "There are %s paths\n" (Bigint.to_string tot_paths) *)
(*     ^ *)
(*     Printf.sprintf "current rate is %f paths per second\n" (paths_per_second paths time_s) *)
(*     ^ *)
(*     Printf.sprintf "estimated time to completion: %s\n" (completion_time (Bigint.to_float tot_paths) paths time_s)) *)
(*   in *)
(*   let sufficient = *)
(*     sufficient ~vc:passive_vc ~prog:(GPL.(seq prsr prog |> encode_tables)) *)
(*   in *)
(*   search_generator ~sufficient ~parserify ~statusbar gpl_graph gen BExpr.true_ *)


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

let table_infer ~sfreq:_ ~prsr ~fn:_ gpl_pair =
  Log.qe "%s" @@ lazy "preprocessing";
  let prsr, pipe = preprocess ~prsr gpl_pair in
  let gcl_pipe = GPL.encode_tables pipe in
  let gcl_prsr = GPL.encode_tables prsr in
  Log.qe "%s" @@ lazy "sequencing";
  let gcl_prog = GCL.seq gcl_prsr gcl_pipe in
  Log.qe "%s" @@ lazy "optimizing";
  let gcl_prog = GCL.optimize gcl_prog in
  Log.qe "%s" @@ lazy "starting inference";
  (* concolic (parserify gcl_pipe) *)
  all_paths gcl_prog None None
 (* table_paths ~sfreq ~fn (prsr, pipe) *)
