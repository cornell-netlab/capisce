open Core
open ASTs

let solver_to_string = function
  | `Z3 -> "z3"
  | `CVC4 -> "CVC4"
  | `Princess -> "Princess"

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
  | `Princess, _ ->
    Solver.run_princess (Smt.simplify cvs smt)

let dp_removed phi =
  let dvs, _ = BExpr.vars phi in
  List.is_empty dvs && BExpr.qf phi 

let z3_simplify cvs phi = Solver.run_z3 (Smt.simplify cvs (BExpr.to_smtlib (BExpr.simplify phi)))

let solve_one ?(solver=`Z3) ~qe phi : (BExpr.t, BExpr.t) Result.t =
  let open Result.Let_syntax in
  Log.qe "solve_one(%s)" @@ lazy (solver_to_string solver);
  let (dvs, _) = BExpr.vars phi in
  List.iter dvs ~f:BExpr.incr_q;
  (* let qphi = BExpr.(forall dvs phi |> order_all_quantifiers) in *)
  let qphi = BExpr.(forall dvs phi) in
  let%bind qf_phi = qe (solve_wto solver) qphi in
  if dp_removed qf_phi then
    Result.Ok qf_phi
  else
    Result.Error qf_phi

let solve_one_option ?(solver=`Z3) ~qe phi =
  solve_one ~solver ~qe phi
  |> Result.ok

let nikolaj_please (solver : ?with_timeout:int -> Var.t list -> string -> string) phi : (BExpr.t, BExpr.t) Result.t =
  Log.qe_s "Nikolaj pleaseeeeeee";
  let _, cvs = BExpr.vars phi in
  let res = solver ~with_timeout:2000 cvs (BExpr.to_smtlib phi) in
  if BottomUpQe.check_success res then
    let phi' = Solver.of_smtlib ~dvs:[] ~cvs res in
    if BExpr.qf phi' then
      Result.Ok phi'
    else 
      Result.Error phi
  else
    let () = Log.smt "Solver failed with message:\n%s" @@ lazy res in
    if String.is_substring res ~substring:"canceled" then
      Result.Error phi
    else
      let partial_fee = Solver.of_smtlib ~dvs:[] ~cvs res in
      Result.Error partial_fee

let rec and_then tactics input =
  match tactics with
  | [] -> None
  | tactic::more_tactics ->
    match tactic input with
    | Result.Ok result -> Some result
    | Result.Error bad_result ->
      and_then more_tactics bad_result

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

let hybrid_strategy vc = 
  orelse ~input:vc
  [
    and_then [
      solve_one ~solver:`Z3 ~qe:(nikolaj_please);
      solve_one ~solver:`Princess ~qe:(nikolaj_please);
      solve_one ~solver:`Z3 ~qe:(nikolaj_please);
    ];
   (* solve_one_option ~solver:`Princess ~qe:BottomUpQe.cnf_qe_result; *)
   ]

let check_sufficiency gcl =
  let _, psv = Psv.passify gcl in
  Log.debug "[concolic] Passive :\n%s" @@ lazy (Psv.to_string psv);
  let all_passive_consts = Psv.vars psv in
  let safety_condition = Psv.vc psv in
  let normal_executions = Psv.(normal (remove_asserts psv)) in
  fun condition ->
    BExpr.ands_ [ 
      condition;
      normal_executions;
      BExpr.not_ safety_condition
    ]
    |> Solver.check_sat_model 
      ~timeout:(Some 20000)
      all_passive_consts

let path_generator gcl =
  let suffices = check_sufficiency gcl in
  fun condition ->
    match suffices condition with
    | None ->
      Log.debug_s "found a sufficiently strong formula";
      None
    | Some counterexample ->
      let input_packet = Model.project_inputs counterexample in
      Log.debug "%s" @@ lazy Model.(to_string input_packet);
      match Concrete.slice input_packet gcl with
      | None ->
        Log.error "Failed to slice(GCL):\n%s\n----------" @@ lazy (GCL.to_string gcl);
        failwith "Could not slice the counterexample"
      | Some pi -> Some pi
      

let mono (gcl : GCL.t) : BExpr.t = 
  let phi = Psv.(vc @@ snd @@ passify gcl) in 
  match solve_one ~solver:`Z3 ~qe:(nikolaj_please) phi with 
  | Error _ -> 
    failwith "Monolithic Solver Failed"
  | Ok cpi -> 
    if not (BExpr.qf cpi) then failwith "result was still quantified";
    cpi


let num_cexs = ref Bigint.zero
let data = ref []

let concolic (gcl : GCL.t) : BExpr.t =
  let get_new_path = path_generator gcl in
  num_cexs := Bigint.zero;
  data := [Clock.now (), BExpr.true_];
  let rec loop phi_agg =
    Log.debug_s "checking implication...";
    match get_new_path phi_agg with
    | None -> 
      (* TERMINATION *)
      phi_agg
    | Some unsolved_path ->
      Bigint.incr num_cexs;
      Log.qe "found counterexample number %s" @@ lazy (Bigint.to_string !num_cexs);
      let simplified_unsolved_path = GCL.simplify_path unsolved_path in
      let path_condition = Psv.(vc @@ snd @@ passify simplified_unsolved_path) in
      match hybrid_strategy path_condition with
        | None ->
          Log.error "GCL:\n%s-------\n" @@ lazy (GCL.to_string unsolved_path);
          Log.error "VC:\n%s-------\n" @@ lazy (BExpr.to_smtlib path_condition);
          failwith "SOLVERS COULD NOT SOLVE PATH"
        | Some control_plane_of_path ->
          data := !data @ [Clock.now (), control_plane_of_path];
          if not (BExpr.qf control_plane_of_path) then failwith "result was still quantified";
          let cvs = snd @@ BExpr.vars control_plane_of_path in
          Log.path_gen "%s" @@ lazy (Var.list_to_smtlib_decls cvs);
          Log.path_gen "%s" @@ lazy (BExpr.to_smtlib control_plane_of_path);
          let sat = Solver.check_sat cvs control_plane_of_path in
          if BExpr.(control_plane_of_path = true_) then begin
            Printf.printf "the following path gave true when cpfed:\n%s\n%!" (GCL.to_string unsolved_path);
            failwith "found false"
          end else if sat then

            loop (BExpr.and_ control_plane_of_path phi_agg)
          else begin
            Log.warn "Uncontrollable path:%s" @@ lazy (GCL.to_string unsolved_path);
            failwith "unsolveable"
          end
  in
  loop BExpr.true_

  let replay data gcl : (Float.t * int) list =
    let paths = GCL.all_paths gcl in
    let _, data = 
    List.fold data ~init:(paths, []) ~f:(fun (unsolved, completion_data) (t, psi) -> 
        Printf.printf "Replaying data from time %f\n%!" t;
        let remain_unsolved = List.filter unsolved ~f:(fun pi -> Option.is_some (check_sufficiency pi psi)) in 
        let num_paths_solved = List.length unsolved - List.length remain_unsolved in 
        (remain_unsolved, completion_data @ [t, num_paths_solved])
      ) in 
    data

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
            match hybrid_strategy phi with
            | None ->
              Log.error "%s" @@ lazy (GCL.to_string gcl);
              Log.error "%s" @@ lazy (BExpr.to_smtlib phi);
              failwith "Couldn't solve path"
            | Some qf_psi ->
              Log.debug "got %s" @@ lazy (BExpr.to_smtlib qf_psi);
              if not (implies qf_psi phi) then begin
                Log.error "CPF is %s" @@ lazy (BExpr.to_smtlib qf_psi);
                Log.error "PHI is %s" @@ lazy (BExpr.to_smtlib phi);
                failwith "CPF did not impliy PHI"
              end;
              let cvs = BExpr.vars qf_psi |> snd in
              if Solver.check_unsat ~timeout:(Some 1000) cvs qf_psi then begin
                Printf.eprintf "Inner path Failed %s\n%!"  (GCL.to_string gcl);
                Printf.eprintf "Formulae was %s\n%!" @@ BExpr.to_smtlib qf_psi;
                failwith "unsolveable"
              end else begin
                Int.incr paths;
                loop (BExpr.and_ phi_agg qf_psi)
              end
    in
    Log.path_gen_s "starting loop";
    let phi = loop BExpr.true_ in
    BExpr.simplify phi  

let check_for_parser prsr gpl_prsr =
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
