open Core

let break = false

let check_success result_string =
  Smt.success result_string && Smt.qf result_string

let is_small_enough old new_ =
  Log.qe "%s" @@ lazy "is the formula small enough?";
  match new_ with
  | Some new_ -> 
     let open BExpr in
     Log.qe "was size %d" @@ lazy (size old);
     Log.qe "now size %d" @@ lazy (size new_);
     let goodness = (size new_) < 10 * (size old) in
     if not goodness then Log.qe "form too big: %d" @@ lazy (size new_);
     (new_, goodness)
  | None ->
     (BExpr.false_, false)

let timeout_solver (solver : ?with_timeout:int -> Var.t list -> string -> string) vars phi =
  let phi_str =
    let avars = BExpr.abstract_qvars phi in
    let phi_str = BExpr.to_smtlib phi in
    if String.length avars > 6 then
      Printf.sprintf "(forall (%s) %s)" avars phi_str
    else
      phi_str
  in
  (* optimistically try the solver with a timeout between 1s and 10s *)
  (* this threshold should void bitblasting *)
  (* solver ~with_timeout:(min (max (BExpr.size phi) 1000) 20000) vars phi_str *)
  solver ~with_timeout:2000 vars phi_str

let unrestricted_solver (solver : ?with_timeout:int -> Var.t list -> string -> string) cvs x phi =
  let open BExpr in
  if Solver.check_unsat cvs phi then begin
    (* unsat formulae are = to false *)
    decr_q x "z3-unsat";
    false_
    end
  else   
    let res = solver cvs (to_smtlib phi) in
    decr_q x @@ Printf.sprintf "z3,%d" (size phi);
    Log.smt "%s" @@ lazy res;
    Solver.of_smtlib ~dvs:[] ~cvs res

  
let try_cnfing body : BExpr.t =
  if BExpr.qf body
  then begin
      Log.qe "%s" @@ lazy "cnfing";
      BExpr.cnf body (* if the formula isn't too big, cnf it*)
    end
  else body

  
let rec cnf_qe (solver : ?with_timeout:int -> Var.t list -> string -> string)  b : BExpr.t option =
  let open Option.Let_syntax in
  let open BExpr in
  (* Log.size (size b); *)
  match b with
  | TTrue | TFalse | TComp _ | LVar _ -> Some b
  | TNot (b) ->
    Option.map ~f:not_ (cnf_qe solver b)
  | TNary (o, bs) ->
     Util.option_map bs ~f:(cnf_qe solver)
     >>| BExpr.get_smarts o
  | Forall (x, b) ->
     let%bind b' = cnf_qe solver b in
     let vars = BExpr.vars b' |> Util.uncurry (@) in
     (* try smart constructor over result of recursive call*)
     (* do I need to do NNF here? *)
     (* could you do nnf in the smart constrction *) 
     begin match forall [x] (nnf b') with
     | Forall (x', body) as b' when Var.equal x x' ->
        (* Log.size (size body); *)
        (* in this case, the smart constructor had no effect*)        
        (* we'll heuristically describe three strategies *)
        (* First, the raw solver with a timeout *)
        (* let b' = BExpr.complete_predicate_abstraction x body |> Option.value ~default:b'  in *)
        let res = timeout_solver solver vars b' in
        let ok = check_success res in
        let b'' = if ok then Some (Solver.of_smtlib ~dvs:[] ~cvs:vars res) else None in
        let b'', ok = is_small_enough b b'' in
        if ok then begin
            Log.qe "%s" @@ lazy "form small enough";
            decr_q x @@ Printf.sprintf "z3,%d" (size b');
            Some b''
          end
        else begin (* TRY CNFING *)
            Log.qe "trying to cnf something of size %d" @@ lazy (BExpr.size body);
            Log.qe "%s" @@ lazy (Smt.assert_apply vars (BExpr.to_smtlib b'));
            let body = try_cnfing body in
            if size body >= size b'' then
              (*if cnfing only made it worse, use the original z3-provided response*)
              Some b''
            else
            begin match BExpr.forall [x'] body |> simplify with
            | Forall (x'', _) as phi when Var.equal x' x'' ->
               (* Log.size (size body); *)
               (*If it had no effect, we are out of things to try*)               
               Some (unrestricted_solver solver vars x phi)
            | b'' ->
               (* Log.size (size b''); *)
               if qf b'' then
                 Some b''
               else cnf_qe solver b''
            end
          end
     | b' ->
        (* Log.size (size b'); *)
        if qf b' then
          Some b'
        else cnf_qe solver b'
     end
  | Exists _ ->
     failwith "not sure how to handle exists"

let rec optimistic_qe (solver : ?with_timeout:int -> Var.t list -> string -> string) b : BExpr.t option =
  let open Option.Let_syntax in
  let open BExpr in
  (* Log.size (size b); *)
  match b with
  | TTrue | TFalse | TComp _ | LVar _ -> Some b
  | TNot (b) ->
     let%map b = optimistic_qe solver b in
     not_ b
  | TNary (o, bs) ->
    Util.option_map bs ~f:(optimistic_qe solver)
    >>| BExpr.get_smarts o
  | Exists _ ->
    failwith "not sure how to handle exists"
  | Forall (x, b) ->
     let%bind b' = optimistic_qe solver b in
     let vars = BExpr.vars b' |> Util.uncurry (@) in
     (* try smart constructor over result of recursive call*)
     (* do I need to do NNF here? *)
     (* could you do nnf in the smart constrction *)
     begin match forall [x] (nnf b') with
     | Forall (x', _) as b' when Var.equal x x' ->
       (* in this case, the smart constructor had no effect*)
       let res = timeout_solver solver vars b' in
       if check_success res then
         Some (Solver.of_smtlib ~dvs:[] ~cvs:vars res)
       else
         let () = Log.smt "Solver failed with message %s" @@ lazy res in
         None
     | b -> optimistic_qe solver b
     end
