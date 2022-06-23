open Core

let models _ _ (* model phi *) =
  failwith "implement"

let check_sat _ (* phi *) =
  failwith "implement"

let project _ _ (* m2 vars*) =
  (* dualize; call smt; and negate *)
  failwith "implement"

let check_sat_model _ _ (*vars phi*) : (Bigint.t * int)  String.Map.t option =
  failwith "implement"
    
let setminus g psi = BExpr.(and_ g (not_ psi))

    
   
(* assume model ⊧ phi *)
(* generalize1 *)
let widen model phi =
  List.map (BExpr.get_atoms phi)
    ~f:(fun atom ->
      if models model atom then
        atom
      else
        BExpr.not_ atom
    )

(* assume ⊧ ¬ (g ∧ generalization) *)
(* generalize2 *)
let narrow g m =
  List.filter m
    ~f:(fun conjunct -> 
      check_sat (setminus g conjunct::m)
    )


let exist_elim vars phi =
  (*For each generalized model, *)
  let rec loop h o =
    match check_sat_model vars h with
    | None ->
       (h, o)
    | Some model ->
       let m1 = widen model phi in
       let m2 = narrow (BExpr.not_ phi) m1 in
       let pi = project m2 vars in             (* pi = exists vars m2  *)
       loop
         (*h = *)(BExpr.(and_ h (not_ pi))) 
         (*o = *)(BExpr.(or_ o pi))
  in
  loop phi BExpr.false_
  
  
