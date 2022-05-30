
open Core

let rec qe (solver : ?with_timeout:int -> Var.t list -> string -> string) b : BExpr.t =
  let open BExpr in
  Log.size (size b);
  match b with
  | TTrue | TFalse | TComp _ | LVar _ -> b
  | TNot (b, _) ->
     not_ (qe solver b)
  | TBin (o, b1, b2, _) ->
     (BExpr.get_smart o) (qe solver b1) (qe solver b2)
  | Forall (x, b) ->
     let b' = qe solver b in
     (* try smart constructor over result of recursive call*)
     begin match forall [x] (nnf b') with
     | Forall (x', body) as b' when Var.equal x x' ->
        Log.size (size body);
        (* in this case, the smart constructor had no effect*)
        (* optimistically try the solver with a timeout between 1s and 10s *)
        (* this threshold should void bitblasting *)
        let vars = vars b' |> Util.uncurry (@) in
        let res = solver ~with_timeout:(min (max (size b') 1000) 10000) vars (to_smtlib b') in
        Log.print @@ lazy "checkin success";
        let b'', good_enough =
          if Smt.success res && Smt.qf res then begin
              Log.print @@ lazy res;
              let b'' = Solver.of_smtlib (* ~cvs:vars *) res in
              (b'', (size b'') < 10 * (BExpr.size b'))
            end
          else
            b', false in
        if good_enough then begin
            Log.print @@ lazy "form small enough";
            decr_q x "z3";
            b''
        end else
          let () = Log.print @@ lazy (Printf.sprintf "form too big: %d" (size b''))  in
           (* In this case, the solver timed out, so lets try to do something smarter *)
          let body = if qf body (*&& size body < 500 *)
                      then cnf (body) (* if the formula isn't too big, cnf it*)
                      else body in
           (* now run the smart constructors again *)
           begin match forall [x'] body |> simplify with
           | Forall (x'', body) as phi when Var.equal x' x'' ->
              Log.size (size body);
              (*If it had no effect, we are out of things to try*)
              if Solver.check_unsat vars phi then begin
                (* unsat formulae are = to false *)
                decr_q x "z3";
                false_
              end else
                (* finally, as a last resort, run the solver with no timeout *)
                let res = solver vars (to_smtlib phi) in
                decr_q x "z3";
                Log.print @@ lazy res;
                Solver.of_smtlib (*~cvs:vars*) res
           | b'' ->
              Log.size (size b'');
              if qf b'' then begin
                  b''
                end
              else qe solver b''
           end
     | b' ->
        Log.size (size b');
        if qf b' then begin
            b'
          end
        else qe solver b'
     end
  | Exists _ ->
     failwith "not sure how to handle exists"
