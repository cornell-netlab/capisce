open Core

type t = Id of (string)
       | Let of t list * t
       | Forall of t list * t
       | Exists of t list * t
       | Fun of t * t list
       | BV of (Bigint.t * int) 
       [@@deriving eq, sexp, compare, quickcheck]     

module Ctx = Map.Make (String) 

             
let to_sexp_string s =
  [%sexp_of: t list] s
  |> Sexp.to_string

let add_sort x e =
  match e with
  | Fun (Id "_", [Id "BitVec"; Id n]) ->
     Var.make x (int_of_string n)
  | Id "Bool" ->
     failwith "Not sure how to translate boolean sorts"
  | _ -> failwith "unrecognized sort" 
     
  
let rec to_vars (gamma : Var.t Ctx.t) (bound : t list) =
  match bound with
  | [] -> gamma, []
  | Fun (Id x_name, [sort]) :: rst ->
     let x = add_sort x_name sort in
     let gamma = Ctx.set gamma ~key:x_name ~data:x in
     let gamma, vars = to_vars gamma rst in
     gamma, x::vars 
  | _ ->
     failwith "malformed sort"

let rec to_expr gamma b : Expr.t =
  match b with
  | Id x ->
     begin match Ctx.find gamma x with
     | None -> failwith (x ^ " was missing from expression context")
     | Some x ->
        Expr.var x
     end
  | Fun (Id "bvnot", [e]) ->
     Expr.bnot (to_expr gamma e)
  | Fun (Id "_", [Id bv; Id size]) ->
     Expr.bv (Bigint.of_string (String.chop_prefix_exn bv ~prefix:"bv")) (Bigint.of_string size |> Bigint.to_int_exn)
  | Fun (Id f, [e1; e2]) ->
     let e1 = to_expr gamma e1 in
     let e2 = to_expr gamma e2 in
     begin match f with
     | "bvor"  -> Expr.bor e1 e2
     | "bvand" -> Expr.band e1 e2
     | "bvxor" -> Expr.bxor e1 e2
     | "bvadd" -> Expr.badd e1 e2
     | "bvmul" -> Expr.bmul e1 e2
     | "bvsub" -> Expr.bsub e1 e2
     | "concat" -> Expr.bconcat e1 e2
     | "bvshl" -> Expr.shl_ e1 e2
     | "bvashr" -> Expr.ashr_ e1 e2
     | "bvlshr" -> Expr.lshr_ e1 e2
     | _ ->
        failwith ("unrecognized binary function " ^ f)
     end
  | Fun (Id f, args) ->
     failwith (Printf.sprintf "[expr] gotta support %s over %d args" f (List.length args))
  | Fun _ ->
     failwith ("unrecognized function")
  | BV (v, w) -> Expr.bv v w
  | Forall _ | Exists _ ->
     failwith "quantifier are not expressions"
  | Let _ ->
     failwith "let bindings are not expressions"
     
    
let rec translate_assignments gamma bindings assignments =
  match assignments with
  | [] -> bindings        
  | Fun (Id var, [bexpr_smt])::rst ->
     let bexpr = to_bexpr_inner gamma bindings bexpr_smt in
     let bindings =  Ctx.set bindings ~key:var ~data:bexpr in
     translate_assignments gamma bindings rst
  | _ ->
    failwith "malformed let-binding"
and to_bexpr_inner (gamma : Var.t Ctx.t) (bindings : BExpr.t Ctx.t ) b =
  match b with
  | Id "false" ->
     BExpr.false_
  | Id "true" ->
     BExpr.true_
  | Id x ->
     begin match Ctx.find bindings x with
     | None ->
        failwith ("tried to look up " ^ x ^ " in boolean context, but couldn't find it")
     | Some b ->
        b
     end
  | Forall (bound_ids, exp) ->
     let gamma, vars = to_vars gamma bound_ids in
     BExpr.forall vars (to_bexpr_inner gamma bindings exp)
  | Exists (bound_ids, exp) ->
     let gamma, vars = to_vars gamma bound_ids in
     BExpr.exists vars (to_bexpr_inner gamma bindings exp )
  | Let (assignments, body) ->
     let bindings = translate_assignments gamma bindings assignments in
     to_bexpr_inner gamma bindings body
  | Fun (Id f, args) ->
     begin match f, args with
     | "goals", [Fun (Id "goal", goals) ] ->
        List.map goals ~f:(to_bexpr_inner gamma bindings) |> BExpr.ands_
     | "not", [a] ->
        BExpr.not_ (to_bexpr_inner gamma bindings a)
     | "and",_ ->
        List.map args ~f:(to_bexpr_inner gamma bindings) |> BExpr.ands_
     | "or", _->
        List.map args ~f:(to_bexpr_inner gamma bindings)  |> BExpr.ors_
     | "=>", _->
        List.map args ~f:(to_bexpr_inner gamma bindings) |> BExpr.imps_
     | "=", [a; b] ->
        begin try
            let a_bool = to_bexpr_inner gamma bindings a in
            let b_bool = to_bexpr_inner gamma bindings b in
            BExpr.iff_ a_bool b_bool
          with
          | Failure msg ->
             Log.print @@ lazy (Printf.sprintf "Warning: %s" msg);
             let a_expr = to_expr gamma a in
             let b_expr = to_expr gamma b in
             BExpr.eq_ a_expr b_expr
        end        
     | "bvule", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.ule_ e1 e2
     | "bvult", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.ult_ e1 e2
     | "bvugt", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.ugt_ e1 e2
     | "bvuge", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.uge_ e1 e2
     | "bvsle", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.sle_ e1 e2
     | "bvslt", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.slt_ e1 e2
     | "bvsgt", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.sgt_ e1 e2
     | "bvsge", [e1; e2] ->
        let e1 = to_expr gamma e1 in
        let e2 = to_expr gamma e2 in
        BExpr.sge_ e1 e2
     | "=", _ | "bvule", _ | "bvult", _ | "bvuge", _ | "bvsle", _ |
       "bvslt", _ | "bvsgt", _ | "bvsge", _ ->
        failwith (Printf.sprintf "Gotta support %s over %d terms" f (List.length args))
        
     | _,_ ->
        failwith ("unrecognized boolean function: " ^ f)
     end
  | BV (_, _) ->
     failwith "got bitvector when converting to boolean expression:("
  | _ ->
     failwith "unrecognized expression"
    
let rec to_bexpr_aggregate gamma smts =
  match smts with
  | [] -> failwith "need at least one"
  | [smt] ->
     begin try to_bexpr_inner gamma Ctx.empty smt with
     | Failure msg ->
        failwith (Printf.sprintf "Example:\n%s\nTriggered failure: %s%!" ([%sexp_of: t] smt |> Sexp.to_string) msg)
     end
  | Fun(Id "declare-const", (Id x :: sort))::smts ->
     let gamma,_ = to_vars gamma [Fun (Id x, sort)] in
     to_bexpr_aggregate gamma smts
  | _ ->
     failwith "unrecognized bexpr"

let to_bexpr = to_bexpr_aggregate Ctx.empty    

  
let to_string _ = failwith "" (* function
   * | Id string -> string
   * | App ts ->
   *    let strings = List.map ~f:to_string ts in     
   *    Printf.sprintf "(%s)" (String.concat ~sep:" " strings) *)
  
let list_to_string _ = failwith ""
  (* List.map ts ~f:to_string
   * |> String.concat ~sep:"\n" *)


