open Poulet4
open GCL
open GCL (* Annoying. Can we fix this? *)
open ToGCL
open Primitives
open ASTs

open Core

let bv_bop (b : BitVec.bop) : Expr.t -> Expr.t -> Expr.t =
  match b with
  | BVPlus (sat, _) ->
     if sat then
       Printf.eprintf "[WARNING] unsoundly implementing saturating addition (|+|) as overflowing addition (+)\n%!";
     (* unsigned and signed are the same ??? *)
     Expr.badd
  | BVMinus (sat, _) ->
     if sat then
       Printf.eprintf "[WARNING] unsoundly implementing saturating subtraction (|-|) as overflowing subtraction (-)\n%!";
     (* signed and unsigned are the same ??? *)
     Expr.bsub
  | BVTimes _ ->
     (* signed and unsigned are the same ??? *)
     Expr.bmul
  | BVConcat ->
     Expr.bconcat
  | BVShl _ ->
     Expr.shl_
  | BVShr signed ->
     if signed then
       Expr.ashr_
     else
       Expr.lshr_
  | BVAnd ->
     Expr.band
  | BVOr ->
     Expr.bor
  | BVXor ->
     Expr.bxor
  
let bv_unop (unop : BitVec.uop) : Expr.t -> Expr.t =
  match unop with
  | BVNeg ->
     Expr.bnot
  | BVCast w ->
     Expr.bcast w
  | BVSlice (hi, lo) ->
     Expr.bslice lo hi
    
(* Coq BitVec -> Expr *)
let rec bv_to_expr (bv : BitVec.t) : Expr.t =
  match bv with
  | BitVec (n, opt_width) ->
     begin match opt_width with
     | None ->
        failwith "Cannot support arbitrary-width bitvectors"
     | Some w ->
        Expr.bvi n w
     end
  | Int (n, opt_width) ->
     begin match opt_width with
     | None ->
        failwith "Cannot support arbitrary-width integers"
     | Some w ->
        let pow2 = Bigint.(pow (of_int 2)) in        
        if Bigint.(n < zero) then
          (* TODO Check this *)
          let n = Bigint.((abs n) % (pow2 (of_int w - one))) in
          Expr.(badd (bnot (bv (Bigint.abs n) w)) (bvi 1 w))
        else
          Expr.bv Bigint.(n % pow2 (of_int w)) w
     end
  | BVVar (x, i) ->
     Expr.var (Var.make x i)
  | BinOp (op, lhs, rhs) ->
     bv_bop op (bv_to_expr lhs) (bv_to_expr rhs)
  | UnOp (op, arg) ->
     bv_unop op (bv_to_expr arg)


let logical_operator (op : Form.lbop) : BExpr.t -> BExpr.t -> BExpr.t =
  match op with
  | LOr -> BExpr.or_
  | LAnd -> BExpr.and_
  | LImp -> BExpr.imp_
  | LIff -> BExpr.iff_

let comparison (lcomp : Form.lcomp) : Expr.t -> Expr.t -> BExpr.t =
  match lcomp with
  | LEq -> BExpr.eq_ 
  | LNeq -> fun e1 e2 -> BExpr.not_ (BExpr.eq_ e1 e2)
  | LLt signed -> if signed then BExpr.slt_ else BExpr.ult_
  | LGt signed -> if signed then BExpr.sgt_ else BExpr.ugt_
  | LLe signed -> if signed then BExpr.sle_ else BExpr.ule_
  | LGe signed -> if signed then BExpr.sge_ else BExpr.uge_
          
let rec form_to_bexpr (phi : Form.t) : BExpr.t =
  match phi with
  | LBool (b) ->
     if b then BExpr.true_ else BExpr.false_
  | LBop (op, lhs, rhs) ->
     logical_operator op
       (form_to_bexpr lhs)
       (form_to_bexpr rhs)
  | LNot (arg) ->
     BExpr.not_ (form_to_bexpr arg)
  | LVar s ->
     BExpr.eq_ (Expr.var (Var.make s 1)) (Expr.bvi 1 1)
  | LComp (c, bv1, bv2) ->
     comparison c (bv_to_expr bv1) (bv_to_expr bv2)

let make_var typ var =
  match width_of_type var typ with
  | Error s -> failwith s
  | Ok i ->
    Var.make var i

(* Coq target to Cmd *)
let rec gcl_to_cmd (t : target) : GCL.t =
  let open GCL in
  match t with
  | GSkip ->
     skip
  | GAssign (typ, var, bv) ->
    assign (make_var typ var) (bv_to_expr bv)
  | GSeq (g1,g2) ->
     seq (gcl_to_cmd g1) (gcl_to_cmd g2)
  | GChoice (g1,g2) ->
     let c1 = gcl_to_cmd g1 in
     let c2 = gcl_to_cmd g2 in
     choice c1 c2
  | GAssume phi ->
     assume (form_to_bexpr phi)
  | GAssert phi ->
     assert_ (form_to_bexpr phi)
  | GExternVoid ("assert",[phi]) ->
     assert_ (BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1))
  | GExternVoid _ | GExternAssn _ ->
     failwith "Externs should have been eliminated"
  | GTable (tbl,_,_) ->
    failwithf "Table %s was not eliminated" tbl ()

let make_act table (act_name, act) : Var.t list * (Action.t list) =
  let prefix = Printf.sprintf "_symb$%s$%s$arg$" table act_name in
  let rename x = String.chop_prefix x ~prefix in
  let hole_mapping vars = let open List.Let_syntax in
    let%bind full_var = vars in
    match String.chop_prefix (Var.str full_var) ~prefix with
    | Some chopped_var ->
      return (full_var, Var.rename full_var chopped_var)
    | None -> []
  in
  let parameterize phi =
    let (_, cvs) = BExpr.vars phi in
    let curr_act_holes = hole_mapping cvs in
    let phi = List.fold curr_act_holes ~init:phi ~f:(fun phi (old,new_) -> BExpr.subst old (Expr.var new_) phi) in
    let params = List.map curr_act_holes ~f:snd in
    params, phi
  in
  let rec loop params (act : Action.t list) prog : Var.t list * (Action.t list) =
    match prog with
    | GSkip -> (params, act)
    | GSeq (a1,a2) ->
      let params, act = loop params act a1 in
      loop params act a2
    | GAssign (typ, var, bv) -> begin
      match rename var with
      | Some var ->
        let x = make_var typ var in
        params@[x],
        act@[Action.assign x (bv_to_expr bv)]
      | None ->
        let x = make_var typ var in
        (params,
         act@[Action.assign x (bv_to_expr bv)])
    end
    | GAssert phi ->
      let phi = form_to_bexpr phi in
      let params', phi = parameterize phi in
      params @ params', [Action.assert_ phi]
    | GExternVoid ("assert",[phi]) ->
      let phi = BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1) in
      let params', phi = parameterize phi in
      params@params', [Action.assert_ phi]
    | GAssume _ ->
      failwith "actions cannot contain assume"
    | GChoice _ ->
      let gcl = gcl_to_cmd prog in
      failwithf "actions cannot contain choice, in action %s.%s: %s\n" table act_name (GCL.to_string gcl) ()
    | GTable _ ->
      failwith "actions cannot contain table"
    | GExternAssn _
    | GExternVoid _ ->
      failwith "externs should be factored out of actions"
  in
  loop [] [] act
  |> Tuple.T2.map_fst ~f:(List.dedup_and_sort ~compare:Var.compare)


(* Coq target to GPL *)
let rec gcl_to_gpl (t : target) : GPL.t =
  match t with
  | GSkip ->
    GPL.skip
  | GAssign (typ, var, bv)  ->
    GPL.assign (make_var typ var) (bv_to_expr bv)
  | GSeq (g1,g2) ->
    GPL.seq (gcl_to_gpl g1) (gcl_to_gpl g2)
  | GChoice (g1,g2) ->
    let c1 = gcl_to_gpl g1 in
    let c2 = gcl_to_gpl g2 in
    GPL.choice c1 c2
  | GAssume phi ->
    GPL.assume (form_to_bexpr phi)
  | GAssert phi ->
    GPL.assert_ (form_to_bexpr phi)
  | GExternVoid ("assert",[phi]) ->
    GPL.assert_ (BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1))
  | GTable (table, keys, actions) ->
    let keys = List.map keys ~f:(fun (k,_) -> bv_to_expr k |> Expr.get_var) in
    let actions = List.map actions ~f:(make_act table) in
    GPL.table table keys actions
  | GExternAssn _
  | GExternVoid _ ->
    failwith "Externs should have been eliminated"
