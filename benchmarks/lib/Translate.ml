open Poulet4   
open GCL
open GCL (* Annoying. Can we fix this? *)
open ToGCL       

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
   
(* Coq target to Cmd *)
let rec gcl_to_cmd (t : target) : Cmd.t =
  match t with
  | GSkip ->
     Cmd.skip
  | GAssign (typ, var, bv) ->
     begin match width_of_type var typ with
     | Error s -> failwith s
     | Ok i -> Cmd.assign (Var.make var i) (bv_to_expr bv)
     end
  | GSeq (g1,g2) ->
     Cmd.seq (gcl_to_cmd g1) (gcl_to_cmd g2) 
  | GChoice (g1,g2) ->
     let c1 = gcl_to_cmd g1 in
     let c2 = gcl_to_cmd g2 in
     Cmd.choice c1 c2
  | GAssume phi ->
     Cmd.assume (form_to_bexpr phi)
  | GAssert phi ->
     Cmd.assert_ (form_to_bexpr phi)
  | GExternVoid ("assert",[phi]) ->
     Cmd.assert_ (BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1)) 
  | GExternVoid _ | GExternAssn _ ->
     failwith "Externs should have been eliminated"
 
