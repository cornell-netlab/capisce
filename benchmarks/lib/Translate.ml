open Poulet4
open GCL
open GCL (* Annoying. Can we fix this? *)
open ToGCL
open Primitives
open ASTs
open DependentTypeChecker

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
  match width_of_type typ with
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
  | GExternVoid ("assert",[Datatypes.Coq_inr phi]) ->
     assert_ (BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1))
  | GExternVoid _ | GExternAssn _ ->
     failwith "Externs should have been eliminated"
  | GTable (tbl,_,_) ->
    failwithf "Table %s was not eliminated" tbl ()

let make_act table (act_name, (params, act)) : Var.t list * (Action.t list) =
  (* let prefix = Printf.sprintf "_symb$%s$%s$arg$" table act_name in *)
  (* let rename x = String.chop_prefix x ~prefix in *)
  (* let hole_mapping vars = let open List.Let_syntax in *)
  (*   let%bind full_var = vars in *)
  (*   match String.chop_prefix (Var.str full_var) ~prefix with *)
  (*   | Some chopped_var -> *)
  (*     return (full_var, Var.rename full_var chopped_var) *)
  (*   | None -> [] *)
  (* in *)
  (* let parameterize phi = *)
  (*   let (_, cvs) = BExpr.vars phi in *)
  (*   let curr_act_holes = hole_mapping cvs in *)
  (*   let phi = List.fold curr_act_holes ~init:phi ~f:(fun phi (old,new_) -> BExpr.subst old (Expr.var new_) phi) in *)
  (*   let params = List.map curr_act_holes ~f:snd in *)
  (*   params, phi *)
  (* in *)
  let get_var = function
    | BitVec.BVVar (x, sz) -> Var.make x sz
    | _ -> failwith "action parameters must be variables, got something else"
  in
  let rec loop (act : Action.t list) prog : Action.t list =
    match prog with
    | GSkip -> act
    | GSeq (a1,a2) ->
      let act = loop act a1 in
      loop act a2
    | GAssign (t, x, bv) ->
      act@[Action.assign (make_var t x) (bv_to_expr bv)]
    | GAssert phi ->
      act@[Action.assert_ (form_to_bexpr phi)]
    | GExternVoid ("assert", [Datatypes.Coq_inr phi]) ->
      let phi = BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1) in
      act@[Action.assert_ phi]
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
  let act = loop [] act in
  let params = List.map ~f:get_var params in
  (params, act)


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
  | GExternVoid ("assert",[Datatypes.Coq_inr phi]) ->
    GPL.assert_ (BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1))
  | GTable (table, keys, actions) ->
    let keys = List.map keys ~f:(fun (k,_) -> bv_to_expr k |> Expr.get_var) in
    let actions = List.map actions ~f:(make_act table) in
    GPL.table table keys actions
  | GExternAssn (_,s,_)
  | GExternVoid (s,_) ->
    Log.warn "Extern %s unrecognized, being replaced with skip" @@ lazy s;
    GPL.skip

module DyckHoareStack = struct
  type elt = {idx : int;
              pre : BExpr.t;
              cmd : HoareNet.t;
             } [@@deriving eq]
  type t = elt list [@@deriving eq]

  let push (stk : t) (idx, pre, cmd) : t =
    {idx; pre; cmd} :: stk

  let init =
    push [] (-1, BExpr.true_, HoareNet.skip)


  let is_empty : t -> bool = function
    | [] -> false
    | _  -> true

  let pop (stck : t) : elt * t =
    match stck with
    | [] ->
      failwith "[DyckHoareStack.pop] cannot pop from empty stack"
    | elt::stck ->
      elt, stck

  let finish stck =
    match pop stck with
    | {idx;pre;cmd}, [] ->
      if idx = -1 && BExpr.(pre = true_) then
        cmd
      else
        failwithf "[finish] ill-formed stack state, initial index was %d and \
                   initial condition was %s " idx (BExpr.to_smtlib pre) ()
    | _, stck ->
      failwithf "[finish] nonempty stack state: %d elements after popping" (List.length stck) ()

  let choice stck1 stck2 =
    match stck1, stck2 with
    | elt1::stck1, elt2::stck2 ->
      if elt1.idx = elt2.idx && BExpr.equal elt1.pre elt2.pre && equal stck1 stck2 then
        {elt1 with cmd = HoareNet.choice elt1.cmd elt2.cmd}
        :: stck1
      else
        failwith "Dyck environment did not match after choice"
    | _, _ ->
      failwith "Dyck environments were different lengths after choice"

  let seq (stck : t) suffix : t =
    let ({idx;pre;cmd}, stck) = pop stck in
    let cmd = HoareNet.seq cmd suffix in
    push stck (idx, pre, cmd)

  let close (stck : t) (closing_idx, post) : t =
    let ({idx=current_idx;pre;cmd}, stck) = pop stck in
    if closing_idx = current_idx then
      HoareNet.triple pre cmd post
      |> seq stck
    else
      failwithf "Tried to close scope %d but was in scope %d" closing_idx current_idx ()

end

let gcl_to_hoare (t : target) : HoareNet.t =
  let rec loop t stack : DyckHoareStack.t=
    match t with
    | GSkip ->
      stack
    | GAssign (typ, var, bv)  ->
      HoareNet.assign (make_var typ var) (bv_to_expr bv)
      |> DyckHoareStack.seq stack
    | GSeq (g1,g2) ->
      stack
      |> loop g1
      |> loop g2
    | GChoice (g1,g2) ->
      let stack1 = loop g1 stack in
      let stack2 = loop g2 stack in
      DyckHoareStack.choice stack1 stack2
    | GAssume phi ->
      HoareNet.assume (form_to_bexpr phi)
      |> DyckHoareStack.seq stack
    | GAssert phi ->
      HoareNet.assert_ (form_to_bexpr phi)
      |> DyckHoareStack.seq stack
    | GExternVoid ("hopen",[Datatypes.Coq_inr idx; Datatypes.Coq_inl phi]) ->
      let phi = form_to_bexpr phi in
      let idx = bv_to_expr idx |> Expr.get_const |> Option.value_exn ~message:"Invalid hopen index" in
      DyckHoareStack.push stack (Bigint.to_int_exn idx, phi, HoareNet.skip)
    | GExternVoid ("hopen", _) ->
      failwith "unsupported arguments to hopen"
    | GExternVoid ("hclose", [Datatypes.Coq_inr idx; Datatypes.Coq_inl phi]) ->
      let phi = form_to_bexpr phi in
      let idx = bv_to_expr idx |> Expr.get_const |> Option.value_exn ~message:"Invalid hopen index" in
      DyckHoareStack.close stack (Bigint.to_int_exn idx, phi)
    | GExternVoid ("hclose", _) ->
      failwith "unsupported arguments to hclose"
    | GExternVoid ("assert",[Datatypes.Coq_inr phi]) ->
      HoareNet.assert_ (BExpr.eq_ (bv_to_expr phi) (Expr.bvi 1 1))
      |> DyckHoareStack.seq stack
    | GExternVoid ("assert", [Datatypes.Coq_inl phi]) ->
      HoareNet.assert_ (form_to_bexpr phi)
      |> DyckHoareStack.seq stack
    | GExternVoid ("assert",_) ->
      failwith "unsupported arguments to assert"
    | GTable (table, keys, actions) ->
      let keys = List.map keys ~f:(fun (k,_) -> bv_to_expr k |> Expr.get_var) in
      let actions = List.map actions ~f:(make_act table) in
      HoareNet.table (table, keys, actions)
      |> DyckHoareStack.seq stack
    | GExternAssn _
    | GExternVoid _ ->
      failwith "Externs should have been eliminated"
  in
  DyckHoareStack.init
  |> loop t
  |> DyckHoareStack.finish
