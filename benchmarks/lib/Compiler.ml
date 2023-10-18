open Poulet4
open GCL
open GCL (* Annoying. Can we fix this? *)
open AST (* the P4cub Ast *)
open ToGCL
open Primitives
open DependentTypeChecker

open Core


module Poulet4EGCL = struct
  (* Compiler(s) from Poulet4's E.t, E.t, E.t GCL.t to HoareNet *)

  let exp_to_string : Exp.t -> string =
    Fn.compose Sexp.to_string Petr4.P4cubSexp.sexp_of_exp

  let eithermap ~f = function
    | Datatypes.Coq_inl x -> f x
    | Datatypes.Coq_inr x -> f x

  let rec coq_gcl_to_string : (E.t, E.t, E.t) t -> string =
    let open Printf in
    function
    | GSkip ->
      sprintf "skip"
    | GAssign (_, lhs, rhs) ->
      sprintf "%s := %s" (exp_to_string lhs) (exp_to_string rhs)
    | GSeq (g1, g2) ->
      sprintf "%s;\n %s" (coq_gcl_to_string g1) (coq_gcl_to_string g2)
    | GChoice (g1, g2) ->
      sprintf "{\n%s\n}\n [] \n{\n%s\n}\n" (coq_gcl_to_string g1) (coq_gcl_to_string g2)
    | GAssume phi ->
      sprintf "assume %s" (exp_to_string phi)
    | GAssert phi ->
      sprintf "assert %s" (exp_to_string phi)
    | GExternVoid (extern, args) ->
      List.to_string ~f:(eithermap ~f:exp_to_string) args
      |> sprintf "%s(%s)" extern
    | GExternAssn (lhs, extern, args) ->
      List.to_string ~f:(eithermap ~f:exp_to_string) args
      |> sprintf "%s := %s(%s)" (exp_to_string lhs) extern
    | GTable (tbl, keys, actions) ->
      List.to_string ~f:fst actions
      |> sprintf "%s.apply(%s, %s)" tbl @@ List.to_string ~f:(fun (k,_) -> exp_to_string k) keys



  let rec get_var_name : Exp.t -> string option =
    let open Option.Let_syntax in
    function
    (* fails when exp isnt variable-able  *)
    | Var (_, original_name, _) ->
      return original_name
    | Uop (_, Una.IsValid, arg) ->
      let%map name = get_var_name arg in
      sprintf "%s.isValid" name
    | Member (_, member_idx, arg) ->
      let%map name = get_var_name arg in
      sprintf "%s.%d" name member_idx
    | _ ->
       None

  let get_var_name_exn p4exp =
    get_var_name p4exp
    |> Option.value_exn
      ~message:(sprintf "[varify] Could not convert %s to variable" (exp_to_string p4exp))

  let type_of_exp : Exp.t -> Typ.t = function
    | Var (typ, _, _)
    | Uop (typ, _, _)
    | Member (typ, _, _) -> typ
    | p4exp -> failwithf "TODO Get type of %s" (exp_to_string p4exp) ()

  let typ_width : Typ.t -> int option = function
    | Bool -> Some 1
    | VarBit n | Bit n | Int n -> Some (Bigint.to_int_exn n)
    | Error | Array _ | Struct _ | Var _ ->
      None

  let extract_var_exn (typ, p4exp) : Var.t =
    let w = typ_width typ |> Option.value_exn ~message:(Printf.sprintf "Couldnt get width of %s" (exp_to_string p4exp)) in
    Var.make (get_var_name_exn p4exp) w

  let extract_var (typ, p4exp) : Var.t option =
    try
      Some (extract_var_exn (typ, p4exp))
    with _ -> None

  let rec varify (p4exp : Exp.t) : Exp.t =
    match p4exp with
    | Bool _ | VarBit _ | Bit _ | Int _ | Var _ | Error _ -> p4exp
    | Slice (hi, lo, arg) ->
      Slice (hi, lo, varify arg)
    | Cast (typ, arg) ->
      Cast(typ, varify arg)
    | Uop (_, Una.IsValid, _) ->
      Var (Typ.Bit Bigint.one, (get_var_name_exn p4exp), -1)
    | Uop (typ, op, arg) ->
      Uop (typ, op, varify arg)
    | Bop (typ, op, lhs, rhs) ->
      Bop (typ, op, varify lhs, varify rhs)
    | Lists (flag, es) ->
      Lists (flag, List.map es ~f:varify)
    | Index (elem_typ, array, index) ->
      Index (elem_typ, varify array, varify index)
    | Member (result_type, _, _) ->
      begin match get_var_name p4exp with
        | None -> p4exp
        | Some x -> Var (result_type, x, -1)
      end

  let map_coq_sum ~inr ~inl = function
    | Datatypes.Coq_inl x -> Datatypes.Coq_inl (inl x)
    | Datatypes.Coq_inr x -> Datatypes.Coq_inr (inr x)

  let rec exp_map_gcl ~exp : (E.t, E.t, E.t) t -> (E.t, E.t, E.t) t =
    function
    | GSkip -> GSkip
    | GAssign (typ, lhs, rhs) ->
      GAssign (typ, exp lhs, exp rhs)
    | GSeq (g1, g2) ->
      let g1 = exp_map_gcl ~exp g1 in
      let g2 = exp_map_gcl ~exp g2 in
      GSeq (g1, g2)
    | GChoice (g1, g2) ->
      let g1 = exp_map_gcl ~exp g1 in
      let g2 = exp_map_gcl ~exp g2 in
      GChoice (g1, g2)
    | GAssume phi ->
      GAssume (exp phi)
    | GAssert phi ->
      GAssert (exp phi)
    | GExternVoid (extern, args) ->
      let args = List.map args ~f:(map_coq_sum ~inl:exp ~inr:exp) in
      GExternVoid(extern, args)
    | GExternAssn (lhs, extern, args) ->
      let args = List.map args ~f:(map_coq_sum ~inl:exp ~inr:exp) in
      GExternAssn (exp lhs, extern, args)
    | GTable (tbl, keys, actions) ->
      let keys = List.map keys ~f:(Tuple2.map_fst ~f:exp) in
      let map_action (name, (data, act)) =
        (name, (List.map ~f:exp data, exp_map_gcl ~exp act))
      in
      let actions = List.map actions ~f:map_action in
      GTable(tbl, keys, actions)

  let to_unary_op_expr op arg =
    match op with
    | Una.BitNot -> Expr.bnot arg
    | Una.Not -> failwith "cannot translate boolean not to bitvectors, though i'd like to"
    | Una.Minus -> failwith "negative numbers unsupported"
    | Una.IsValid -> failwithf "isValid (%s) should already be a string, but its a Unary Op" (Expr.to_smtlib arg) ()

  let to_binary_op_expr =
    let open Bin in
    let open Expr in
    function
    | Plus -> badd
    | Minus -> bsub
    | PlusSat | MinusSat ->
      failwith "saturating arithmetic should have been factored out"
    | Times -> bmul
    | Shl -> shl_
    | Shr -> ashr_
    | BitAnd -> band
    | BitXor -> bxor
    | BitOr -> bor
    | PlusPlus
    | Le | Ge | Lt | Gt | Eq | NotEq ->
      failwith "comparison not supported"
    | And | Or ->
      failwith "booleans not supported"

  let rec to_expr_exn (p4exp : Exp.t) =
    let open Expr in
    match p4exp with
    | Bool b -> if b then bvi 1 1 else bvi 0 1
    | VarBit (max_width, _, value) ->
      Bigint.to_int_exn max_width
      |> bv value
    | Bit (width, value)
    | Int (width, value) ->
      Bigint.to_int_exn width
      |> bv value
    | Var (typ, original_name, _) ->
      let w = typ_width typ |> Option.value_exn ~message:(Printf.sprintf "Couldn't get width of variable %s" original_name) in
      var @@ Var.make original_name w
    | Slice (hi, lo, arg) ->
      to_expr_exn arg
      |> bslice (Bigint.to_int_exn lo) (Bigint.to_int_exn hi)
    | Cast (typ, arg) ->
      let width = typ_width typ |> Option.value_exn ~message:(Printf.sprintf "Couldn't get width for cast %s" (exp_to_string p4exp)) in
      let arg = to_expr_exn arg in
      bcast width arg
    | Uop (_, op, arg) ->
      (to_unary_op_expr op) (to_expr_exn arg)
    | Bop (_, op, lhs, rhs) ->
      (to_binary_op_expr op) (to_expr_exn lhs) (to_expr_exn rhs)
    | Lists _ | Index _ | Member _ | Error _ ->
      failwithf "[to_expr] Cannot translate %s to hoarenet, must be factored out" (exp_to_string p4exp) ()

  let to_unary_op_bexpr = function
    | Una.Not -> BExpr.not_
    | _ -> failwith "boolean conversion error: tried to translate a non-boolean unary operator to bexpr"

  let is_comparison =
    let open Bin in
    function
    | Le | Ge | Lt | Gt | Eq | NotEq -> true
    | _ -> false

  let is_logical = function
    | Bin.And | Bin.Or -> true
    | _ -> false

  let to_binary_op_comp =
    let open Bin in
    let open BExpr in
    function
    | Plus | PlusSat | Minus | MinusSat | Times | Shl | Shr | BitAnd | BitXor | BitOr | PlusPlus ->
      failwith "boolean conversion error: tried to translate a non-boolean binary operator to bexpr"
    | Le -> sle_
    | Ge -> sge_
    | Lt -> slt_
    | Gt -> sgt_
    | Eq -> eq_
    | NotEq -> fun x y -> not_ (eq_ x y)
    | And -> failwith "boolean conversion error: expected comparison, got &&"
    | Or -> failwith "boolean conversion error: expected comparison, got ||"

 let to_binary_op_bexpr =
    let open Bin in
    let open BExpr in
    function
    | Plus | PlusSat | Minus | MinusSat | Times | Shl | Shr | BitAnd | BitXor | BitOr | PlusPlus ->
      failwith "boolean conversion error: tried to translate a non-boolean binary operator to bexpr"
    | Le | Ge | Lt | Gt | Eq | NotEq ->
      failwith "boolean conversion error: expected logical boolean expression, got comparison "
    | And -> and_
    | Or -> or_

  let rec to_bexpr_exn (p4exp : Exp.t) =
    let open BExpr in
    match p4exp with
    | Bool b -> if b then true_ else false_
    | VarBit _ | Bit _ | Int _ ->
      failwithf "Cannot convert %s to a boolean" (exp_to_string p4exp) ()
    | Var (_, original_name, idx) ->
      let e = to_expr_exn (Var (Typ.Bool, original_name, idx)) in
      eq_ e @@ Expr.bvi 1 1
    | Slice _ ->
      failwithf "boolean conversion error, slicing is a bitvector operation: %s" (exp_to_string p4exp) ()
    | Cast (Typ.Bool, arg) ->
      to_expr_exn arg
      |> eq_ (Expr.bvi 1 1)
    | Cast _ ->
      failwithf "boolean conversion error, casting to non-boolean: %s" (exp_to_string (p4exp)) ()
    | Uop (_, op, arg) ->
      (to_unary_op_bexpr op) (to_bexpr_exn arg)
    | Bop (_, op, lhs, rhs) ->
      if is_logical op then
        (to_binary_op_bexpr op) (to_bexpr_exn lhs) (to_bexpr_exn rhs)
      else if is_comparison op then
        (to_binary_op_comp op) (to_expr_exn lhs) (to_expr_exn rhs)
      else
        failwithf "boolean conversion error: tried to use bitvector operator in a boolean context: %s" (exp_to_string p4exp) ()
    | Lists _ | Index _ | Member _ | Error _ ->
      failwithf "[to_bexpr] Cannot translate %s to hoarenet, must be factored out" (exp_to_string p4exp) ()

  let extern e args : Action.t list =
    let open Action in
    let open Datatypes in
    let extract hdr =
      let bit = Typ.Bit Bigint.one in
      let hdr_isValid = extract_var_exn (bit, Uop (bit, Una.IsValid, hdr)) in
      [assign hdr_isValid Expr.(bvi 1 1)]
    in
    match e, args with
    | "mark_to_drop",[] ->
      let egress_spec = Var.make "standard_metdata.1" 9 in
      [assign egress_spec (Expr.bvi 511 9)]
    | "assume", [Coq_inr phi] ->
      let phi = to_bexpr_exn phi in
      [assume phi]
    | "assume", _ ->
      failwithf "unrecognized arguments to assume: expected 1, got %d" (List.length args) ()
    | "extract", [Coq_inl hdr] ->
      extract hdr
    | "extract", [Coq_inr phi] ->
      Log.warn "Got an Coq_inr as an argument to extract, Optimistically forcing it into an Inl: %s" @@ lazy (exp_to_string phi);
      extract phi
    | _-> failwithf "TODO implement action %s wih %d arguments" e (List.length args) ()

  
  let to_action (action, (params, act)) : Var.t list * Action.t list =
    let var_params = List.map params ~f:(fun p -> extract_var (type_of_exp p, p) |> Option.value_exn ~message:(Printf.sprintf "failed to get parameter var of %s" (exp_to_string p))) in
    let rec to_action act =
      let open Action in
      match act with
      | GSkip -> []
      | GAssign (typ, lhs, rhs) ->
        let x = extract_var_exn (typ, lhs) in
        let e = to_expr_exn rhs in
        [assign x e]
      | GSeq (g1, g2) ->
        to_action g1 @ to_action g2
    | GChoice (_, _) ->
      failwith "to_action error unexpected CHOICE in actions"
    | GAssume expr ->
      let phi = to_bexpr_exn expr in
      [assume phi]
    | GAssert expr ->
      let phi = to_bexpr_exn expr in
      [assert_ phi]
    | GTable (name, _, _) ->
      failwithf "tables cannot be in actions, but got table %s in action %s" name action ()
    | GExternVoid (name, args) -> extern name args
    | GExternAssn _ -> failwith "TODO to_actions unimplemented externs"
    in
    (var_params, to_action act)

  let explode_and_fold_lists (p4exp : E.t) : E.t list =
    let access name i : string =
      Printf.sprintf "%s_$%d$" name i
    in
    let open List.Let_syntax in
    match p4exp with
    | Var (Typ.Array (n, typ), og_name, bruijn) ->
      List.init (Bigint.to_int_exn n) ~f:(fun idx ->
          E.Var (typ, access og_name idx, bruijn)
        )
    | Var _ -> return p4exp
    | Lists (Lst.Header _ , _) ->
      failwith "explode_and_fold_lists: what's a header literal?"
    | Lists (_ , es) ->
      es
    | Index (_, Lists (_, es), index_exp) ->
      begin match index_exp with
        | VarBit (_, _, index)
        | Bit (_, index)
        | Int (_, index) ->
          return @@ List.nth_exn es (Bigint.to_int_exn index)
        | _ ->
          failwithf "couldn't statically compute index of index %s, perhaps constant folding is required?"
            (exp_to_string index_exp) ()
      end
    | Index _ ->
      failwithf "unsure how to fold non-literal list indexing %s"
        (exp_to_string p4exp) ()
    | Member _ ->
      failwithf "unsure how to fold or explode membership access %s"
        (exp_to_string p4exp) ()
    | Error _
    | Bool _
    | VarBit _
    | Bit _
    | Int _
    | Slice _ (* not an array*)
    | Cast _ (* cannot cast arrays *)
    | Uop _ | Bop _ (* no operations on arrays *)
      ->
      return p4exp


  let rec elaborate_listlikes : (E.t, E.t, E.t) t -> (E.t, E.t, E.t) t =
    let open List.Let_syntax in
    let sum_elab (args : (E.t, E.t) Datatypes.sum list) =
      List.bind args ~f:(function
          | Coq_inl phi -> [Datatypes.Coq_inl phi]
          | Coq_inr exp ->
            let%map e = explode_and_fold_lists exp in
            Datatypes.Coq_inr e
        )
    in
    function
    | GSkip -> GSkip
    | GAssign (_, lhs, rhs) ->
      List.fold2_exn
        (explode_and_fold_lists lhs)
        (explode_and_fold_lists rhs)
        ~init:GSkip
        ~f:(fun acc lhs rhs ->
            GSeq (acc, GAssign (type_of_exp lhs, lhs, rhs)))
    | GSeq (g1, g2) ->
      GSeq (elaborate_listlikes g1, elaborate_listlikes g2)
    | GChoice (g1, g2) ->
      GChoice (elaborate_listlikes g1, elaborate_listlikes g2)
    | GAssume _ | GAssert _ as g ->
      g
    | GExternVoid (name, args) ->
      GExternVoid(name, sum_elab args)
    | GExternAssn (lhs, name, args) ->
      let lhss = explode_and_fold_lists lhs in
      if List.length lhss = 1 then
        GExternAssn (List.hd_exn lhss, name, sum_elab args)
      else
        failwith "elaborate: I don't know how to elaborate the lhs of an extern"
    | GTable (tbl, keys, actions) ->
      let elab_action (name, (data, act_cmd)) =
        (name, (data, elaborate_listlikes act_cmd))
      in
      let elab_keys =
        let%bind (key_exp, matchkind) = keys in
        let%map sub_key_exp = explode_and_fold_lists key_exp in
        (sub_key_exp, matchkind)
      in
      if List.length elab_keys = List.length keys then
        GTable (tbl, elab_keys, List.map ~f:elab_action actions)
      else
        failwith "elaborate: whole lists are not supported as keys"

  let eliminate_slices x = x

  let simplify_expressions coq_gpl =
    coq_gpl
    |> exp_map_gcl ~exp:varify
    |> elaborate_listlikes
    |> eliminate_slices

  let rec always_valid (expr : E.t) : bool =
    (* returns true if the expression is guaranteed to be valid, that is, it accesses no header values *)
    match expr with
    | Bool _ | VarBit _ | Var _ | Bit _ | Int _ | Error _ -> true
    | Slice (_,_,arg) -> always_valid arg
    | Cast (_, e) -> always_valid e
    | Uop (_, Una.IsValid, _) -> true
    | Uop (_, _, arg) -> always_valid arg
    | Bop (_, _, lhs, rhs) ->
      always_valid lhs && always_valid rhs
    | Lists (Struct, _) -> true
    | Lists (Header _, _) -> false
    | Lists (Array _, es) -> List.for_all es ~f:always_valid
    | Index (_, array, _) -> always_valid array
    | Member (_, _, arg) -> always_valid arg


let to_hoarenet (coq_gpl : (E.t, E.t, E.t) t) : HoareNet.t =
    let open HoareNet in
    let rec loop = function
    | GSkip -> skip
    | GAssign (typ, lhs, rhs) ->
      let x = extract_var_exn (typ, lhs) in
      let e = to_expr_exn rhs in
      assign x e
    | GSeq (g1, g2) ->
      sequence [loop g1; loop g2]
    | GChoice (g1, g2) ->
      choices [loop g1; loop g2]
    | GAssume expr ->
      let phi = to_bexpr_exn expr in
      assume phi
    | GAssert expr ->
      let phi = to_bexpr_exn expr in
      assert_ phi
    | GTable (name, keys, actions) ->
      let gpl_keys = List.map keys ~f:(fun (key, matchkind) ->
          let k = extract_var_exn (type_of_exp key, key) in
          match String.lowercase matchkind with
          | "exact" -> `Exact k
          | "lpm" | "ternary" | "optional" ->
            if always_valid key then
              `MaskableDegen k
            else
              `Maskable k
          | unknown_mk ->
            failwithf "unknown match_kind %s" unknown_mk ())
      in
      let gpl_actions = List.map actions ~f:to_action in
      instr_table (name, gpl_keys, gpl_actions)
    | GExternVoid (name, args) -> HoareNet.sequence_map ~f:HoareNet.of_action @@ extern name args
    | GExternAssn _ -> failwith ""
  in
  simplify_expressions coq_gpl
  |> loop


end

