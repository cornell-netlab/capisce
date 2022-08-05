open Core
open Pbench
open Base_quickcheck
open Equivalences

let count = ref 0   
              
let identity () =
  Test.run_exn (module BExpr) ~config:z3_config
    ~f:(fun b ->
      [%test_pred: BExpr.t] (log_eq b) (BExpr.simplify b))

let well_formed_var () =
  Test.run_exn (module Var)
    ~f:([%test_pred: Var.t] Var.well_formed)

let well_formed_expr () =
  Test.run_exn (module Expr)
    ~f:([%test_pred: Expr.t] Expr.well_formed)

let well_formed_bexpr () =
  Test.run_exn (module BExpr)
    ~f:([%test_pred: BExpr.t] BExpr.well_formed)


let nested_foralls () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let start =
    dumb (fun () -> not_ (forall [z] (imp_ (eq_ (var z) (bvi 4 32))
                                        (forall [a] (eq_ (bvi 73722014 32) (var a))))))
  in
  let expected = not_ (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) 
                                     (forall [a] (eq_ (bvi 73722014 32) (var a))))) in 
  let simplified = simplify start in 
  Alcotest.(check bexpr) "syntactically equivalent" expected simplified

let nested_foralls1 () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let start =
    dumb (fun () -> (forall [z] (imp_ (eq_ (var z) (bvi 4 32))
                                        (forall [a] (eq_ (bvi 73722014 32) (var a))))))
  in
  let expected = (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) 
                                     (forall [a] (eq_ (bvi 73722014 32) (var a))))) in
  let simplified = simplify start in 
  Alcotest.(check bexpr) "syntactically equivalent" expected simplified  

let single_forall () =
  let open BExpr in
  let open Expr in
  let a = Var.make "a" 32 in
  let start =
    dumb (fun () -> forall [a] (eq_ (bvi 73722014 32) (var a)))
  in
  let expected = forall [a] (eq_ (bvi 73722014 32) (var a)) in
  let simplified = simplify start in 
  Alcotest.(check bexpr) "syntactically equivalent" expected simplified

let true_or_phi__true () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] true_ (or_ true_ b))
  
let phi_or_true__true () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] true_ (or_ b true_))

let false_or_phi__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (or_ false_ b))

let phi_or_false__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (or_ b false_))

(** TESTING CONJUNCTIONS *)
  
let false_and_phi__false () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] false_ (and_ false_ b))

let phi_and_false__false () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] false_ (and_ b false_))

let true_and_phi__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (and_ true_ b))

let phi_and_true__phi () =
  let open BExpr in
  Test.run_exn
    (module BExpr)
    ~f:(fun b -> [%test_eq: BExpr.t] b (and_ b true_))


let reduce_scope_right () =
  Test.run_exn
    ~config:{z3_config with test_count = 100}
    (module struct
       type t = Var.t * BExpr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let open BExpr in
         let%bind v = Var.quickcheck_generator in
         let f b1 = not (BExpr.vars b1 |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
         let%bind b1 = quickcheck_generator |> filter ~f in
         let%bind b2 = quickcheck_generator in
         return (v, b1, b2)
     end)
    ~f:(fun (v,b1,b2) ->
      let open BExpr in
      let phi () = forall [v] (imp_ b1 b2)  in
      let phi' () = imp_ b1 (forall [v] b2) in
      Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (dumb phi')
    )

let one_point_rule_imp () =
  Test.run_exn
    ~config:{z3_config with test_count = 100}
    (module struct
       type t = Var.t * Expr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind x = Var.quickcheck_generator in
         let x_fresh e = Expr.vars e  |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal x |> not in
         (* let x_occur b = BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal x in *)
         let%bind e = Expr.quickcheck_generator |> filter ~f:x_fresh in 
         let%bind b = BExpr.quickcheck_generator in (* |> filter ~f:x_occur in *)
         return (x, e, b)
     end)
    ~f:(fun (x, e, b) ->
      let open BExpr in
      let open Expr in
      let phi () = forall [x] (imp_ (eq_ (var x) e) b) in
      Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())
    )

let one_point_rule_or_not_left () =
  Test.run_exn
    ~config:{z3_config with test_count = 200}
    (module struct
       type t = Var.t * Expr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind x = Var.quickcheck_generator in
         let x_fresh e = Expr.vars e  |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal x |> not in
         (* let x_occur b = BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal x in *)
         let%bind e = Expr.quickcheck_generator |> filter ~f:x_fresh in 
         let%bind b = BExpr.quickcheck_generator in (* |> filter ~f:x_occur in *)
         return (x, e, b)
     end)
    ~f:(fun (x, e, b) ->
      let open BExpr in
      let open Expr in
      let phi () = forall [x] (or_ (not_ (eq_ (var x) e)) b) in
      Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())
    )

let one_point_rule_or_not_left_bug () =
      let open BExpr in
      let open Expr in
      let x = Var.make "kk" 32 in
      let e = var (Var.make "jy" 32) in 
      let b () =
        (ule_
           (shl_ (bnot (badd (bvi 2839304728 32) (var (Var.make "rl" 32))))
              (bnot (bnot (var (Var.make "uh" 32)))))
           (badd
              (ashr_ (bnot (bvi 24086778 32))
                 (bnot (var (Var.make "ns" 32))))
              (var (Var.make "jy" 32))))
      in
      let phi _u_ = forall [x] (or_ (not_ (eq_ (var x) e)) (b _u_)) in
      Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())

let funky_one_point_concrete () =
      let open Expr in
      let open BExpr in
      let x = Var.make "kk" 32 in
      let e = var (Var.make "jy" 32) in 
      let b () =
        (ule_
           (var (Var.make "rl" 32))
           (var x))
      in
      let b' _u_ = one_point_rule (var x) e (b _u_) in 
      let expected () =
          (ule_
             (var (Var.make "rl" 32))
             e) in
      Alcotest.(check bexpr_sexp)  "syntactically equivalent" (expected ()) (b' ())

      
(* `(Forall(kk 32)
 *   (TBin LOr(TNot(TComp
 *                     Eq(Var(kk 32))(Var(jy 32))@@((jy 32)(kk 32)))@@((jy 32)(kk 32)))
 *            (TComp Ule(Var(rl 32))(Var(kk 32))@@((kk 32)(rl 32))) 
              @@((jy 32)(kk 32)(rl 32))))' *)


let one_point_rule_or_not_right () =
  Test.run_exn
    ~config:{z3_config with test_count = 200}
    (module struct
       type t = Var.t * Expr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind x = Var.quickcheck_generator in
         let x_fresh e = Expr.vars e  |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal x |> not in
         (* let x_occur b = BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal x in *)
         let%bind e = Expr.quickcheck_generator |> filter ~f:x_fresh in 
         let%bind b = BExpr.quickcheck_generator in (* |> filter ~f:x_occur in *)
         return (x, e, b)
     end)
    ~f:(fun (x, e, b) ->
      let open BExpr in
      let open Expr in
      let phi () = forall [x] (or_ b (not_ (eq_ (var x) e))) in
      Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())
    )    
  
  
let reduce_scope_left () =
  Test.run_exn
    ~config:{z3_config with test_count = 100}
    (module struct
       type t = Var.t * BExpr.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let open BExpr in
         let%bind v = Var.quickcheck_generator in
         let f b2 = not (BExpr.vars b2 |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
         let%bind b1 = quickcheck_generator in
         let%bind b2 = quickcheck_generator |> filter ~f in
         return (v, b1, b2)
     end)
    ~f:(fun (v,b1,b2) ->
      let open BExpr in
      let phi = forall [v] (imp_ b1 b2) |> simplify in
      let phi' = or_ (forall [v] (not_ b1)) b2 |> simplify in
      Alcotest.(check smt_equiv) "logically equivalent" phi phi'
    )

let unused_u_var () =
  Test.run_exn
    ~config:{z3_config with test_count = 50}
    (module struct
       type t = Var.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
          let open Quickcheck.Generator in
          let open Let_syntax in
          let open BExpr in
          let%bind v = Var.quickcheck_generator in
          let f b = not (BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
          let%bind b = quickcheck_generator |> filter ~f in
          return (v, b)
     end)
    ~f:(fun (v,b) ->
      let open BExpr in
      Alcotest.(check smt_equiv) "logically equivalent" b (forall [v] b)      
    )

let unused_e_var () =
  Test.run_exn
    ~config:{z3_config with test_count = 50}
    (module struct
       type t = Var.t * BExpr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
          let open Quickcheck.Generator in
          let open Let_syntax in
          let open BExpr in
          let%bind v = Var.quickcheck_generator in
          let f b = not (BExpr.vars b |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v) in
          let%bind b = quickcheck_generator |> filter ~f in
          return (v, b)
     end)
    ~f:(fun (v,b) ->
      let open BExpr in
      [%test_pred: BExpr.t] (log_eq b) (exists [v] b)      
    )

let univ_eq () =
  Test.run_exn
    ~config:z3_config
    (module struct
       type t = Var.t * Expr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind v = Var.quickcheck_generator in
         let f e = Expr.vars e |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v |> not in 
         let%bind e = Expr.quickcheck_generator |> filter ~f in
         return (v, e)
     end)
    ~f:(fun (v,e) ->
      let open BExpr in
      let open Expr in
      Alcotest.(check smt_equiv) "logically equivalent" false_ (forall [v] (eq_ (var v) e)) 
    ) 

let univ_neq () =
  Test.run_exn
    ~config:z3_config
    (module struct
       type t = Var.t * Expr.t [@@deriving quickcheck, sexp]
       let quickcheck_generator : t Generator.t =
         let open Quickcheck.Generator in
         let open Let_syntax in
         let%bind v = Var.quickcheck_generator in
         let f e = Expr.vars e |> Util.uncurry (@) |> Util.lmem ~equal:Var.equal v |> not in 
         let%bind e = Expr.quickcheck_generator |> filter ~f in
         return (v, e)
     end)
    ~f:(fun (v,e) ->
      let open BExpr in
      let open Expr in
      Alcotest.(check smt_equiv) "logically equivalent" false_ (forall [v] (not_ (eq_ (var v) e))) 
    )   
  
let buggy_qc_example () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let phi () =
    forall [z]
      (imp_
        (not_ (exists [a] (eq_ (var a) (bvi 264974479 32))))
        (iff_ false_
           (eq_ (bsub (bvi 5371006 32) (bnot (bvi 1 32))) (var z))))
  in
  let smart_phi = phi () in
  let dumb_phi = dumb phi in
  Alcotest.(check smt_equiv) "Z3 proves equivalent" dumb_phi smart_phi
  
let buggy_qc_example_literal () =
    let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let got =
    forall [z]
      (imp_
        (not_ (exists [a] (eq_ (var a) (bvi 264974479 32))))
        (iff_ false_
           (eq_ (bsub (bvi 5371006 32) (bnot (bvi 1 32))) (var z)))) in
  let expected =
    dumb @@ fun () ->
              (imp_ (not_ (exists [a] (eq_ (var a) (bvi 264974479 32))))
                 (forall [z] (iff_ false_ (eq_ (bsub (bvi 5371006 32) (bnot (bvi 1 32))) (var z)))))
  in
  Alcotest.(check bexpr) "literally equivalent" expected got


let buggy_qc_example_1 () =
  let open BExpr in
  let open Expr in
  let m = Var.make "m" 32 in
  let c = Var.make "c" 32 in
  let h = Var.make "h" 32 in
  let z = Var.make "z" 32 in  
  let phi () =
    (iff_ false_
       (forall [m]
          (imp_
             (eq_ (bor (bvi 8 32) (bsub (bvi 3 32) (bvi 1172 32)))
                (var m))
             (forall [c]
                (forall [h]
                   (forall [z]
                      (eq_
                         (bor (var z)
                            (bsub (var h) (var c)))
                         (bnot (bvi 3 32))))))))) in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())

let buggy_qc_example_2 () =
  let open BExpr in
  let open Expr in
  let m = Var.make "m" 32 in
  let y = Var.make "y" 32 in
  let h = Var.make "h" 32 in
  let j = Var.make "j" 32 in
  let phi () =
    (forall [y]
       (imp_
          (iff_
             (or_
                (not_
                   (iff_ (imp_ (not_ false_) (not_ (not_ (not_ false_))))
                      (not_ true_)))
                false_)
             (imp_ false_
                (forall [m] (not_ (eq_ (bnot (bvi 679 32)) (var m))))))
          (forall [j]
             (eq_
                (bor (var y)
                   (bmul (bnot (var h)) (bvi 5173488 32))) 
                (var j)))))
  in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())

let roundtrip_gen_2 () =
  let open BExpr in
  let open Expr in
  let tt_var = Var.make "tt" 32 in
  let tt = var tt_var in
  let phi () = (forall [tt_var] (and_
                                   (ule_ (bvi 10055514 32) tt)
                                   (sge_ (bvi 25 32) (bnot (bvi 13 32))))) in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())

let roundtrip_gen_2a () =
  let open BExpr in
  let open Expr in
  let tt_var = Var.make "tt" 32 in
  let tt = var tt_var in
  let phi () = (forall [tt_var] (ule_ (bvi 10055514 32) tt)) in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())   

let roundtrip_gen_3 () =
  let open BExpr in
  let open Expr in
  let bw_var = Var.make "bw" 32 in
  let ga_var = Var.make "ga" 32 in
  let dq_var = Var.make "dq" 32 in
  let bw = var bw_var in
  let ga = var ga_var in
  let dq = var dq_var in
  let phi () = 
    forall [bw_var]
      (forall [ga_var]
         (forall [dq_var]
            (not_
               (ugt_ bw (bxor dq (ashr_ (bvi 4340 32) ga)))))) in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())
  
let symbolic () =
  let sym = Var.make "meta__ipv4_da" 32 in
  let data = Var.make "row_ipv4_lpm__meta_ipv4" 32 in
  Var.is_sym_of ~sym ~data
  |> Alcotest.(check bool) "is symbolic extension" true 
  
  
let rewrite_unused_mask () =
  let open BExpr in
  let open Expr in  
  let meta__ipv4_da = Var.make "meta__ipv4_da" 32 in
  let row_ipv4_lpm__meta_ipv4 = Var.make "_symb$ipv4_lpm$meta_ipv4" 32 in
  let row_ipv4_lpm__meta_ipv4Mask = Var.make "_symb$pv4_lpm$meta_ipv4Mask" 32 in
  let phi =
    forall [meta__ipv4_da]
      (not_ (eq_ (band (var meta__ipv4_da) (var row_ipv4_lpm__meta_ipv4Mask))
               (band (var row_ipv4_lpm__meta_ipv4) (var row_ipv4_lpm__meta_ipv4Mask)))) in
  Alcotest.(check bexpr) "syntactically equivalent" false_ phi

let rewrite_unused_mask_equivalent () =
  let open BExpr in
  let open Expr in  
  let meta__ipv4_da = Var.make "meta__ipv4_da" 32 in
  let row_ipv4_lpm__meta_ipv4 = Var.make "row_ipv4_lpm__meta_ipv4" 32 in
  let row_ipv4_lpm__meta_ipv4Mask = Var.make "row_ipv4_lpm__meta_ipv4Mask" 32 in
  let phi () =
    forall [meta__ipv4_da]
      (not_ (eq_ (band (var meta__ipv4_da) (var row_ipv4_lpm__meta_ipv4Mask))
               (band (var row_ipv4_lpm__meta_ipv4) (var row_ipv4_lpm__meta_ipv4Mask)))) in
  Alcotest.(check smt_equiv) "syntactically equivalent" (dumb phi) (phi ())   
  

let single_foralls1 () =
    let open BExpr in
    let open Expr in
    let z = Var.make "z" 32 in
    let start =
      dumb (fun () -> (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) false_)))
    in
    let expected = (forall [z] (imp_ (eq_ (var z) (bvi 4 32)) false_)) in  
    let simplified = simplify start in 
    Alcotest.(check bexpr) "syntactically equivalent" expected simplified  
  
  
let nested_foralls_literal () =
  let open BExpr in
  let open Expr in
  let z = Var.make "z" 32 in
  let a = Var.make "a" 32 in
  let got =
    not_ (forall [z] (imp_ (eq_ (var z) (bvi 4 32))
                        (forall [a] (eq_ (bvi 73722014 32) (var a)))))
    |> simplify
  in
  let expected = true_ in
  Alcotest.(check bexpr) "syntactically equivalent" expected got    
  
let and_not_example () =
  let open BExpr in
  let open Expr in
  let c = Var.make "c" 32 |> var in
  let b = Var.make "b" 32 |> var in
  let init =
    dumb (fun () ->
        (and_ (imp_ (eq_ c (badd b (bvi 3999 32))) false_) true_))
  in
  let simplified = BExpr.simplify init in
  [%test_pred: BExpr.t] (log_eq init) simplified

let and_not_eq__false_example () =
  let open BExpr in
  let open Expr in
  let x = Var.make "x" 1 |> var in  
  let phi = (and_
                (not_
                  (eq_ x (bvi 0 1)))
                (not_
                  (eq_ x (bvi 1 1)))) in
  Alcotest.(check bexpr) "literal equivalence" false_ phi

let and_not_example_literal () =
  let open BExpr in
  let open Expr in
  let c = Var.make "c" 32 |> var in
  let b = Var.make "b" 32 |> var in
  let phi = dumb (fun () -> eq_ c (badd b (bvi 3999 32))) in
  let init =
    dumb (fun () -> (and_ (imp_ phi false_) true_)) in
  let expected =
    dumb (fun () -> not_ phi)
  in
  let simplified = BExpr.simplify init in
  Alcotest.(check bexpr) "literal equivalence" expected simplified
  

let eliminate_quantified_variable_neq () =
  let open BExpr in
  let open Expr in
  let ipv4__isValid = Var.make "ipv4__isValid" 1 in
  let row_nat__ipv4__isValid = Var.make "row_nat__ipv4__isValid" 1 in 
  let b () = forall [ipv4__isValid] (not_ (eq_ (var ipv4__isValid) (var row_nat__ipv4__isValid))) in
  Alcotest.(check bexpr) "literal equivalence" false_ (b ())

let eliminate_quantified_variable_eq () =
  let open BExpr in
  let open Expr in
  let ipv4__isValid = Var.make "ipv4__isValid" 1 in
  let row_nat__ipv4__isValid = Var.make "row_nat__ipv4__isValid" 1 in 
  let b () = forall [ipv4__isValid] (eq_ (var ipv4__isValid) (var row_nat__ipv4__isValid)) in
  Alcotest.(check bexpr) "literal equivalence" false_ (b ())  

let eliminate_trivial_vars () =
  let open BExpr in
  let open Expr in
  let x = Var.make "x" 32 in
  let y = Var.make "y" 32 in
  let phi = dumb (fun () -> forall [x; y] (or_
                                             (imp_ false_ true_)
                                             (eq_ (var x) (var y)))) in
  
  Alcotest.(check smt_equiv) "proven equivalence" true_ phi


let left_scope_failure () =
  let open BExpr in
  let open Expr in
  let oo = Var.make "oo" 32 in
  let phi () = forall [oo]
              (imp_
                 (eq_ (var oo) (bvi 353 32))
                 (imp_ true_ true_)) in
  let computed () =
    (or_ (forall [oo] (not_ (eq_ (var oo) (bvi 353 32))))
         (imp_ true_ true_)) in
  Alcotest.(check smt_equiv) "logicall equivalence" (dumb phi) (dumb computed) 

let rsl_bug_left () =
  let open BExpr in
  let open Expr in
  let v = Var.make "ze" 32 in
  let jm = Var.make "jm" 32 in
  let mn = Var.make "mn" 32 in
  let b1 = iff_
             (not_ true_)
             (iff_ (imp_ (or_ true_ true_) true_)
                (iff_ true_ false_)) in
  let b2 = eq_ (var jm) (var mn) in
  let phi () = forall [v] (imp_ b1 b2) in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())
  

let rsl_bug_right () =
  let open BExpr in
  let open Expr in
  let v = Var.make "ze" 32 in
  let jm = Var.make "jm" 32 in
  let mn = Var.make "mn" 32 in
  let b1 = iff_
             (not_ true_)
             (iff_ (imp_ (or_ true_ true_) true_)
                (iff_ true_ false_)) in
  let b2 = eq_ (var jm) (var mn) in
  let phi () = or_ (forall [v] (not_ b1)) b2 in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb phi) (phi ())

let rsl_bug_dumbeq () =
  let open BExpr in
  let open Expr in
  let v = Var.make "ze" 32 in
  let jm = Var.make "jm" 32 in
  let mn = Var.make "mn" 32 in
  let b1 = iff_
             (not_ true_)
             (iff_ (imp_ (or_ true_ true_) true_)
                (iff_ true_ false_)) in
  let b2 = eq_ (var jm) (var mn) in
  let orig () = forall [v] (imp_ b1 b2) in
  let simpl () = or_ (forall [v] (not_ b1)) b2 in
  Alcotest.(check smt_equiv) "logically equivalent" (dumb simpl) (orig ())
  

let cached_vars () =
  Test.run_exn
    ~config:{Test.default_config with test_count = 100000}
    (module BExpr)
    ~f:(fun b ->
      let open BExpr in
      let sort = List.dedup_and_sort ~compare:Var.compare in
      let normalize (dvs,cvs) = (sort dvs, sort cvs) in
      let b = simplify b in
      let cached_vars = vars b |> normalize in
      let computed_vars = compute_vars b |> normalize in
      Alcotest.(check (pair (list var) (list var)))
        "set-like equivalent pairs" computed_vars cached_vars
    )

let cached_vars_ule_example () =
  let open BExpr in
  let sort = List.dedup_and_sort ~compare:Var.compare in
  let normalize (dvs,cvs) = (sort dvs, sort cvs) in
  let b =
    let open Expr in
    (ule_
       (shl_ (bnot (badd (bvi 2839304728 32) (var (Var.make "rl" 32))))
          (bnot (bnot (var (Var.make "uh" 32)))))
       (badd
          (ashr_ (bnot (bvi 24086778 32))
             (bnot (var (Var.make "ns" 32))))
          (var (Var.make "jy" 32))))
  in
  let cached_vars = vars b |> normalize in
  let computed_vars = compute_vars b |> normalize in
  Alcotest.(check (pair (list var) (list var)))
    "set-like equivalent pairs" computed_vars cached_vars


let one_point_rule_or_not_bug () =
  let open BExpr in
  let open Expr in
  let bitvar s = (var (Var.make s 1)) in
  let evar s = (var (Var.make s 32)) in
  let phi () = or_
                  (not_ (eq (bitvar "meta.spec.deref") (bv 0 1)))
                  (not_ (eq (bitvar "meta.spec.assign") (bv 0 1)))
                  (not_ (eq (bitvar "_symb$assign$match_0") hdr.ethernet.dstAddr))
                  (not_ (eq (evar "_symb$deref$match_0") (evar "meta.ptr")))
                  (not_ (eq (evar "_symb$allocator$match_0") (evar "_symb$deref$match_0"))) in  
  
  
  
let tests =
  [
    Alcotest.test_case "Variable Generator is well-formed" `Quick well_formed_var;
    Alcotest.test_case "Expression Generator is well-formed" `Quick well_formed_expr;
    Alcotest.test_case "Boolean Generator is well-formed" `Quick well_formed_bexpr;
    Alcotest.test_case "∀ kk. ¬(kk = jy) ∨ e(kk,jy,...)" `Quick one_point_rule_or_not_left_bug;
    Alcotest.test_case "computed vars are cached e" `Quick cached_vars_ule_example;
    Alcotest.test_case "one-point-style substitution works" `Quick funky_one_point_concrete;    
    Alcotest.test_case "QE buggy example" `Quick and_not_example;
    Alcotest.test_case "simplify((φ⇒⊥) ∧ ⊤) = ¬φ" `Quick and_not_example_literal;
    Alcotest.test_case "simplify(¬∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ ¬∀z. z=4 ⇒ (∀ a. 73722014=a)" `Quick nested_foralls;
    Alcotest.test_case "simplify(∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ ∀z. z=4 ⇒ (∀ a. 73722014=a)" `Quick nested_foralls1;
    Alcotest.test_case "simplify(¬∀z. z=4 ⇒ (∀ a. 73722014=a)) ≡ true" `Quick nested_foralls_literal;
    Alcotest.test_case "simplify(∀a. 73722014 = a) = smart(∀a.73722014=a)" `Quick single_forall;
    Alcotest.test_case "smart φ ⇔ dumb φ, φ = ∀ z. (¬ ∃ a. a = V) ⇒ (⊥ ⇔ z = N-1)" `Quick buggy_qc_example;
    Alcotest.test_case "∀ z. (¬ ∃ a. a = V) ⇒ (⊥ ⇔ z = N-1) = (¬ ∃ a. a = V) ⇒ ∀ z. (⊥ ⇔ z = N-1)" `Quick buggy_qc_example_literal;
    Alcotest.test_case "∀m. (m = e) ⇒ ∀ c h z. z|(h-c) = ~3 simplifies correctly" `Slow buggy_qc_example_1;
    Alcotest.test_case "complicated formula simplifies correctly" `Quick buggy_qc_example_2;
    Alcotest.test_case "(∀x. x ≠ y) reduces to (false) via smarts" `Quick eliminate_quantified_variable_neq;
    Alcotest.test_case "(∀x. x = y) reduces to (false) via smarts" `Quick eliminate_quantified_variable_eq;
    Alcotest.test_case "∀ x. (x & ρ.m) ≠ (ρ.x & ρ.m) reduces to ⊥" `Quick rewrite_unused_mask;
    Alcotest.test_case "∀ x. (x & ρ.m) ≠ (ρ.x & ρ.m) ⇔ ⊥" `Quick rewrite_unused_mask_equivalent;
    Alcotest.test_case "∀ xy. (⊥ ⇒ ⊤) ∨ (x = y) ⇔ ⊤" `Quick eliminate_trivial_vars;
    Alcotest.test_case "(x ≠ [1]₁) ∧ (x ≠ [0]₁) ⇔ ⊥" `Quick and_not_eq__false_example;
    Alcotest.test_case "∀ tt. (and (bvult 10.. tt) (bvsge 25 (bnot 13)))" `Quick roundtrip_gen_2;
    Alcotest.test_case "∀ tt. (bvult 10.. tt)" `Quick roundtrip_gen_2a;
    Alcotest.test_case "generated from roundtripping" `Slow roundtrip_gen_3;       
    Alcotest.test_case "rsl bug left" `Quick rsl_bug_left;
    Alcotest.test_case "rsl bug right" `Quick rsl_bug_right;
    Alcotest.test_case "rsl bug dumb equivalent" `Quick rsl_bug_dumbeq;
    Alcotest.test_case "rsl failure" `Quick left_scope_failure;
    Alcotest.test_case "QC Smart QE" `Slow identity;
    Alcotest.test_case "QC ⊤ ∨ φ = ⊤" `Quick true_or_phi__true;
    Alcotest.test_case "QC ⊥ ∨ φ = φ" `Quick false_or_phi__phi;
    Alcotest.test_case "QC φ ∨ ⊤ = ⊤" `Quick phi_or_true__true;
    Alcotest.test_case "QC φ ∨ ⊤ = φ" `Quick phi_or_false__phi;    
    Alcotest.test_case "QC φ ∧ ⊤ = φ" `Quick phi_and_true__phi;
    Alcotest.test_case "QC ⊤ ∧ φ = φ" `Quick true_and_phi__phi;
    Alcotest.test_case "QC φ ∧ ⊥ = ⊥" `Quick phi_and_false__false;
    Alcotest.test_case "QC ⊥ ∧ φ = ⊥" `Quick false_and_phi__false;    
    Alcotest.test_case "QC one_point_rule_imp" `Slow one_point_rule_imp;
    Alcotest.test_case "QC one_point_rule_or_not_left" `Slow one_point_rule_or_not_left;
    Alcotest.test_case "QC one_point_rule_or_not_right" `Slow one_point_rule_or_not_right;        
    Alcotest.test_case "QC reduce_scope_right" `Slow reduce_scope_right;
    Alcotest.test_case "QC reduce_scope_left" `Slow reduce_scope_left;
    Alcotest.test_case "QC unused_u_var" `Quick unused_u_var;
    Alcotest.test_case "QC unused_e_var" `Quick unused_e_var;
    Alcotest.test_case "QC univ_eq" `Quick univ_eq;
    Alcotest.test_case "QC univ_neq" `Quick univ_neq;
    Alcotest.test_case "QC cached_vars" `Slow cached_vars;
  ]

  
                   
