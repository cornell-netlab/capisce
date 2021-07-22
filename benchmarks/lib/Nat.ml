open Core
open Cmd

let max_rows = 1024
let rowsize n = 
  int_of_float
    (Float.round_up (Core.log (float_of_int n) /. Core.log (float_of_int 2)))               

let vec x n = Expr.bv (Bigint.of_int x) n             
  
let zero n = vec 0 n  

let one n = vec 1 n

let clone = vec 99 32 

let drop = vec 511 9

let setzero s = assign (Var.make s 1) (zero 1)
let setone s = assign (Var.make s 1) (one 1)

let evar s n = Expr.var (Var.make s n)

             
let asmeq e1 e2 = assume (BExpr.eq_ e1 e2)
let asmeq_sv s v sz = asmeq (evar s sz) (Expr.bv (Bigint.of_int v) sz)                
let asmeq_ss s1 s2 sz = asmeq (evar s1 sz) (evar s2 sz)
let asm0 s1 sz = asmeq (evar s1 sz) (zero sz)
let asm1 s1 sz = asmeq (evar s1 sz) (one sz)
               
let asteq e1 e2 = assert_ (BExpr.eq_ e1 e2)
let asteq_sv s v sz = asteq (evar s sz) (Expr.bv (Bigint.of_int v) sz)                
let asteq_ss s1 s2 sz = asteq (evar s1 sz) (evar s2 sz)
let ast0 s1 sz = asteq (evar s1 sz) (zero sz)
let ast1 s1 sz = asteq (evar s1 sz) (one sz)

let copy s1 s2 sz =
  assign (Var.make s1 sz) (evar s2 sz)

let set s e sz = assign (Var.make s sz) e

let decrement s sz = set s (Expr.bsub (evar s sz) (one sz)) sz                

let choice_seq cs1 cs2 = choice (sequence cs1) (sequence cs2)  

let choice_seqs cs =
  List.fold cs ~init:(assume BExpr.false_)
    ~f:(fun c cs -> choice c (sequence cs))

let ifelse t c1 c2 =
  choice_seq (assume t::c1) (assume (BExpr.not_ t)::c2)
                       
let ternary d r sz =
  let v x = evar x sz in
  let m = r ^ "Mask" in
  choice_seq
    [asm0 m sz]
    [ negate (asm0 m sz);
      (* ast1 (d ^ "__init") 1; *)
      asmeq Expr.(band (v d) (v m)) Expr.(band (v r) (v m ))]

let copy_meta_to_hf hdr fld meta sz =
  let hf = Printf.sprintf "%s__%s" hdr fld in
  let init = Printf.sprintf "%s__init" in
  let h_is_valid = BExpr.eq_ (evar (Printf.sprintf "%s__isValid" hdr) 1) (one 1) in
  [ (* ast1 (init meta) 1; *)
    copy hf meta sz;
    ifelse h_is_valid [setone (init hf)] [];
  ] |> sequence
           
  
let prog =
  [ (* setzero "cpu_header__isValid";
     * setzero "cpu_header__preamble__init";    
     * setzero "cpu_header__device__init";
     * setzero "cpu_header__reason__init";
     * setzero "cpu_header__if_index__init";    
     * 
     * setzero "ethernet__isValid";
     * setzero "ethernet__dstAddr__init";    
     * setzero "ethernet__srcAddr__init";
     * setzero "ethernet__etherType__init";
     * 
     * setzero "ipv4__isValid";
     * setzero "ipv4__version__init";
     * setzero "ipv4__ihl__init";
     * setzero "ipv4__diffserv__init";    
     * setzero "ipv4__totalLen__init";    
     * setzero "ipv4__identification__init";    
     * setzero "ipv4__flags__init";    
     * setzero "ipv4__fragOffset__init";    
     * setzero "ipv4__ttl__init";    
     * setzero "ipv4__protocol__init";    
     * setzero "ipv4__hdrChecksum__init";    
     * setzero "ipv4__srcAddr__init";    
     * setzero "ipv4__dstAddr__init";    
     * 
     * setzero "tcp__isValid";   
     * setzero "tcp__srcPort__init";
     * setzero "tcp__dstPort__init";
     * setzero "tcp__seqNo__init";
     * setzero "tcp__ackNo__init";
     * setzero "tcp__dataOffset__init";
     * setzero "tcp__res__init";
     * setzero "tcp__flags__init";
     * setzero "tcp__window__init";
     * setzero "tcp__checksum__init";
     * setzero "tcp__urgentPtr__init";
     * 
     * 
     * setzero "meta__do_forward__init";
     * setzero "meta__ipv4_sa__init";
     * setzero "meta__ipv4_da__init";
     * setzero "meta__tcp_sp__init";
     * setzero "meta__tcp_dp__init";
     * setzero "meta__nhop_ipv4__init";
     * setzero "meta__if_ipv4_addr__init";
     * setzero "meta__if_mac_addr__init";
     * setzero "meta__is_ext_if__init";
     * setzero "meta__tcpLength__init";
     * setzero "meta__if_index__init"; *)

    (* initialize standard_metadata to 0 to check determined forwarding*)
    set "standard_metadata__egress_spec" (zero 9) 9;
    
    (* assign (Var.make "meta__if_index" 9) (Expr.var (Var.make "standard_metadata__ingress_port" 9));
     * 
     * ifelse BExpr.(eq_ (evar"pkt__lookahead" 64) (zero 64))
     *   [ asm0 "pkt__lookahead" 64;
     *     setone "cpu_header__isValid";
     *     setone "cpu_header__preamble__init";    
     *     setone "cpu_header__device__init";
     *     setone "cpu_header__reason__init";
     *     setone "cpu_header__if_index__init";
     *     copy "cpu_header__preamble" "pkt__lookahead" 64;
     *     copy "meta__if_index" "cpu_header__if_index" 9;
     *   ]
     *   [ ];
     * 
     * setone "ethernet__isValid";
     * setone "ethernet__dstAddr__init";    
     * setone "ethernet__srcAddr__init";
     * setone "ethernet__etherType__init";        
     * 
     * choice_seq [
     *     asmeq_sv "ethernet__etherType" 2048 16;
     *     setone "ipv4__isValid";
     *     setone "ipv4__version__init";
     *     setone "ipv4__ihl__init";
     *     setone "ipv4__diffserv__init";    
     *     setone "ipv4__totalLen__init";    
     *     setone "ipv4__identification__init";    
     *     setone "ipv4__flags__init";    
     *     setone "ipv4__fragOffset__init";    
     *     setone "ipv4__ttl__init";    
     *     setone "ipv4__protocol__init";    
     *     setone "ipv4__hdrChecksum__init";    
     *     setone "ipv4__srcAddr__init";    
     *     setone "ipv4__dstAddr__init";    
     *     
     *     copy "meta__ipv4_sa" "ipv4__srcAddr" 32;
     *     setone "meta__ipv4_sa__init";
     *     copy "meta__ipv4__da" "ipv4__dstAddr" 32;
     *     setone "meta__ipv4_sa__init";
     *             
     *     (\*skip tcp len, its boring*\)
     *     choice_seq [
     *         asmeq_sv "ipv4__protocol" 6 8;
     *         setone "tcp__isValid";
     *         setone "tcp__srcPort__init";
     *         setone "tcp__dstPort__init";
     *         setone "tcp__seqNo__init";
     *         setone "tcp__ackNo__init";
     *         setone "tcp__dataOffset__init";
     *         setone "tcp__res__init";
     *         setone "tcp__flags__init";
     *         setone "tcp__window__init";
     *         setone "tcp__checksum__init";
     *         setone "tcp__urgentPtr__init";
     * 
     *         copy "meta__tcp_sp" "tcp__srcPort" 32;
     *         setone "meta__tcp_sp__init";
     *         copy "meta__tcp_dp" "tcp__dstPort" 32;
     *         setone "meta__tcp_dp__init"
     *       ]
     *       [negate (asmeq_sv "ipv4__protocol" 6 8)]
     *   ]
     *   [negate (asmeq_sv "ethernet__etherType" 2048 16)]; *)

    (*Start ingress*)
    (* if_info *)
    (* asmeq_ss "ghost_if_info__meta__if_index" "meta__if_index" 9; *)
    (* choice_seq
     *   [asmeq_ss "row_if_info__meta__if_index" "meta__if_index" 9;
     *    asm0 "ghost_if_info__miss" 1;
     *    (\* asmeq_ss "ghost_if_info__hitAction" "row_if_info__id" (rowsize max_rows); *\)
     *    choice_seq
     *      [ asm0 "row_if_info__action" 1;
     *        assign (Var.make "standard_metadata__egress_spec" 9) drop]
     *      [ asm1 "row_if_info__action" 1;
     *        copy "meta__if_ipv4_addr" "row_if_info__data__ipv4_addr" 32;
     *        setone "meta__if_ipv4_addr__init";           
     *        copy "meta__if_mac_addr" "row_if_info__data__mac_addr" 48;
     *        setone "meta__if_mac_addr__init";           
     *        copy "meta__is_ext_if" "row_if_info__data__is_ext" 1;
     *        setone "meta__is_ext_if__init";
     *      ]
     *   ]
     *   [ asm1 "ghost_if_info__miss" 1]; *)
    (*/ if_info *)

    (* nat  *)    
    (* asmeq_ss "ghost_nat__meta__is_ext_if" "meta__is_ext_if" 1; 
     * asmeq_ss "ghost_nat__meta__ipv4__isValid" "ipv4__isValid" 1;
     * asmeq_ss "ghost_nat__meta__tcp__isValid" "tcp__isValid" 1;
     * asmeq_ss "ghost_nat__ipv4__srcAddr" "ipv4__srcAddr" 32;
     * asmeq_ss "ghost_nat__ipv4__dstAddr" "ipv4__dstAddr" 32;
     * asmeq_ss "ghost_nat__tcp__srcPort" "tcp__srcPort" 32;
     * asmeq_ss "ghost_nat__tcp__dstPort" "tcp__dstPort" 32; *)

    (* ast1 "meta__is_ext_if__init" 1; *)

    asmeq_ss "meta__is_ext_if" "row_nat__meta__is_ext_if" 1;
    choice_seq [
        asmeq_ss "ipv4__isValid" "row_nat__ipv4__isValid" 1;
        asmeq_ss "tcp__isValid" "row_nat__tcp__isValid" 1;
        ternary "ipv4__srcAddr" "row_nat__ipv4__srcAddr" 32;
        ternary "ipv4__dstAddr" "row_nat__ipv4__dstAddr" 32;
        ternary "tcp__srcPort" "row_nat__tcp__srcPort" 32;
        ternary "tcp__dstPort" "row_nat__dstPort" 32;

        asm0 "ghost_nat__miss" 1;
        (* asmeq_ss "ghost_nat__hitAction" "rho_nat__id" 7; *)

        choice_seqs
          [[asmeq_sv "row_nat__action" 0 3;
            set "standard_metadata__egress_spec" drop 9];

           [asmeq_sv "row_nat__action" 1 3;
            set "standard_metadata__instance_type" clone 32;
           ];

           (* [asmeq_sv "row_nat__action" 2 3;
            *  setzero "meta__do_forward";
            *  setone "meta__do_forward__init";
            *  set "standard_metadata__egress_spec" drop 9
            * ];
            * 
            * [asmeq_sv "row_nat__action" 3 3;
            *  setone "meta__do_forward";
            *  setone "meta__do_forward__init";        
            *  copy "meta__ipv4_sa" "row_nat__data__srcAddr" 32;
            *  setone "meta__ipv4_sa__init";
            *  copy "meta__tcp_sp" "row_nat__data__srcPort" 32;
            *  setone "meta__tcp_sp__init";
            * ];
            * 
            * [asmeq_sv "row_nat__action" 4 3;
            *  setone "meta__do_forward";
            *  setone "meta__do_forward__init";        
            *  copy "meta__ipv4_da" "row_nat__data__dstAddr" 32;
            *  setone "meta__ipv4_da__init";
            *  copy "meta__tcp_dp" "row_nat__data__dstPort" 32;
            *  setone "meta__tcp_dp__init"
            * ];
            * 
            * [asmeq_sv "row_nat__action" 5 3;
            *  setone "meta__do_forward";
            *  setone "meta__do_forward__init"] *)
          ]
      ] 
      [asm1 "ghost_nat__miss" 1];

    (* ast1 "meta__do_forward__init" 1; *)
    ifelse BExpr.(eq_ (evar "meta__do_forward" 1) (one 1)) [
        (* ast1 "ipv4__ttl__init" 1; *)
        ifelse BExpr.(not_ (eq_ (evar "ipv4__ttl" 8) (zero 8))) [
            (* ipv4_lpm *)
            (* asmeq_ss "ghost_ipv4_lpm__meta__ipv4_da" "meta__ipv4_da" 32; *)
            choice_seq              
              [(* hit *)
                ternary "meta__ipv4_da" "row_ipv4_lpm__meta_ipv4" 32;
    
                asm0 "ghost_ipv4_lpm__miss" 1;
                asmeq_ss "ghost_ipv4_lpm__hitAction" "row_ipv4_lpm__id" 10;
                choice_seq [
                    (* set_nhop *)
                    asm0 "row_ipv4_lpm__action" 1;
                    copy "meta__nhop_ipv4" "row_ipv4_lpm__nhop_ipv4" 32;
                    setone "meta__nhop_ipv4__init";
                    copy "standard_metadata__egress_spec" "row_ipv4_lpm__port" 9;
                    (* ast1 "ipv4__ttl__init" 1; *)
                    decrement "ipv4__ttl" 8;
                  ] [(* _drop *)
                    asm1 "row_ipv4_lpm__action" 1;
                    set "standard_metadata__egress_spec" drop 9;
                  ]
              ]
              [
                asm1 "ghost_ipv4_lpm__miss" 1;
              ];
            (*/ ipv4_lpm *)
            
            (* forward *)
            (* ast1 "meta__nhop_ipv4__init" 1; *)
            (* asmeq_ss "ghost_forward__meta__nhop_ipv4" "meta__nhop_ipv4" 32; *)
            choice_seq [
                (* hit *)
                asmeq_ss "meta__nhop_ipv4" "row_forward__nhop_ipv4" 32;
                asm0 "ghost_forward__miss" 1;
                (* asmeq_ss "ghost_forward__hitAction" "row_forward__id" 32; *)
                choice_seq [
                    (* _set_dmac *)
                    asm0 "row_forward__action" 1;
                    copy "ethernet__dstAddr" "row_forward__data__dmac" 48;
                  ] [
                    (* _drop  *)
                    asm0 "row_forward__action" 1;
                    set "standard_metadata__egress_spec" drop 9;
                  ]
              ] [
                (* miss *)
                asm1 "ghost_forward__miss" 1;
              ]            
            (*/forward*)
          ] []        
      ]
      [];

    assert_ BExpr.(not_ (eq_ (evar "standard_metadata__egress_spec" 9) (zero 9)));
    (*/ ingress*)
  ] |> sequence
    (* egress *)
  (*   ifelse BExpr.( eq_ (evar "standard_metadata__egress_spec" 9) drop)
   *     []
   *     [ copy "standard_metadata__egress_port" "standard_metadata__egress_spec" 9;
   * 
   *       ifelse BExpr.(eq_ (evar "standard_metadata__instance_type" 32) (zero 32))
   *       [ (\* send_frame *\)
   *         (\* asmeq_ss "standard_metadata__egress_port" "ghost_send_frame__standard_metadata__egress_port" 9; *\)
   *         choice_seq
   *           [ (\* hit *\)
   *             asmeq_ss "standard_metadata__egress_port" "row_send_frame__standard_metadata__egress_port" 9;
   *             asm0 "ghost_send_frame__miss" 1;
   *             (\* asmeq_ss "ghost_send_frame__hitAction" "row_send_frame__id" 8; *\)
   *             choice_seq [
   *                 (\* do_rewrites *\)
   *                 asm0 "row_send_frame__action" 1;
   *                 setzero "cpu_header__isValid";
   *                 setzero "cpu_header__preamble__init";    
   *                 setzero "cpu_header__device__init";
   *                 setzero "cpu_header__reason__init";
   *                 setzero "cpu_header__if_index__init";
   * 
   *                 copy "ethernet__srcAddr" "row_send_frame__smac" 32;
   * 
   *                 copy_meta_to_hf "ipv4" "srcAddr" "meta__ipv4_sa" 32;
   *                 copy_meta_to_hf "ipv4" "dstAddr" "meta__ipv4_da" 32;
   *                 copy_meta_to_hf "tcp" "srcPort" "meta__tcp_sp" 32;
   *                 copy_meta_to_hf "tcp" "dstPort" "meta__tcp_dp" 32;
   *                 
   *               ] [
   *                 (\* _drop *\)
   *                 asm1 "row_send_frame__action" 1;
   *                 set "standard_metadata__egress_spec" drop 9;
   *               ]
   *           ]
   *           [ (\* miss *\)
   *             asm1 "ghost_send_frame__miss" 1
   *           ]
   *         (\* / send_frame *\)
   *       ] [
   *         (\* send_to_cpu*\)
   *         choice_seq
   *           [ (\* hit *\)
   *             asm0 "ghost_send_to_cpu__miss" 1;
   *             (\* asmeq_ss "ghost_send_to_cpu__hitAction" "row_send_to_cpu__id" 1; *\)
   *             (\*do cpu encap*\)              
   *             setone "cpu_header__isValid";
   *             setone "cpu_header__preamble__init";    
   *             setone "cpu_header__device__init";
   *             setone "cpu_header__reason__init";
   *             setone "cpu_header__if_index__init";
   * 
   *             set "cpu_header__preamble" (zero 64) 64;    
   *             set "cpu_header__device" (zero 8) 8;
   *             set "cpu_header__reason" (vec 171 8) 8;
   *             copy "cpu_header__if_index" "meta__if_index" 9;
   *           ]
   *           [ (\* miss *\)
   *             asm1 "ghost_send_to_cpu__miss" 1;
   *           ]
   *         (\* / send_to_cpu*\)
   *       ]
   *     ]
   * ] |> sequence *
   *
   *)

let proglite =
  [ choice_seq [
        asmeq_ss "ipv4__isValid" "row_nat__ipv4__isValid" 1;
        (* asmeq_ss "tcp__isValid" "row_nat__tcp__isValid" 1;
         * ternary "ipv4__srcAddr" "row_nat__ipv4__srcAddr" 32;
         * ternary "ipv4__dstAddr" "row_nat__ipv4__dstAddr" 32;
         * ternary "tcp__srcPort" "row_nat__tcp__srcPort" 32;
         * ternary "tcp__dstPort" "row_nat__dstPort" 32; *)

        asm0 "ghost_nat__miss" 1;

        choice_seqs
          [[asmeq_sv "row_nat__action" 0 3;
            set "standard_metadata__egress_spec" drop 9];

           [asmeq_sv "row_nat__action" 1 3;
            set "standard_metadata__instance_type" clone 32;
           ];
          ]
      ] 
      [asm1 "ghost_nat__miss" 1];

    choice_seq              
      [(* hit *)
        ternary "meta__ipv4_da" "row_ipv4_lpm__meta_ipv4" 32;
        
          asm0 "ghost_ipv4_lpm__miss" 1;
          asmeq_ss "ghost_ipv4_lpm__hitAction" "row_ipv4_lpm__id" 10;
          choice_seq [
              (* set_nhop *)
                asm0 "row_ipv4_lpm__action" 1;
                (* copy "meta__nhop_ipv4" "row_ipv4_lpm__nhop_ipv4" 32;
                 * setone "meta__nhop_ipv4__init"; *)
                copy "standard_metadata__egress_spec" "row_ipv4_lpm__port" 9;
                (* ast1 "ipv4__ttl__init" 1; *)
                (* decrement "ipv4__ttl" 8; *)
              ] [(* _drop *)
              asm1 "row_ipv4_lpm__action" 1;
              set "standard_metadata__egress_spec" drop 9;
            ]
      ]
      [
        asm1 "ghost_ipv4_lpm__miss" 1;
      ];
    (*/ ipv4_lpm *)
      
    (* (\* forward *\)
     * (\* ast1 "meta__nhop_ipv4__init" 1; *\)
     * (\* asmeq_ss "ghost_forward__meta__nhop_ipv4" "meta__nhop_ipv4" 32; *\)
     * choice_seq [
     *     (\* hit *\)
     *     asmeq_ss "meta__nhop_ipv4" "row_forward__nhop_ipv4" 32;
     *     asm0 "ghost_forward__miss" 1;
     *     (\* asmeq_ss "ghost_forward__hitAction" "row_forward__id" 32; *\)
     *       choice_seq [
     *           (\* _set_dmac *\)
     *           asm0 "row_forward__action" 1;
     *           copy "ethernet__dstAddr" "row_forward__data__dmac" 48;
     *         ] [
     *           (\* _drop  *\)
     *           asm0 "row_forward__action" 1;
     *           set "standard_metadata__egress_spec" drop 9;
     *         ]
     *   ] [
     *     (\* miss *\)
     *     asm1 "ghost_forward__miss" 1;
     *   ];             *)
      (*/forward*)  
    assert_ BExpr.(not_ (eq_ (evar "standard_metadata__egress_spec" 9) (zero 9)));
    
  ]
  |> sequence

let smt () =
  Log.print (Cmd.to_string proglite );
  let phi = wp proglite BExpr.true_ in
  let (dvs, cvs) = BExpr.vars phi in
  BExpr.forall dvs phi
  |> Smt.simplify cvs       
                     
let smt_slicing () =
  let cs = Cmd.assert_slices prog in
  let phis = List.map cs ~f:(fun prog -> Cmd.wp prog BExpr.true_) in
  List.map phis ~f:(fun phi ->
        let (dvs, cvs) = BExpr.vars phi in
        BExpr.forall dvs phi
        |> Smt.simplify cvs)
