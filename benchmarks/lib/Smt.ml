open Core 
let string_of_timeout =
  Option.value_map ~default:""
    ~f:(Printf.sprintf "(set-option :timeout %i)\n\n")


let simplify_str consts str =
  Printf.sprintf "(set-logic UFBV)%s\n\n(simplify %s)\n%!"
    (Var.list_to_smtlib_decls consts)
    str

let simplify consts phi =
  simplify_str consts (BExpr.to_smtlib phi)


let assert_apply_str consts phi_str =
  Printf.sprintf "%s\n\n(assert %s)\n\n(apply qe)%!"
    (Var.list_to_smtlib_decls consts)
    phi_str 

let assert_apply_light_str consts phi_str =
  Printf.sprintf "%s\n\n(assert %s)\n\n(apply qe-light)%!"
    (Var.list_to_smtlib_decls consts)
    phi_str


let assert_apply consts phi =
  assert_apply_str consts (BExpr.to_smtlib phi)

let check_sat ?(timeout=None) consts phi =
  Printf.sprintf "%s%s\n\n(assert %s)\n\n(check-sat)%!"
    (string_of_timeout timeout)
    (Var.list_to_smtlib_decls consts)
    (BExpr.to_smtlib phi)
  
let check_equiv consts1 phi1_str consts2 phi2_str =
  Printf.sprintf "(assert (= (exists (%s) %s) (exists (%s) %s)))\n(check-sat)"
    (Var.list_to_smtlib_quant consts1)
    phi1_str
    (Var.list_to_smtlib_quant consts2)
    phi2_str
