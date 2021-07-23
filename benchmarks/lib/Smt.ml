open Core 
let string_of_timeout =
  Option.value_map ~default:""
    ~f:(Printf.sprintf "(set-option :timeout %i)\n\n")

let simplify consts phi =
  Printf.sprintf "%s\n\n(simplify %s)\n%!"
    (Var.list_to_smtlib_decls consts)
    (BExpr.to_smtlib phi)

let simplify_str consts str =
  Printf.sprintf "%s\n\n(simplify %s)\n%!"
    (Var.list_to_smtlib_decls consts)
    str

let assert_apply consts phi =
  Printf.sprintf "%s\n\n(assert %s)\n\n(apply qe)%!"
    (Var.list_to_smtlib_decls consts)
    (BExpr.to_smtlib phi)


let check_sat ?(timeout=None) consts phi =
  Printf.sprintf "%s%s\n\n(assert %s)\n\n(check-sat)%!"
    (string_of_timeout timeout)
    (Var.list_to_smtlib_decls consts)
    (BExpr.to_smtlib phi)
  
