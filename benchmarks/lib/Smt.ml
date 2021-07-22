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
  
let check_sat consts phi =
  Printf.sprintf "%s\n\n(assert %s)\n\n(check-sat)%!"
    (Var.list_to_smtlib_decls consts)
    (BExpr.to_smtlib phi)
  
