let string consts phi =
  Printf.sprintf "%s\n\n(simplify %s)\n%!"
    (Var.list_to_smtlib_decls consts)
    (Test.to_smtlib phi)
