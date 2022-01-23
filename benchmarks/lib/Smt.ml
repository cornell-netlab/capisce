open Core 
let string_of_timeout =
  Option.value_map ~default:""
    ~f:(Printf.sprintf "(set-option :timeout %i)\n\n")


let simplify consts str =
  Printf.sprintf "(set-logic UFBV)%s\n\n(simplify %s)\n%!"
    (Var.list_to_smtlib_decls consts)
    str

let assert_apply consts phi_str =
  Printf.sprintf "%s\n\n(assert %s)\n\n(apply qe)%!"
    (Var.list_to_smtlib_decls consts)
    phi_str 

let assert_apply_light consts phi_str =
  Printf.sprintf "%s\n\n(assert %s)\n\n(apply qe-light)%!"
    (Var.list_to_smtlib_decls consts)
    phi_str

let check_equiv consts1 phi1_str consts2 phi2_str =
  Printf.sprintf "(assert (= (exists (%s) %s) (exists (%s) %s)))\n(check-sat)"
    (Var.list_to_smtlib_quant consts1)
    phi1_str
    (Var.list_to_smtlib_quant consts2)
    phi2_str
 
let check_sat ?(timeout=None) consts phi_str =
  Printf.sprintf "%s%s\n\n(assert %s)\n\n(check-sat)%!"
    (string_of_timeout timeout)
    (Var.list_to_smtlib_decls consts)
    phi_str
    
let doesnt_contain_any s subs =
  List.for_all subs ~f:(fun substring -> not (String.is_substring s ~substring))

let success s =
  doesnt_contain_any s ["error"; "unknown"; "UNKNOWN"; "timeout"; "Killed"]

let is_sat s =
  success s
  && String.is_substring s ~substring:"sat"
  && not (String.is_substring s ~substring:"unsat")

let is_unsat s =
  success s
  && String.is_substring s ~substring:"unsat"

let is_unknown s =
  String.is_substring (String.lowercase s) ~substring:"unknown"
  

let qf s = doesnt_contain_any s ["forall"; "exists"]
  



    
