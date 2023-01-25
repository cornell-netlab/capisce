open Core 
let string_of_timeout =
  Option.value_map ~default:""
    ~f:(Printf.sprintf "(set-option :timeout %i)\n\n")


let simplify consts str =
  Printf.sprintf "(set-logic UFBV)%s\n\n(simplify %s)\n%!"
    (Var.list_to_smtlib_decls consts)
    str

let tseitin consts =
  Printf.sprintf "(set-logic UFBV)%s\n\n(assert %s)\n(apply tseitin-cnf)"
    (Var.list_to_smtlib_decls consts)

let assert_apply ?timeout consts phi_str =
  let open Printf in
  let cmd = match timeout with
    | None -> "(apply qe)"
    | Some ms -> sprintf "(apply (try-for qe %i))" ms in  
  sprintf "%s\n\n(assert %s)\n\n%s%!"
    (Var.list_to_smtlib_decls consts)
    phi_str
    cmd

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

let check_sat_funs ?(timeout=None) consts funs phi_str =
  (* Printf.sprintf "%s%s\n%s\n(assert %s)\n\n(check-sat)%!" *)
  Printf.sprintf "%s%s\n%s\n(assert %s)\n\n(check-sat)%!"
    (string_of_timeout timeout)
    (Var.list_to_smtlib_decls consts)
    funs
    ((fun _ -> "true")
       phi_str
    )


let check_sat_model ?(timeout=None) consts phi_str =
  Printf.sprintf "%s\n(get-value (%s))"
    (check_sat ~timeout consts phi_str)
    (List.map consts ~f:Var.str |> String.concat ~sep:" ")

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

let extract_model consts z3_output_str =
  let find str = List.find consts ~f:(fun x -> String.(Var.str x = str)) in
  if is_sat z3_output_str then
    match String.split_lines z3_output_str with
    | [] -> failwith "didnt get any output from Z3"
    | sat::rst ->
      Log.smt "Removing sat response: %s" (lazy sat);
      let model_str = String.concat rst ~sep:"\n" in
      match Sexp.parse model_str with
      | Done (model,_) ->
        begin match model with
        | List assocs ->
          List.fold assocs ~init:Model.empty
            ~f:(fun model -> function
                | List [Atom x_str; Atom value_str] ->
                  begin match find x_str with
                  | None -> failwithf "Got %s from Z3, couldnt find it in constants list" x_str ()
                  | Some x ->
                    let lint_string = String.substr_replace_first value_str ~pattern:"#" ~with_:"0" in
                    Model.update model x (Bigint.of_string lint_string, Var.size x)
                  end
                | sexp ->
                  failwithf "Expected assoc pair... Could not parse %s" (Sexp.to_string sexp) ()
              )
          |> Option.some
        | _ ->
          failwithf "Expected assoc list, could not parse model %s" (Sexp.to_string model) ()
        end
      | Cont _ ->
        failwithf "Failed to parse model %s" z3_output_str ()
  else
    None
