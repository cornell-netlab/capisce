open Core
open ASTs

module Header = struct 
  type t = {
    name : string;
    fields : (string * int) list;
  }

  let is x = String.is_prefix (Var.str x) ~prefix:"hdr."
  let is_valid x = is x && String.is_suffix (Var.str x) ~suffix:"isValid"

  let get_headers : Var.t list -> t String.Map.t =
    List.fold ~init:String.Map.empty ~f:(fun hdrs x -> 
      match String.chop_prefix (Var.str x) ~prefix:"hdr." with 
      | None -> hdrs
      | Some x_rst -> 
        match String.lsplit2 x_rst ~on:'.' with 
        | None -> 
          failwithf "Dont know how to get header of %s" (Var.str x) ()
        | Some (_, field) when String.(field = "isValid") ->
          hdrs
        | Some (hdr_name, field) -> 
          String.Map.update hdrs hdr_name ~f:(function
          | None -> {name= hdr_name; fields = [
            field, Var.size x;
            ]
          }
          | Some {name; fields} -> 
            assert (String.(name = hdr_name));
            if List.exists fields ~f:(fun (f, _) -> String.(f = field)) then 
              {name; fields}
            else
              {name; fields = 
                (field, Var.size x)::fields
              }
          )
    )

  let emit_header_types (headers : t String.Map.t) = 
    String.Map.fold headers ~init:"" ~f:(fun ~key ~data emission -> 
      assert String.(key = data.name);
      List.map data.fields ~f:(fun (f, w) -> 
        Printf.sprintf "  bit<%d> %s;" w f
      )
      |> String.concat ~sep:"\n"
      |> Printf.sprintf "%s\nheader %s_t {\n%s\n}" emission data.name
    )

  let emit_headers_struct struct_name (headers : t String.Map.t) =
    String.Map.keys headers
    |> List.map ~f:(fun header_name -> Printf.sprintf "  %s_t %s;" header_name header_name)
    |> String.concat ~sep:"\n"
    |> Printf.sprintf "struct %s {\n%s\n}\n" struct_name
end

module Metadata = struct
  type t = {
    name : string;
    meta : (string * t) list;
    fields : (string * int) list;
  }

  let empty name = {name; meta = []; fields = []}

  let is x = String.is_prefix (Var.str x) ~prefix:"meta."
  let is_standard x = String.is_prefix (Var.str x) ~prefix:"standard_metadata."

  let has_field m x = 
    List.exists m.fields ~f:(fun (y, _) -> 
      String.(x = y)
    )
  
  let has_nested_metadata m nested =
    List.exists m.meta ~f:(fun  (nested', _) -> 
      String.(nested = nested') 
    )

  let rec get_metadata name xs : t =
    List.fold xs ~init:(empty name) ~f:(fun metadata x -> 
      match String.chop_prefix (Var.str x) ~prefix:(name ^ ".") with 
      | None -> metadata 
      | Some field -> 
        if String.contains field '.' then 
          let (submeta, _) = String.lsplit2_exn field ~on:'.' in 
          get_metadata (name ^ "." ^ submeta) xs
        else if has_field metadata field then
          metadata
        else 
          { metadata with 
            fields = 
            (field, Var.size x)::metadata.fields
          }
    )

  let emit_metadata metadata = 
    let rec loop typename m = 
      let nested_metadata = 
        List.map m.meta ~f:(fun (name, _) -> 
          Printf.sprintf "  %s_t %s;\n" name name
        )
        |> String.concat ~sep:""
      in
      let fields =
        List.map m.fields ~f:(fun (name, w) -> 
          Printf.sprintf "  bit<%d> %s;\n" w name
        ) 
        |> String.concat ~sep:""
      in
      let preceeding = 
        List.map m.meta ~f:(fun (name, m) -> 
          loop (Printf.sprintf "%s_t" name) m
        )
        |> String.concat ~sep:""
      in
      Printf.sprintf {|
%s
struct %s {
%s
%s
}|} preceeding typename nested_metadata fields
    in
    loop "my_metadata_t" metadata
    

end

module Parser = struct
  (* Constructs a parser, starting at state "start", and
    ending at either "accept" or "reject" *)
  type state_name = string
  type transition = 
    { 
      discriminee : Expr.t list;
      cases : (Expr.t list * state_name) list;
      default : state_name
    }

  let select x cases default =
    { discriminee = [Expr.var x];
      cases = List.map cases ~f:(fun (e, st) -> [e], st);
      default
    }

  let default default =
    { discriminee = []; cases = []; default}

  type state = {
    name : state_name;
    body : GCL.t;
    transition : transition
  }

  type t = state String.Map.t

  let of_state_list = 
    List.fold ~init:String.Map.empty
    ~f:(fun prsr state -> 
      String.Map.set prsr ~key:state.name ~data:state
    )

  let vars (prsr : t) : Var.t list =
    let transition_vars {discriminee;cases; default=_} =
      let concat f e = let a, b = f e in a @ b in
      let discriminee_vars =
        List.bind discriminee ~f:(concat Expr.vars)
      in 
      let cases_vars = 
        List.bind cases ~f:(fun (es, _) -> List.bind es ~f:(concat Expr.vars))
      in
      discriminee_vars @ cases_vars
    in
    let state_vars (state : state) =
      GCL.vars state.body
      @ transition_vars state.transition
    in
    String.Map.data prsr
    |> List.bind ~f:state_vars
    |> List.dedup_and_sort ~compare:Var.compare

  let unroll_index unroll_map unroll name =
    (* unroll_map contains the number of times 
       each step can occur in the state machine.
     *)
    String.Map.find unroll_map name
    |> Option.value ~default:unroll 

  let decr unroll_map unroll (name : state_name) =
   (* Each time a state occurs, its entry in unroll_map
      is decremented.
    *)
    let new_unroll = 
      unroll_index unroll_map unroll name - 1
    in
    String.Map.set unroll_map ~key:name ~data:new_unroll

  let invalidate_headers psm = 
    vars psm 
    |> List.filter ~f:(Header.is)
    |> List.filter ~f:(Header.is_valid)
    |> List.map ~f:(fun hdr_is_valid -> GCL.assign hdr_is_valid Expr.(bvi 0 1))
    |> GCL.sequence

  let to_gcl unroll (parser : t) : GCL.t =
    let parse_result = Var.make "parse_result" 1 in 
    let accept = Expr.bvi 1 1 in 
    let reject = Expr.bvi 0 1 in 
    let rec inline (unroll_map : int String.Map.t) (st : state)=
      let unroll_map = decr unroll_map unroll st.name in 
      GCL.sequence [
        st.body;
        inline_transition unroll_map st.transition
      ]
    and inline_transition unroll_map {discriminee;cases;default} =
      let inline_next_state st = 
        if String.(st = "accept") then
          GCL.assign parse_result accept
        else if String.(st = "reject") then 
          GCL.assign parse_result reject
        else
          inline unroll_map (String.Map.find_exn parser st)
      in
      match discriminee with 
      | [] -> 
        inline_next_state default
      | queries -> 
        List.fold_right cases 
        ~init:(inline_next_state default)
        ~f:(fun (tests, next_state) else_ -> 
          let cond = BExpr.ands_ @@ List.map2_exn tests queries ~f:(BExpr.eq_) in
          let then_ = inline_next_state next_state in 
          GCL.ite cond then_ else_
        )
    in
    GCL.sequence [
      invalidate_headers parser;
      String.Map.find_exn parser "start"
      |> inline String.Map.empty 
    ]
  let emit_parser_state {name; body; transition} : string = 
    let rec emit_parser_body gcl =
      let open GCL in 
      match gcl with 
      | Prim p -> 
        begin match p.data with 
        | Assign (x,e) -> 
          begin match String.chop_suffix (Var.str x) ~suffix:".isValid" with 
          | Some hdr -> 
            Printf.sprintf "    packet.extract(%s);" hdr
          | None -> 
            Printf.sprintf "    %s = %s;" (Var.str x) (Expr.emit_p4 e)
          end 
        | Passive _ -> 
          failwith "unexpected parser passive"
        end
      | Seq cs -> 
        List.map cs ~f:emit_parser_body 
        |> String.concat ~sep:"\n"
      | Choice _ -> failwith "unexpected choice"
    in
    let emit_transition transition =
      match transition.discriminee with 
      | [] -> 
        Printf.sprintf "transition %s;" transition.default
      | queries -> 
        let emit_tuple es = List.map es ~f:(Expr.emit_p4) |> String.concat ~sep:"," in
        let cases = 
          List.map transition.cases ~f:(fun (tests, state) -> 
            Printf.sprintf "      (%s) : %s;" (emit_tuple tests) state
          )
          |> String.concat ~sep:"\n"
        in
        Printf.sprintf "transition select(%s){\n%s\n      default : %s;\n    }\n" 
          (emit_tuple queries) cases transition.default
    in
    Printf.sprintf {|
  state %s {
%s
    %s
  }
    |} name (emit_parser_body body) (emit_transition transition)

  let emit_p4 parser_name parser =
    String.Map.fold parser ~init:"" 
      ~f:(fun ~key:_ ~data:state acc -> 
          emit_parser_state state
          |> Printf.sprintf "%s\n%s" acc
        )
    |> Printf.sprintf {|
parser %s(
  packet_in packet,
  out my_headers_t hdr,
  out my_metadata_t meta,
  inout standard_metadata_t standard_metadata)
{
%s
}
|} parser_name
end


let tabwidth = 2

let emit_p4_control control_name (gpl : GPL.t) : string =
  let indent numtabs = String.init (tabwidth * numtabs) ~f:(fun _ -> ' ') in 
  let rec loop (offset : int) (gpl : GPL.t) = 
    match gpl with
    | Seq cs -> 
      List.map cs ~f:(loop offset) |> 
      String.concat ~sep:"\n"
    | Choice [
        (Prim (Active ({data=Passive (Assume phi);alt = _})));
        Seq ((Prim (Active ({data=Passive (Assume nphi);alt = _})))::flss)
    ] when BExpr.(equal (not_ phi) nphi) || BExpr.(equal phi (not_ nphi)) -> 
      let flss_str = loop (offset + 1) (Seq flss) in 
      Printf.sprintf "%sif (%s) {} else {\n%s\n%s}\n" (indent offset) 
        (BExpr.emit_p4 phi)
        flss_str
        (indent offset)
    | Choice [
      Seq ((Prim (Active ({data=Passive (Assume phi);alt = _})))::trus);
      Seq ((Prim (Active ({data=Passive (Assume nphi);alt = _})))::flss)
      ] when BExpr.(equal (not_ phi) nphi) || BExpr.(equal phi (not_ nphi)) -> 
        let trus_str = loop (offset + 1) (Seq trus) in 
        let flss_str = loop (offset + 1) (Seq flss) in 
        Printf.sprintf "%sif (%s) {\n%s\n%s} else {\n%s\n%s}\n" (indent offset) 
          (BExpr.emit_p4 phi)
          trus_str
          (indent offset)
          flss_str
          (indent offset)
    | Choice cs ->
      List.iter cs ~f:(fun c -> Printf.printf "%s\n------\n%!" (GPL.to_string c));
      failwith "unrecognized [] between the above"
    | Prim (Active ({data=Assign (x,e);alt=_})) when Header.is x && Header.is_valid x -> 
      let hdr = String.chop_suffix_exn (Var.str x) ~suffix:".isValid" in
      if Expr.is_one e then 
        Printf.sprintf "%s%s.setValid();" (indent offset) hdr
      else if Expr.is_zero e then 
        Printf.sprintf "%s%s.setInvalid();" (indent offset) hdr
      else 
        failwith "Don't know what to do when assigning a header to a funky value"
    | Prim (Active ({data=Assign (x,e);alt=_})) ->
      Printf.sprintf "%s%s = %s;" (indent offset) 
        (Var.str x)
        (Expr.emit_p4 e)
    | Prim (Active ({data=Passive (Assume phi); alt=_})) -> 
      Log.warn "[EmitP4] Skipping raw assume %s" @@ lazy (BExpr.to_smtlib phi);
      ""
    | Prim (Active ({data=Passive (Assert phi);alt=_})) ->
      Log.warn "[EmitP4] Skipping raw assert %s" @@ lazy (BExpr.to_smtlib phi);
      ""
    | Prim (Table table) ->
      Printf.sprintf "%s%s.apply();" (indent offset) table.name;
  in 
  let variable_definitions =
    let local_vars = 
      GPL.vars gpl
      |> List.filter ~f:(fun x -> not (Header.is x || Metadata.is x || Metadata.is_standard x))
    in
    List.fold local_vars ~init:"" ~f:(fun acc x ->
      Printf.sprintf "%s  bit<%d> %s;\n"acc (Var.size x) (Var.str x)
    )
  in
  let string_of_kind = 
    let open Primitives.Table in function 
    | Maskable -> "ternary"
    | Exact | MaskableDegen -> "exact"
  in
  let action_definitions =
    List.bind (GPL.tables gpl) ~f:(fun table -> 
      List.mapi table.actions ~f:(fun i (params, body) -> 
        let gpl_body = List.map body ~f:GPL.active |> GPL.sequence in 
        let params = List.map params ~f:(fun x ->
          Printf.sprintf "bit<%d> %s" (Var.size x) (Var.str x)
        ) |> String.concat ~sep:","
        in
        Printf.sprintf "  action %s_action_%d(%s){\n%s\n  }\n" table.name i params
          (loop 2 gpl_body)
      )
    ) |> String.concat ~sep:"\n"
  in
  let table_definitions =
    let open List.Let_syntax in 
    let%map table = GPL.tables gpl in 
    let keys = 
      List.map table.keys ~f:(fun (key, kind) ->
        Printf.sprintf "\n      %s : %s;" (Expr.(emit_p4 (var key))) (string_of_kind kind)
      )
      |> String.concat
    in
    let actions = 
      List.mapi table.actions ~f:(fun i _ -> 
        Printf.sprintf "\n      %s_action_%d;" table.name i
      )
      |> String.concat
    in
    Printf.sprintf
    {|
  table %s {
    key = {%s
    }
    actions = {%s
    }
  }
    |} table.name keys actions

  in
  Printf.sprintf {|
control %s (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  // Variable Definitions
%s
  // Action Definitions
%s
  // Table Definitions
%s

  apply {
    // Pipeline
%s
  }
}
  |}
  (control_name)
  (variable_definitions)
  (action_definitions)
  (String.concat table_definitions)
  (loop 2 gpl)

let emit_headers psm ing eg =
  let all_vars =
    Parser.vars psm @ GPL.vars ing @ GPL.vars eg
    |> List.dedup_and_sort ~compare:Var.compare
  in
  let headers = Header.get_headers all_vars in 
  Printf.sprintf {|
// Define header types
%s
// Assemble headers in a single struct
%s
  |}
  (Header.emit_header_types headers)
  (Header.emit_headers_struct "my_headers_t" headers)

let emit_metadata psm ing eg =
  let all_vars =
    Parser.vars psm @ GPL.vars ing @ GPL.vars eg
    |> List.dedup_and_sort ~compare:Var.compare
  in 
  let metadata = Metadata.get_metadata "meta" all_vars in
  Metadata.emit_metadata metadata

let emit parser_state_machine ingress egress =
  Printf.sprintf
  {|
#include <core.p4>
#include <v1model.p4>  
// HEADERS
%s
// METADATA
%s
// PARSER
%s
// INGRESS
%s
// EGRESS
%s
// OTHER
control MyVerifyChecksum(
    inout my_headers_t   hdr,
    inout my_metadata_t  meta)
{
    apply {     }
}

control MyComputeChecksum(
    inout my_headers_t  hdr,
    inout my_metadata_t meta)
{
    apply {   }
}
control MyDeparser(
    packet_out      packet,
    in my_headers_t hdr)
{
    apply {
    }
}
V1Switch(
    MyParser(),
    MyVerifyChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;
  |}
  (emit_headers parser_state_machine ingress egress)
  (emit_metadata parser_state_machine ingress egress)
  (Parser.emit_p4 "MyParser" parser_state_machine)
  (emit_p4_control "MyIngress" ingress)
  (emit_p4_control "MyEgress" egress)
