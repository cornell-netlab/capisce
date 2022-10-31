open Core
open Primitives

module Hornet : Primitive = struct

  type t =
    | Pipeline of Pipeline.t
    | DepAsst of { heap_variable: string;
                   index : int;
                   refinement : Assert.t }
  [@@deriving quickcheck, sexp, eq, compare, hash]

  let assume phi = Pipeline (Pipeline.assume phi)
  let assert_ phi = Pipeline (Pipeline.assert_ phi)
  let contra c1 c2 =
    match c1, c2 with
    | Pipeline p1, Pipeline p2 -> Pipeline.contra p1 p2
    | _, _ -> false

  let to_smtlib = function
    | Pipeline p -> Pipeline.to_smtlib p
    | DepAsst x ->
      Printf.sprintf "{ %s | %s }"
        x.heap_variable
        (Assert.to_smtlib x.refinement)

  let size = function
    | Pipeline p -> Pipeline.size p
    | DepAsst asst ->
      1 + Assert.size asst.refinement

  let vars = function
    | Pipeline p -> Pipeline.vars p
    | DepAsst _ -> []

  (* let name = function *)
  (*   | Pipeline p -> Pipeline.name p *)
  (*   | DepAsst asst -> Printf.sprintf "DEPASST %s" asst.heap_variable *)

  (* let subst x e = function *)
  (*   | Pipeline p -> *)
  (*     Pipeline (Pipeline.subst x e p) *)
  (*   | DepAsst asst -> *)
  (*     DepAsst {asst with *)
  (*              refinement = BExpr.subst x e asst.refinement *)
  (*             } *)

  (* let const_prop facts = function *)
  (*   | Pipeline p -> *)
  (*     let facts, p = Pipeline.const_prop facts p in *)
  (*     (facts, Pipeline p) *)
  (*   | DepAsst asst -> *)
  (*     facts, *)
  (*     DepAsst { *)
  (*       asst with *)
  (*       refinement = *)
  (*         BExpr.fun_subst (Facts.lookup facts) asst.refinement *)
  (*         |> BExpr.simplify *)
  (*     } *)

  (* let explode c = *)
  (*   match c with *)
  (*   | Pipeline p -> *)
  (*     Pipeline.explode p *)
  (*     |> Util.mapmap ~f:(fun p -> Pipeline p) *)
  (*   | DepAsst _ -> *)
  (*     [[c]] *)

  (* let dead_code_elim reads c = *)
  (*   let open Option.Let_syntax in *)
  (*   match c with *)
  (*   | Pipeline p -> *)
  (*     let%map reads, p = Pipeline.dead_code_elim reads p in *)
  (*     (reads, Pipeline p) *)
  (*   | DepAsst {heap_variable=_; index=_; refinement} -> *)
  (*     let reads = Var.Set.of_list @@ Assert.vars refinement in *)
  (*     Some (reads, c) *)

  (* let normalize_names = function *)
  (*   | Pipeline p -> *)
  (*     Pipeline (Pipeline.normalize_names p) *)
  (*   | DepAsst {heap_variable; index; refinement}-> *)
  (*     DepAsst { *)
  (*       heap_variable; *)
  (*       index; *)
  (*       refinement = *)
  (*         BExpr.normalize_names refinement *)
  (*     } *)

end
