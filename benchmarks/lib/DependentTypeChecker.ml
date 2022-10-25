open Core
open Primitives

module Ho4reNet : Primitive = struct

  type t =
    | Pipeline of Pipeline.t
    | DepAsst of { heap_variable: string;
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

  let count_asserts = function
    | Pipeline p -> Pipeline.count_asserts p
    | DepAsst _ -> 1

  let size = function
    | Pipeline p -> Pipeline.size p
    | DepAsst asst ->
      1 + Assert.size asst.refinement

  let comparisons = function
    | Pipeline p -> Pipeline.comparisons p
    | DepAsst _ -> None

  let is_node = function
    | Pipeline p -> Pipeline.is_node p
    | DepAsst _ -> true

  let name = function
    | Pipeline p -> Pipeline.name p
    | DepAsst asst -> Printf.sprintf "DEPASST %s" asst.heap_variable

  let is_table = function
    | Pipeline p -> Pipeline.is_table p
    | DepAsst _ -> false

  let vars = function
    | Pipeline p -> Pipeline.vars p
    | DepAsst _ -> []

  let subst x e = function
    | Pipeline p ->
      Pipeline (Pipeline.subst x e p)
    | DepAsst asst ->
      DepAsst {asst with
               refinement = BExpr.subst x e asst.refinement
              }

  let const_prop facts = function
    | Pipeline p ->
      let facts, p = Pipeline.const_prop facts p in
      (facts, Pipeline p)
    | DepAsst {heap_variable; refinement} ->
      facts,
      DepAsst {
        heap_variable;
        refinement =
          BExpr.fun_subst (Facts.lookup facts) refinement
          |> BExpr.simplify
      }

  let explode c =
    match c with
    | Pipeline p ->
      Pipeline.explode p
      |> Util.mapmap ~f:(fun p -> Pipeline p)
    | DepAsst _ ->
      [[c]]

  let dead_code_elim reads c =
    let open Option.Let_syntax in
    match c with
    | Pipeline p ->
      let%map reads, p = Pipeline.dead_code_elim reads p in
      (reads, Pipeline p)
    | DepAsst {heap_variable=_; refinement} ->
      let reads = Var.Set.of_list @@ Assert.vars refinement in
      Some (reads, c)

  let normalize_names = function
    | Pipeline p ->
      Pipeline (Pipeline.normalize_names p)
    | DepAsst {heap_variable; refinement}->
      DepAsst {
        heap_variable;
        refinement =
          BExpr.normalize_names refinement
      }

end
