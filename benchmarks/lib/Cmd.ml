open Core
open Primitives

module Make (P : Primitive) = struct

  module Cmd = struct
    type t =
      | Prim of P.t
      | Seq of t list
      | Choice of t list
    [@@deriving quickcheck, eq, sexp, compare, hash]


    module PSet = Set.Make (P)
    module PMap = Map.Make (P)
    module PHash_set = Hash_set.Make (P)
    module PHashtbl = Hashtbl.Make (P)

    let assume phi = Prim (P.assume phi)
    let assert_ phi = Prim (P.assert_ phi)
    let skip = Prim (P.assume BExpr.true_)
    let pass = Prim (P.assert_ BExpr.true_)
    let dead = Prim (P.assume BExpr.false_)
    let abort = Prim (P.assert_ BExpr.false_)

    let prim p = Prim p

    let is_mult_unit p = equal skip p || equal pass p
    let is_mult_annihil p = equal dead p || equal abort p

    let is_add_unit p = equal dead p
    let is_add_annihil p = equal abort p

    (* let get_prim = function *)
    (*   | Prim p -> Some p *)
    (*   | _ -> None *)

    (* let get_seq = function *)
    (*   | Seq cs -> Some cs *)
    (*   | _ -> None *)

    (* let get_choice = function *)
    (*   | Choice cs -> Some cs *)
    (*   | _ -> None *)

    let contra c1 c2 = match c1, c2 with
      | Prim p1, Prim p2 -> P.contra p1 p2
      | _, _ -> false

    let rec to_string_aux indent (c : t) : string =
      let open Printf in
      let space = Util.space indent in
      match c with
      | Prim p ->
        sprintf "%s %s" space (P.to_smtlib p)
      | Seq cs ->
        List.map cs ~f:(to_string_aux indent)
        |> String.concat ~sep:(sprintf ";\n")
      | Choice cs ->
        List.map cs
          ~f:(fun c ->
              sprintf "{\n%s\n%s}" (to_string_aux (indent+2) c) space)
        |> String.concat ~sep:(sprintf " [] ")
        |> Printf.sprintf "%s%s" space

    let to_string = to_string_aux 0

    let rec size = function
      | Prim p -> P.size p
      | Seq cs
      | Choice cs ->
        (*List.length cs - 1 + *) List.sum (module Int) ~f:size cs
        (* List.fold cs ~init:(List.length cs - 1) *)
        (*   ~f:(fun n c -> n + size c) *)

    let flatten_seqs cs : t list =
      let open List.Let_syntax in
      let%bind c = cs in
      match c with
      | Choice _  | Prim _ ->
        return c
      | Seq cs -> cs

    let sequence cs =
      let cs = flatten_seqs cs in
      let cs = List.filter cs ~f:(Fn.non is_mult_unit) in
      let cs = List.remove_consecutive_duplicates cs ~which_to_keep:`First ~equal in
      match List.find cs ~f:is_mult_annihil with
      | Some p -> p
      | None ->
        if List.exists2_exn cs cs ~f:(contra) then
          abort
        else
          match cs with
          | [] -> skip
          | [c] -> c
          | _ -> Seq cs

    let sequence_opt cs =
      Util.commute cs
      |> Option.map ~f:sequence

    let seq c1 c2 =
      match c1, c2 with
      | Seq c1s, Seq c2s ->
        c2s
        |> List.rev_append @@ List.rev c1s
        |> sequence
      | Seq c1s, _ ->
        List.rev c1s
        |> List.cons c2
        |> List.rev
        |> sequence
      | _, Seq c2s ->
        c1 :: c2s
        |> sequence
      | _, _ ->
        sequence [c1; c2]

    let choices cs : t =
      if List.is_empty cs then
        failwith "[Cmd.choices] cannot construct 0-ary choice"
      else
        let cs = List.filter cs ~f:(Fn.non is_add_unit) in
        if List.is_empty cs then
          (* all paths are dead *)
          dead
        else if List.exists cs ~f:(is_add_annihil) then
          abort
        else
          begin
            match List.dedup_and_sort cs ~compare with
            | [c] -> c
            | cs -> Choice cs
          end

    let choices_opt cs : t option =
      Util.commute cs
      |> Option.map ~f:choices


    let choice c1 c2 =
      match c1, c2 with
      | Choice c1s, Choice c2s ->
        choices (List.rev_append c1s c2s)
      | Choice c1s, _ ->
        choices (c1s @ [c2])
      | _, Choice c2s ->
        choices (c1 :: c2s)
      | _, _ ->
        choices [c1;c2]

    let choice_seq cs1 cs2 = choice (sequence cs1) (sequence cs2)

    let choice_seqs cs = List.map cs ~f:sequence |> choices

    (**/ END Smart Constructors*)

    let is_primitive (c : t) =
      match c with
      | Prim _ -> true
      | _ -> false

    let vars c =
      let rec vars_set = function
        | Prim p -> P.vars p |> Var.Set.of_list
        | Seq cs -> List.map cs ~f:vars_set |> Var.Set.union_list
        | Choice cs -> List.map cs ~f:vars_set |> Var.Set.union_list
      in
      vars_set c |> Var.Set.to_list

    (* Monoids *)
    let zero = dead
    let ( + ) = choice
    let one = skip
    let ( * ) = seq
  end

  include Cmd

end
