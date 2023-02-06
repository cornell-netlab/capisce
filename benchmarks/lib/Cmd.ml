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

    let rec bottom_up ~prim ~sequence ~choices (c : t) =
      let f = bottom_up ~prim ~sequence ~choices in
      match c with
      | Prim p -> prim p
      | Seq cs -> sequence @@ List.map cs ~f
      | Choice cs -> choices @@ List.map cs ~f


    let rec top_down ~init ~prim ~sequence ~choices (c : t) =
      let f acc = top_down ~init:acc ~prim ~sequence ~choices in
      match c with
      | Prim p -> prim init p
      | Seq cs ->
        sequence init cs f
      | Choice cs ->
        choices init cs f

    let forward ~(init:'a) ~(prim : 'a -> P.t -> 'a) ~(choices:'a list -> 'a) (c : t) =
      top_down c
        ~init
        ~prim
        ~choices:(fun acc cs recursive_call ->
            List.map cs ~f:(recursive_call acc)
            |> choices
          )
        ~sequence:(fun acc cs recursive_call ->
            List.fold cs ~init:acc ~f:(fun acc c ->
                recursive_call acc c
              )
          )
      (* let rec loop acc c = *)
      (* match c with *)
      (* | Prim p -> prim acc p *)
      (* | Seq cs -> *)
      (*   List.fold_left cs ~init:acc ~f:loop *)
      (* | Choice cs -> *)
      (*   List.map cs ~f:(loop acc) |> choices *)
      (* in *)
      (* loop init c *)

    let backward ~(init:'a) ~(prim : P.t -> 'a -> 'a ) ~(choices: 'a list -> 'a) (c:t) : 'a =
      let rec loop (c : t) (acc : 'a) : 'a =
        match c with
        | Prim p ->
          Log.debug "[backward] prim %s" @@ lazy (P.to_smtlib p);
          prim p acc
        | Seq cs ->
          Log.debug_s "[sequence]";
          List.fold_right cs ~init:acc ~f:loop
        | Choice cs ->
          Log.debug_s "[choice]";
          List.map cs ~f:(fun c -> loop c acc) |> choices
      in
      loop c init


    let vars c =
      bottom_up c
        ~prim:(Fn.compose Var.Set.of_list P.vars)
        ~sequence:Var.Set.union_list
        ~choices:Var.Set.union_list
      |> Var.Set.to_list

    (* Monoids *)
    let zero = dead
    let ( + ) = choice
    let one = skip
    let ( * ) = seq
  end

  include Cmd

end
