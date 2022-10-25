open Core
open Primitives

module Make (P : Primitive) = struct

  module Cmd = struct
    type t =
      | Prim of P.t
      | Seq of t list
      | Choice of t list
    [@@deriving quickcheck, eq, sexp, compare]


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

    let rec count_asserts_aux c n =
      match c with
      | Prim p ->
        n + P.count_asserts p
      | Seq cs
      | Choice cs ->
        List.fold cs ~init:n ~f:(fun n c ->
            count_asserts_aux c n
          )

    let count_asserts c = count_asserts_aux c 0

    let rec size = function
      | Prim p -> P.size p
      | Seq cs
      | Choice cs ->
        List.fold cs ~init:(List.length cs - 1)
          ~f:(fun n c -> n + size c)

    let sequence cs =
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

    (* PRE: x is not an lvalue in c *)
    let rec subst x e c =
      match c with
      | Prim p -> Prim (P.subst x e p)
      | Seq cs ->
        List.map cs ~f:(subst x e) |> sequence
      | Choice cs ->
        List.map cs ~f:(subst x e) |> choices

    let rec normalize_names (c : t) : t =
      match c with
      | Prim p -> Prim (P.normalize_names p)
      | Seq cs ->
        List.map cs ~f:normalize_names |> sequence
      | Choice cs ->
        List.map cs ~f:normalize_names
        |> choices

    let dnf (c : t) : t =
      let rec loop c : t =
        match c with
        | Prim p -> Prim p
        | Choice chxs ->
          List.fold chxs ~init:dead ~f:(fun acc c -> choice acc (loop c))
        | Seq [] -> skip
        | Seq (s::sqs) -> begin
            match loop s, loop (sequence sqs) with
            | Choice chxs, Choice chxs_rec ->
              List.cartesian_product chxs chxs_rec
              |> List.map ~f:(Util.uncurry seq)
              |> choices
            | Choice chxs, c_rec ->
              List.map chxs ~f:(fun chx -> seq chx c_rec)
              |> choices
            | c, Choice chxs_rec ->
              List.map chxs_rec ~f:(fun chx_rec -> seq c chx_rec)
              |> choices
            | c, c_rec ->
              seq c c_rec
          end
      in
      loop c

    let rec count_paths c : Bigint.t =
      match c with
      | Prim _ ->
        Bigint.one
      | Seq cs ->
        List.fold cs ~init:Bigint.one
          ~f:(fun paths_so_far c -> Bigint.(paths_so_far * count_paths c))
      | Choice cs ->
        List.map cs ~f:(count_paths)
        |> List.reduce_exn ~f:(Bigint.(+))

    let paths (c : t) : t Sequence.t =
      Log.path_gen "building the squence of %s paths" @@ lazy (count_paths c |> Bigint.to_string);
      let rec loop (c : t) : t Sequence.t =
        let open Sequence in
        match c with
        | Prim _ ->
          return c
        | Seq cs ->
          of_list cs
          |> fold ~init:(Sequence.singleton skip)
            ~f:(fun sequence_of_paths c ->
                loop c
                |> cartesian_product sequence_of_paths
                |> map ~f:(fun (s1,s2) -> seq s1 s2))
        | Choice cs ->
          of_list cs
          |> map ~f:loop
          |> concat
      in
      loop c

    let rec const_prop_inner f c : Facts.t * t =
      match c with
      | Prim p ->
        let (f, p) = P.const_prop f p in
        (f, Prim p)
      | Seq cs ->
        let fs, cs =
          List.fold cs ~init:(f, [])
            ~f:(fun (f, cs) c ->
                let f, c = const_prop_inner f c in
                (f, cs @ [c])) in
        (fs, sequence cs)
      | Choice [] ->
        failwith "Choice of no alternatives"
      | Choice (c::cs) ->
        List.fold cs
          ~init:(const_prop_inner f c)
          ~f:(fun (fs, cs) c1 ->
              let f1, c1 = const_prop_inner f c1 in
              let fs = Facts.merge fs f1 in
              (fs , choice c1 cs))

    let const_prop c : t =
      Log.compiler_s "constant propagation";
      const_prop_inner Facts.empty c |> snd

    let rec dead_code_elim_inner reads c : (Var.Set.t * t) =
      match c with
      | Prim (p) ->
        begin match P.dead_code_elim reads p with
          | None ->
            (reads, skip)
          | Some (reads, p) ->
            (reads, prim p)
        end
      | Choice [] -> failwith "cannot have 0-ary choice"
      | Choice (c::cs) ->
        List.fold cs
          ~init:(dead_code_elim_inner reads c)
          ~f:(fun (read_by_cs, cs) c ->
              let read_by_c, c = dead_code_elim_inner reads c in
              (Var.Set.union read_by_cs read_by_c, choice cs c))
      | Seq cs ->
        let (reads, cs) =
          List.fold (List.rev cs) ~init:(reads, [])
            ~f:(fun (reads, cs) c ->
                let reads, c = dead_code_elim_inner reads c in
                (reads, c::cs)) in
        (reads, sequence cs)

    let dead_code_elim c =
      Log.compiler_s "dead code elim";
      Util.fix ~equal
        (fun c -> snd (dead_code_elim_inner Var.Set.empty c))
        c

    let optimize c =
      Log.compiler_s "optimizing...";
      let o c = dead_code_elim (const_prop c) in
      Util.fix ~equal o c

    let optimize_seq_pair (c1,c2) =
      let dce (c1,c2) =
        let (reads, c2) = dead_code_elim_inner Var.Set.empty c2 in
        let (_, c1) = dead_code_elim_inner reads c1 in
        (c1, c2)
      in
      let cp (c1, c2)=
        let (facts, c1) = const_prop_inner Facts.empty c1 in
        let (_    , c2) = const_prop_inner facts       c2 in
        (c1, c2)
      in
      let equal (c1,c2) (c1',c2') = equal c1 c1' && equal c2 c2' in
      let o (c1,c2) = dce (cp (c1,c2)) in
      Util.fix ~equal o (c1,c2)


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

    let forward ~(init:'a) ~(prim : 'a -> P.t -> 'a) ~(choices:'a list -> 'a) (c:t) =
      let rec loop acc c =
      match c with
      | Prim p -> prim acc p
      | Seq cs ->
        List.fold_left cs ~init:acc ~f:loop
      | Choice cs ->
        List.map cs ~f:(loop acc) |> choices
      in
      loop init c

    let backward ~(init:'a) ~(prim : P.t -> 'a -> 'a ) ~(choices: 'a list -> 'a) (c:t) : 'a =
      let rec loop (c : t) (acc : 'a) : 'a =
        match c with
        | Prim p -> prim p acc
        | Seq cs ->
          List.fold_right cs ~init:acc ~f:loop
        | Choice cs ->
          List.map cs ~f:(fun c -> loop c acc) |> choices
      in
      loop c init


    let vars c =
      let sorted_concat xss =
        List.concat xss
        |> Var.sort
      in
      bottom_up c
        ~prim:(Fn.compose Var.sort P.vars)
        ~sequence:sorted_concat
        ~choices:sorted_concat

    (* Monoids *)
    let zero = dead
    let ( + ) = choice
    let one = skip
    let ( * ) = seq
  end

  include Cmd

end
