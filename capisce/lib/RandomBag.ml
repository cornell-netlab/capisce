open Core

module Make (Elt : Set_intf.Elt) = struct

  module S = Set.Make(struct
      type t = (int * Elt.t)
      [@@deriving compare, sexp]
    end)

  type t = S.t ref

  let create () : t = ref S.empty

  let push (bag : t) (x : Elt.t) : unit =
    let idx = Random.int 1000 in
    bag := S.add !bag (idx, x)

  let pop (bag : t) : Elt.t option =
    let open Option.Let_syntax in
    let%map (idx, value) = S.choose !bag in
    bag := S.remove !bag (idx, value);
    value

end
