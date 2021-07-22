open Core

module VarMap = Map.Make(Var)
          
type t = int VarMap.t

let label = Printf.sprintf "%s___%i"
       
let init (fvs : Var.t list) : t =
  List.fold fvs ~init:VarMap.empty ~f:(fun s v -> VarMap.add_exn s ~key:v ~data:0)
       
let to_vsub_list (s : t) : (Var.t * Var.t) list =
  VarMap.fold s ~init:[] ~f:(fun ~key ~data acc ->
      let k' = label (Var.str key) data in
      let key' = Var.(make k' (size key)) in 
      (key, key') :: acc)

let incr (s_opt : t option) x : (Var.t * t) option =
  let open Option.Let_syntax in
  let%map s = s_opt in
  let i' = ref 0 in
  let s' =
    VarMap.update s x
      ~f:(function
        | None -> failwith (Printf.sprintf "couldn't find %s to increment" (Var.str x))
        | Some i ->
           i':= i+1;
           !i')
  in
  (Var.make (label (Var.str x) (!i')) (Var.size x), s')      

let symm_diff (s1 : t) (s2 : t) : t =
  let open VarMap in
  fold_symmetric_diff s1 s2 ~init:empty
    ~data_equal:(=)
    ~f:(fun acc -> function
      | _, `Left _ -> failwith "element in left but not right"
      | _, `Right _ -> failwith "element in right but not left"
      | key, `Unequal (idx1,idx2) -> set acc ~key ~data:(max idx1 idx2))
                                   
let sync (s : t) (diff : t) : (Var.t * Var.t) list =
  VarMap.fold diff ~init:[]
    ~f:(fun ~key ~data acc ->
      let old_idx = VarMap.find_exn s key in
      if old_idx = data then
        acc
      else
        let old_var = Var.(make (label (Var.str key) old_idx) (Var.size key)) in
        let new_var = Var.(make (label (Var.str key) data) (Var.size key)) in
        (old_var, new_var) :: acc)

let max (s1 : t) (s2 : t) : t =
  let open VarMap in
  merge s1 s2
    ~f:(fun ~key:_ -> function
      | `Both (idx1,idx2) ->
         Some (max idx1 idx2)
      | `Left idx1 -> Some idx1
      | `Right idx2 -> Some idx2           
    )
