open! Core

let wrap s =
  if String.mem s ' '
  then sprintf "(%s)" s
  else s

module Or_wildcard = struct
  type 'a t = 'a option [@@deriving compare]

  let sexp_of_t sexp_of = function
    | Some x -> sexp_of x
    | None -> Sexp.Atom "_"

  let t_of_sexp t_of_sexp = function
    | Sexp.Atom "_" -> None
    | x -> Some (t_of_sexp x)

  let to_caml = function
    | None -> "_"
    | Some x -> x

  let to_rocq = function
    | None -> "_"
    | Some x -> x

  let to_caml' to_caml = function
    | None -> "_"
    | Some x -> to_caml x

  let to_rocq' to_rocq = function
    | None -> "_"
    | Some x -> to_rocq x
end

module Or_wrap = struct
  type 'a t = 'a

  let sexp_of_t sexp_of x = sexp_of x

  let t_of_sexp t_of_sexp x =
    match x with
    | Sexp.List [x] -> t_of_sexp x
    | x -> t_of_sexp x
end

module Or_var = struct
  type 'a t =
    | Var of string
    | Regular of 'a
  [@@deriving compare]

  let sexp_of_t sexp_of = function
    | Var x -> Sexp.Atom x
    | Regular x -> sexp_of x

  let t_of_sexp t_of_sexp = function
    | (Sexp.Atom x') as x ->
      begin try Regular (t_of_sexp x) with _ -> Var x' end
    | x -> Regular (t_of_sexp x)

  let to_caml to_caml = function
    | Var x -> x
    | Regular x -> to_caml x

  let to_rocq to_rocq = function
    | Var x -> x
    | Regular x -> to_rocq x
end

module Node = struct
  type ws = string Or_wildcard.t [@@deriving sexp, compare]
  module T = struct
    type t =
      | Empty
      | V1 of ws * ws
      | V2 of ws * ws * ws * ws
      | V3 of ws * ws * ws * ws * ws * ws
      | Node of ws * t Or_var.t Or_wildcard.t * ws * ws * t Or_var.t Or_wildcard.t
    [@@deriving sexp, compare]
  end
  include T

  module Map = Map.Make(T)

  let rec memo_sub ~index ~(acc : int Map.t) = function
    | Empty -> index, acc
    | V1 _ | V2 _ | V3 _ as key -> 
      let index = succ index in
      index, Core.Map.set acc ~key ~data:index
    | Node (w, n1, k0, v0, n2) as n ->
      let index, acc = memo_sub' ~index ~acc n1 in
      let index, acc = memo_sub' ~index ~acc n2 in
      let index = succ index in
      index, Core.Map.set acc ~key:n ~data:index
  and memo_sub' ~index ~acc = function
    | None -> index, acc
    | Some (Regular n) -> memo_sub ~index ~acc n
    | Some (Var _) -> index, acc

  let rec to_caml ?(as_var = false) ?(memo = Map.empty) (t : t) = 
    let result_inner =
      match t with
      | Empty -> "T (Empty _)"
      | V1 (k1, v1) -> 
        sprintf "T (V1 { k1 = %s; v1 = %s})" 
          (Or_wildcard.to_caml k1) (Or_wildcard.to_caml v1)
      | V2 (k11, v11, k1, v1) ->
        sprintf "T (V2 { k11 = %s; v11 = %s; k1 = %s; v1 = %s})" 
          (Or_wildcard.to_caml k11) (Or_wildcard.to_caml v11)
          (Or_wildcard.to_caml k1) (Or_wildcard.to_caml v1)
      | V3 (k11, v11, k1, v1, k12, v12) ->
        sprintf "T (V3 { k11 = %s; v11 = %s; k1 = %s; v1 = %s; k12 = %s; v12 = %s})" 
          (Or_wildcard.to_caml k11) (Or_wildcard.to_caml v11)
          (Or_wildcard.to_caml k1) (Or_wildcard.to_caml v1)
          (Or_wildcard.to_caml k12) (Or_wildcard.to_caml v12)
      | Node (w, n1, k0, v0, n2) ->
        sprintf "T (Node { weight = %s; n1 = %s; k0 = %s; v0 = %s; n2 = %s})"
          (Or_wildcard.to_caml w)
          (Or_wildcard.to_caml' (Or_var.to_caml (to_caml ~as_var ~memo)) n1)
          (Or_wildcard.to_caml k0)
          (Or_wildcard.to_caml v0)
          (Or_wildcard.to_caml' (Or_var.to_caml (to_caml ~as_var ~memo)) n2)
    in
    match as_var, Core.Map.find memo t with
    | false, Some index -> sprintf "t_%d" index
    | true, Some index -> sprintf "(%s as t_%d)" result_inner index
    | _ -> result_inner

  let rec to_rocq = function
    | Empty -> "Empty"
    | V1 (k1, v1) ->
      sprintf "V1 %s %s"
        (wrap (Or_wildcard.to_rocq k1))
        (wrap (Or_wildcard.to_rocq v1))
    | V2 (k11, v11, k1, v1) ->
      sprintf "V2 %s %s %s %s"
        (wrap (Or_wildcard.to_rocq k11))
        (wrap (Or_wildcard.to_rocq v11))
        (wrap (Or_wildcard.to_rocq k1))
        (wrap (Or_wildcard.to_rocq v1))
    | V3 (k11, v11, k1, v1, k12, v12) ->
      sprintf "V3 %s %s %s %s %s %s"
        (wrap (Or_wildcard.to_rocq k11))
        (wrap (Or_wildcard.to_rocq v11))
        (wrap (Or_wildcard.to_rocq k1))
        (wrap (Or_wildcard.to_rocq v1))
        (wrap (Or_wildcard.to_rocq k12))
        (wrap (Or_wildcard.to_rocq v12))
    | Node (w, n1, k0, v0, n2) ->
      sprintf "Node %s %s %s %s %s"
        (wrap (Or_wildcard.to_rocq w))
        (wrap (Or_wildcard.to_rocq' (Or_var.to_rocq to_rocq) n1))
        (wrap (Or_wildcard.to_rocq k0))
        (wrap (Or_wildcard.to_rocq v0))
        (wrap (Or_wildcard.to_rocq' (Or_var.to_rocq to_rocq) n2))
end

module Line = struct
  type t = Node.t Or_wrap.t * Node.t Or_wrap.t * Node.t Or_wrap.t [@@deriving sexp]

  let to_caml (n1, n2, nres) =
    let index, memo = Node.memo_sub ~index:0 ~acc:Node.Map.empty n1 in
    let index, memo = Node.memo_sub ~index ~acc:memo n2 in
    let index, memo' = Node.memo_sub ~index ~acc:Node.Map.empty nres in
    let memo = Core.Map.filter_keys memo ~f:(Core.Map.mem memo') in
    Printf.sprintf "  | %s\n  , %s ->\n    %s"
      (Node.to_caml ~as_var:true ~memo n1)
      (Node.to_caml ~as_var:true ~memo n2)
      (Node.to_caml ~as_var:false ~memo nres)

  let to_rocq (n1, n2, nres) =
    Printf.sprintf "  | %s eq:_\n  , %s eq:_ :=\n    %s"
      (Node.to_rocq n1)
      (Node.to_rocq n2)
      (Node.to_rocq nres)

  let to_rocq_boolean ?(value = true)(n1, n2, _) =
    Printf.sprintf "  | %s, %s => %s"
      (Node.to_rocq n1)
      (Node.to_rocq n2)
      (if value then "True" else "False")
end


let%expect_test _ =
  let input =
    Sexp.of_string_conv_exn
      {|
((V1 k1 v1)
 (Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222))
 (Node 8 (V3 k1 v1 k0 v0 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)))
    |}
      [%of_sexp: Line.t]
  in
  print_endline (Line.to_caml input);
  [%expect {|
    | T (V1 { k1 = k1; v1 = v1})
    , T (Node { weight = _; n1 = T (V1 { k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (V3 { k11 = k221; v11 = v221; k1 = k22; v1 = v22; k12 = k222; v12 = v222}) as t_3)}) ->
      T (Node { weight = 8; n1 = T (V3 { k11 = k1; v11 = v1; k1 = k0; v1 = v0; k12 = k21; v12 = v21}); k0 = k2; v0 = v2; n2 = t_3})
    |}];
  print_endline (Line.to_rocq input);
  [%expect {|
    | V1 k1 v1 eq:_
    , Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) eq:_ :=
      Node 8 (V3 k1 v1 k0 v0 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)
    |}];
  ()

