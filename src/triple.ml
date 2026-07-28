open Sexplib0.Sexp_conv

(* References:

   We don't use the Grandchild Scheme, but [1] is very helpful.

   [1] Vincent Jugé. Grand-children weight-balanced binary search trees
   https://arxiv.org/abs/2410.08825

   [2] Straka, M. (2012). Adams’ Trees Revisited. In: Peña, R., Page, R. (eds) Trends in Functional Programming. TFP 2011. Lecture Notes in Computer Science, vol 7193. Springer, Berlin, Heidelberg. https://doi.org/10.1007/978-3-642-32037-8_9

   [3] Blelloch, Guy E., et al. “Just Join for Parallel Ordered Sets.” Proceedings of the 28th ACM Symposium on Parallelism in Algorithms and Architectures, edited by , ACM, 2016, pp. 253–64. Spaa ’16. Crossref, https://doi.org/10.1145/2935764.2935768.

   [4] Y. HIRAI and K. YAMAMOTO, “Balancing weight-balanced trees,” Journal of Functional Programming, vol. 21, no. 3, pp. 287–307, 2011. doi:10.1017/S0956796811000104 
*)

module Comparison = struct
  type t = Lt |Eq | Gt
end

module type Ordered = sig
  type t
  val compare: t -> t -> Comparison.t
end

module type StandardOrdered = sig
  type t
  val compare: t -> t -> int
end

(* From base *)
module Non_short_circuiting : sig
  val (||) : bool -> bool -> bool
  val (&&) : bool -> bool -> bool

end = struct
  external to_int : bool -> int = "%identity"
  external unsafe_of_int : int -> bool = "%identity"

  let ( || ) a b = unsafe_of_int (to_int a lor to_int b)
  let ( && ) a b = unsafe_of_int (to_int a land to_int b)
end

module [@inline always] OrderedOfStandard (X : StandardOrdered) = struct
  type t = X.t
  (* Branches returning known constructors: this is the only form flambda
     can fuse with the match consuming the result (case-of-case). A
     branchless arithmetic conversion can never be fused back into control
     flow. *)
  let [@inline always] compare a b : Comparison.t =
    match%compare X.compare a b with
    | Eq -> Eq
    | Lt -> Lt
    | Gt -> Gt
    (*
    let c = X.compare a b in
    (*
    if c = 0 then Eq else if c < 0 then Lt else Gt
    ((Obj.magic (c > 0) : int) - (Obj.magic (c < 0) : int) + 1)
    |> (Obj.magic : int -> Comparison.t) 

       *)         
    c + 1 |> (Obj.magic : int -> Comparison.t) 
       *)
end

external phys_same : 'a 'b. 'a -> 'b -> bool = "%eq"


module [@inline always] Make(K : StandardOrdered) = struct
  type c_empty = [ `Empty ]
  type c_v1 = [ `V1 ]
  type c_v2 = [ `V2 ]
  type c_v3 = [ `V3 ]
  type c_node = [ `Node ]

  type n_interior = [ `Interior ]
  type n_leaf = [ `Leaf ]

  module T : sig
    (* [Empty] must carry a value, because the [is_int] check
       slows down matches and [weight] *)
    type empty = private unit
    type ('nconstructor, 'nkind, +!'v) node =
      | Empty : empty -> (c_empty, n_leaf, 'v) node
      | V1 : { k1 : K.t; v1 : 'v } -> (c_v1, n_leaf, 'v) node
      | V2 : { k11 : K.t; v11 : 'v
             ; k1 : K.t; v1 : 'v
             } -> (c_v2, n_leaf, 'v) node
      | V3 : { k11 : K.t; v11 : 'v
             ; k1 : K.t; v1 : 'v
             ; k12 : K.t; v12 : 'v
             } -> (c_v3, n_leaf, 'v) node
      | Node : { weight : int
               ; n1 : 'v t
               ; k0 : K.t; v0 : 'v
               ; n2 : 'v t
               } -> (c_node, n_interior, 'v) node
    and +!'v t = T : ('nconstructor, 'nkind, 'v) node -> 'v t [@@unboxed]

    type +!'v leaf = L : ('nconstructor, n_leaf, 'v) node -> 'v leaf [@@unboxed]

    val empty : 'v t
  end = struct
    type empty = unit
    type ('nconstructor, 'nkind, +!'v) node =
      | Empty : empty -> (c_empty, n_leaf, 'v) node
      | V1 : { k1 : K.t; v1 : 'v } -> (c_v1, n_leaf, 'v) node
      | V2 : { k11 : K.t; v11 : 'v
             ; k1 : K.t; v1 : 'v
             } -> (c_v2, n_leaf, 'v) node
      | V3 : { k11 : K.t; v11 : 'v
             ; k1 : K.t; v1 : 'v
             ; k12 : K.t; v12 : 'v
             } -> (c_v3, n_leaf, 'v) node
      | Node : { weight : int
               ; n1 : 'v t
               ; k0 : K.t; v0 : 'v
               ; n2 : 'v t
               } -> (c_node, n_interior, 'v) node
    and +!'v t = T : ('nconstructor, 'nkind, 'v) node -> 'v t [@@unboxed]

    type +!'v leaf = L : ('nconstructor, n_leaf, 'v) node -> 'v leaf [@@unboxed]

    let empty = T (Empty ())
  end
  include T

  module Invariant = struct
    open Sexplib0
    let rec sexp_shape = function
      | T (Empty _) -> Sexp.Atom "Empty"
      | T (V1 _) -> Sexp.Atom "V1"
      | T (V2 _) -> Sexp.Atom "V2"
      | T (V3 _) -> Sexp.Atom "V3"
      | T (Node { weight; n1; n2; _ }) -> Sexp.List [ Sexp.Atom "Node"; Sexp_conv.sexp_of_int weight; sexp_shape n1; sexp_shape n2 ]


    let rec no_node_empty t' = function
      | T (Node { n1 = T (Empty _); _ })
      | T (Node { n2 = T (Empty _); _ }) ->
        Printf.eprintf "%s\n" (Sexplib0.Sexp.to_string (sexp_shape t'));
        assert false
      | T (Node { n1; n2; _ }) -> no_node_empty t' n1; no_node_empty t' n2
      | _ -> ()

    let rec no_node_unfused t' = function
      | T (Node {n1 = T (V1 _); n2 = T (V1 _); _ }) ->
        Printf.eprintf "%s\n" (Sexplib0.Sexp.to_string (sexp_shape t'));
        assert false
      | T (Node { n1; n2; _ }) -> no_node_unfused t' n1; no_node_unfused t' n2
      | _ -> ()

    let do_check = false

    let [@inline always] check_invariant t =
      if do_check
      then begin
        no_node_empty t t;
        no_node_unfused t t
      end

  end

  module Stats = struct
    type t =
      { mutable count_empty : int
      ; mutable count_v1 : int
      ; mutable count_v2 : int
      ; mutable count_v3 : int
      ; mutable count_node : int
      ; mutable depth : int
      } [@@deriving sexp]

    let create () =
      { count_empty = 0; count_v1 = 0; count_v2 = 0; count_v3 = 0; count_node = 0; depth = 0 }

    let update s t =
      match t with
      | T (Empty _) -> s.count_empty <- s.count_empty + 1
      | T (V1 _) -> s.count_v1 <- s.count_v1 + 1
      | T (V2 _) -> s.count_v2 <- s.count_v2 + 1
      | T (V3 _) -> s.count_v3 <- s.count_v3 + 1
      | T (Node _) -> s.count_node <- s.count_node + 1

    let rec gather ~depth s t =
      update s t;
      match t with
      | T (Node { n1; n2; _ }) ->
        let depth = depth + 1 in
        if depth > s.depth then s.depth <- depth;
        gather ~depth s n1; gather ~depth s n2
      | _ -> ()

    let gather t =
      let s = create () in
      gather ~depth:0 s t;
      s
  end

  type 'a n_empty = (c_empty, n_leaf, 'a) node
  type 'a n_v1 = (c_v1, n_leaf, 'a) node
  type 'a n_v2 = (c_v2, n_leaf, 'a) node
  type 'a n_v3 = (c_v3, n_leaf, 'a) node
  type 'a n_node = (c_node, n_interior, 'a) node

  (* Alternative weight function, compiles to:
     48 89 c3                mov    %rax,%rbx
     48 0f b6 43 f8          movzbq -0x8(%rbx),%rax
     48 8d 15 00 00 00 00    lea    0x0(%rip),%rdx        # 14ff <camlBcaml__Triple.weight2_608+0xf>
                        64_PC32     .rodata+0x24
     48 63 04 82             movslq (%rdx,%rax,4),%rax
     48 01 c2                add    %rax,%rdx
     ff e2                   jmp    *%rdx
     b8 03 00 00 00          mov    $0x3,%eax
     c3                      ret
     66 90                   xchg   %ax,%ax
     b8 05 00 00 00          mov    $0x5,%eax
     c3                      ret
     66 90                   xchg   %ax,%ax
     b8 07 00 00 00          mov    $0x7,%eax
     c3                      ret
     66 90                   xchg   %ax,%ax
     b8 09 00 00 00          mov    $0x9,%eax
     c3                      ret
     66 90                   xchg   %ax,%ax
     48 8b 03                mov    (%rbx),%rax
     c3                      ret
     0f 1f 40 00             nopl   0x0(%rax)
  *)
  let [@inline always] weight2 = function
    | T (Empty _) -> 1
    | T (V1 _) -> 2
    | T (V2 _) -> 3
    | T (V3 _) -> 4
    | T (Node { weight; _ }) -> weight

  (* Must be a separate function for the match to compile properly to
     the identity + 1 *)
  let [@inline always] weight_leaf = function
    | L (Empty _) -> 1
    | L (V1 _) -> 2
    | L (V2 _) -> 3
    | L (V3 _) -> 4

  (* ~Equivalent to using caml_bytes_get_64u, but no unsafe stuff, and works
     on both 32 and 64 bit:
    48 0f b6 58 f8          movzbq -0x8(%rax),%rbx
    48 83 fb 04             cmp    $0x4,%rbx
    7c 05                   jl     1550 <camlBcaml__Triple.weight_631+0x10>
    48 8b 00                mov    (%rax),%rax
    c3                      ret
    90                      nop
    48 0f b6 40 f8          movzbq -0x8(%rax),%rax
    48 8d 44 00 03          lea    0x3(%rax,%rax,1),%rax
    c3                      ret
    0f 1f 44 00 00          nopl   0x0(%rax,%rax,1)
  *)
  let [@inline always] weight = function
    | T (Node { weight; _}) -> weight
    | T (V1 _ as leaf) -> weight_leaf (L leaf)
    | T (V2 _ as leaf) -> weight_leaf (L leaf)
    | T (V3 _ as leaf) -> weight_leaf (L leaf)
    | T (Empty _ as leaf) -> weight_leaf (L leaf)


  (*
    48 0f b6 58 f8          movzbq -0x8(%rax),%rbx
    48 83 fb 04             cmp    $0x4,%rbx
    7c 05                   jl     1570 <camlBcaml__Triple.weight1_641+0x10>
    48 8b 00                mov    (%rax),%rax
    c3                      ret
    90                      nop
    48 8b 40 f8             mov    -0x8(%rax),%rax
    48 25 ff 00 00 00       and    $0xff,%rax
    48 8d 44 00 03          lea    0x3(%rax,%rax,1),%rax
    c3                      ret
     *)
  let [@inline always] weight1 (T t) =
    match t with
    | Node { weight; _ } -> weight
    | _ ->
      let module Internal = struct
        external get : bytes -> int -> int64 = "%caml_bytes_get64u"
      end in
      (Int64.to_int (Int64.logand (Internal.get ((Obj.magic t) : bytes) (-8)) 0xFFL)) + 1

  let size t = weight t - 1

  let [@inline always] single_rotation_left_node ~n1w ~n2w ~n11 ~n1k ~n1v ~n12 ~n0k ~n0v ~n2 =
    T (Node { weight = n1w + n2w
            ; n1 = n11
            ; k0 = n1k ; v0 = n1v
            ; n2 = T (Node ({ weight = weight n12 + n2w
                            ; n1 = n12
                            ; k0 = n0k; v0 = n0v
                            ; n2
                            }))
            })

  let [@inline always] single_rotation_right_node ~n1w ~n2w ~n1 ~n0k ~n0v ~n21 ~n2k ~n2v ~n22 =
    T (Node { weight = n1w + n2w
            ; n1 = T (Node ({ weight = n1w + weight n21
                            ; n1 = n1
                            ; k0 = n0k; v0 = n0v
                            ; n2 = n21
                            }))
            ; k0 = n2k; v0 = n2v
            ; n2 = n22
            })

  let [@inline always] double_rotation_left_node ~n1w ~n2w ~n11 ~n1k ~n1v ~n12k ~n12v ~n121 ~n122 ~n0k ~n0v ~n2 =
    T (Node { weight = n1w + n2w
            ; n1 = T (Node ({ weight = (weight n11) + (weight n121)
                            ; n1 = n11
                            ; k0 = n1k; v0 = n1v
                            ; n2 = n121
                            }))
            ; k0 = n12k; v0 = n12v
            ; n2 = T (Node ({ weight = weight n122 + n2w
                            ; n1 = n122
                            ; k0 = n0k; v0 = n0v
                            ; n2
                            }))
            })

  let [@inline always] double_rotation_right_node ~n1w ~n2w ~n1 ~n0k ~n0v ~n21k ~n21v ~n211 ~n212 ~n2k ~n2v ~n22 =
    T (Node { weight = n1w + n2w
            ; n1 = T (Node ({ weight = n1w + weight n211
                            ; n1 = n1
                            ; k0 = n0k; v0 = n0v
                            ; n2 = n211
                            }))
            ; k0 = n21k; v0 = n21v
            ; n2 = T (Node ({ weight = (weight n22) + (weight n212)
                            ; n1 = n212
                            ; k0 = n2k; v0 = n2v
                            ; n2 = n22
                            }))
            })

  let omega2 = 5
  let alpha2 = 2
  let delta2 = 0

  let [@inline always] valid_input_imbalance n1w n2w =
    let open Non_short_circuiting in
    10 * n1w < 8 * (n1w + n2w) && 10 * n2w < 8 * (n1w + n2w)

  let [@inline always] needs_rotation ~deep_side ~shallow_side =
    2 * deep_side > omega2 * shallow_side + delta2

  let balance_condition_left_rotation ~n1w ~n2w =
    needs_rotation ~deep_side:n1w ~shallow_side:n2w

  let balance_condition_right_rotation ~n1w ~n2w =
    needs_rotation ~deep_side:n2w ~shallow_side:n1w

  let [@inline always] balanced_size n1 n2 =
    let open Non_short_circuiting in
    (omega2 * n1 + delta2 >= 2 * n2) && (omega2 * n2 + delta2 >= 2 * n1)

  let [@inline always] needs_single_rotation2 ~n11w ~n121w ~n122w ~n2w =
    (* Seems like evaluating all branches in parallel is an improvement,
       maybe fewer unpredictable branches *)
    let open Non_short_circuiting in
    not (
      (balanced_size n11w n121w)
      && (balanced_size n122w n2w)
      && (balanced_size (n11w + n121w) (n122w + n2w))
    )

  let [@inline always] balance_condition_left_single ~n11w ~n121w ~n122w ~n2w =
    needs_single_rotation2 ~n11w ~n121w ~n122w ~n2w

  let [@inline always] balance_condition_right_single ~n1w ~n211w ~n212w ~n22w =
    needs_single_rotation2 ~n11w:n22w ~n121w:n212w ~n122w:n211w ~n2w:n1w

  let balance_deep ~n1 ~k0 ~v0 ~n2 =
    let n1w = weight n1 in
    let n2w = weight n2 in
    if balance_condition_left_rotation ~n1w ~n2w
    then begin
      match n1 with
      | T (Node ({ weight = _; n1 = n11; k0 = n1k; v0 = n1v; n2 = n12 })) ->
        begin match n12 with
          | T (Node ({ weight = _; n1 = n121; k0 = n12k; v0 = n12v; n2 = n122 }))
            when not (balance_condition_left_single ~n11w:(weight n11) ~n121w:(weight n121) ~n122w:(weight n122) ~n2w) ->
            double_rotation_left_node ~n1w ~n2w ~n11 ~n1k ~n1v ~n12k ~n12v ~n121 ~n122 ~n0k:k0 ~n0v:v0 ~n2
          | _ ->
            single_rotation_left_node ~n1w ~n2w ~n11 ~n1k ~n1v ~n12 ~n0k:k0 ~n0v:v0 ~n2
        end
      | _ -> assert false (* See rocq proof *)
    end else if balance_condition_right_rotation ~n1w ~n2w
    then begin
      match n2 with
      | T (Node ({ weight = _; n1 = n21; k0 = n2k; v0 = n2v; n2 = n22 })) ->
        begin match n21 with
          | T (Node ({ weight = _; n1 = n211; k0 = n21k; v0 = n21v; n2 = n212 }))
            when not (balance_condition_right_single ~n1w:(weight n1) ~n211w:(weight n211) ~n212w:(weight n212) ~n22w:(weight n22)) ->
            double_rotation_right_node ~n1w ~n2w ~n1 ~n0k:k0 ~n0v:v0 ~n21k ~n21v ~n211 ~n212 ~n2k ~n2v ~n22
          | _ ->
            single_rotation_right_node ~n1w ~n2w ~n1 ~n0k:k0 ~n0v:v0 ~n21 ~n2k ~n2v ~n22
        end
      | _ -> assert false (* See rocq proof *)
    end else begin
      T (Node ({ weight = n1w + n2w; n1; k0; v0; n2 }))
    end

let balance_shallow ~n1 ~k0 ~v0 ~n2 =
  match n1, n2 with
(*$ 
open Core
open Case_writer

let shallow_cases = Sexp.load_sexps_conv_exn "../shallow_cases.sexp" Line.t_of_sexp
let fusion_cases = Sexp.load_sexps_conv_exn "../fusion_cases.sexp" Line.t_of_sexp
let () = Printf.printf "\n"
let () = List.iter shallow_cases ~f:(fun l ->
  Printf.printf "%s\n" (Line.to_caml l)
   )
let () = List.iter fusion_cases ~f:(fun l ->
  Printf.printf "%s\n" (Line.to_caml l)
   )
*)
  | T (Empty _)
  , T (Empty _) ->
    T (V1 { k1 = k0; v1 = v0})
  | T (V1 { k1 = k1; v1 = v1})
  , T (Empty _) ->
    T (V2 { k11 = k1; v11 = v1; k1 = k0; v1 = v0})
  | T (Empty _)
  , T (V1 { k1 = k2; v1 = v2}) ->
    T (V2 { k11 = k0; v11 = v0; k1 = k2; v1 = v2})
  | T (V1 { k1 = k1; v1 = v1})
  , T (V1 { k1 = k2; v1 = v2}) ->
    T (V3 { k11 = k1; v11 = v1; k1 = k0; v1 = v0; k12 = k2; v12 = v2})
  | T (V2 { k11 = k11; v11 = v11; k1 = k1; v1 = v1})
  , T (Empty _) ->
    T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k0; v12 = v0})
  | T (Empty _)
  , T (V2 { k11 = k21; v11 = v21; k1 = k2; v1 = v2}) ->
    T (V3 { k11 = k0; v11 = v0; k1 = k21; v1 = v21; k12 = k2; v12 = v2})
  | T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k12; v12 = v12})
  , T (Empty _) ->
    T (Node { weight = 5; n1 = T (V2 { k11 = k11; v11 = v11; k1 = k1; v1 = v1}); k0 = k12; v0 = v12; n2 = T (V1 { k1 = k0; v1 = v0})})
  | T (Empty _)
  , T (V3 { k11 = k21; v11 = v21; k1 = k2; v1 = v2; k12 = k22; v12 = v22}) ->
    T (Node { weight = 5; n1 = T (V2 { k11 = k0; v11 = v0; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})})
  | T (Node { weight = _; n1 = (T (V3 { k11 = k111; v11 = v111; k1 = k11; v1 = v11; k12 = k112; v12 = v112}) as t_1); k0 = k1; v0 = v1; n2 = T (V1 { k1 = k12; v1 = v12})})
  , T (V1 { k1 = k2; v1 = v2}) ->
    T (Node { weight = 8; n1 = t_1; k0 = k1; v0 = v1; n2 = T (V3 { k11 = k12; v11 = v12; k1 = k0; v1 = v0; k12 = k2; v12 = v2})})
  | T (V1 { k1 = k1; v1 = v1})
  , T (Node { weight = _; n1 = T (V1 { k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (V3 { k11 = k221; v11 = v221; k1 = k22; v1 = v22; k12 = k222; v12 = v222}) as t_3)}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k1; v11 = v1; k1 = k0; v1 = v0; k12 = k21; v12 = v21}); k0 = k2; v0 = v2; n2 = t_3})
  | T (Node { weight = _; n1 = (T (Node { weight = 5; n1 = n111; k0 = k11; v0 = v11; n2 = n112}) as t_1); k0 = k1; v0 = v1; n2 = T (V1 { k1 = k12; v1 = v12})})
  , T (V1 { k1 = k2; v1 = v2}) ->
    T (Node { weight = 9; n1 = t_1; k0 = k1; v0 = v1; n2 = T (V3 { k11 = k12; v11 = v12; k1 = k0; v1 = v0; k12 = k2; v12 = v2})})
  | T (V1 { k1 = k1; v1 = v1})
  , T (Node { weight = _; n1 = T (V1 { k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (Node { weight = 5; n1 = n221; k0 = k22; v0 = v22; n2 = n222}) as t_3)}) ->
    T (Node { weight = 9; n1 = T (V3 { k11 = k1; v11 = v1; k1 = k0; v1 = v0; k12 = k21; v12 = v21}); k0 = k2; v0 = v2; n2 = t_3})
  | T (Node { weight = _; n1 = T (V1 { k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (V3 { k11 = k121; v11 = v121; k1 = k12; v1 = v12; k12 = k122; v12 = v122})})
  , T (V1 { k1 = k2; v1 = v2}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k121; v12 = v121}); k0 = k12; v0 = v12; n2 = T (V3 { k11 = k122; v11 = v122; k1 = k0; v1 = v0; k12 = k2; v12 = v2})})
  | T (V1 { k1 = k1; v1 = v1})
  , T (Node { weight = _; n1 = T (V3 { k11 = k211; v11 = v211; k1 = k21; v1 = v21; k12 = k212; v12 = v212}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k1; v11 = v1; k1 = k0; v1 = v0; k12 = k211; v12 = v211}); k0 = k21; v0 = v21; n2 = T (V3 { k11 = k212; v11 = v212; k1 = k2; v1 = v2; k12 = k22; v12 = v22})})
  | T (Node { weight = _; n1 = T (V1 { k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (Node { weight = _; n1 = T (V1 { k1 = k121; v1 = v121}); k0 = k12; v0 = v12; n2 = (T (V2 { k11 = k1221; v11 = v1221; k1 = k122; v1 = v122}) as t_3)})})
  , (T (V1 { k1 = k2; v1 = v}) as t_6) ->
    T (Node { weight = 9; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k121; v12 = v121}); k0 = k12; v0 = v12; n2 = T (Node { weight = 5; n1 = t_3; k0 = k0; v0 = v0; n2 = t_6})})
  | (T (V1 { k1 = k1; v1 = v1}) as t_1)
  , T (Node { weight = _; n1 = T (Node { weight = _; n1 = (T (V2 { k11 = k2111; v11 = v2111; k1 = k211; v1 = v211}) as t_2); k0 = k21; v0 = v21; n2 = T (V1 { k1 = k212; v1 = v212})}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})}) ->
    T (Node { weight = 9; n1 = T (Node { weight = 5; n1 = t_1; k0 = k0; v0 = v0; n2 = t_2}); k0 = k21; v0 = v21; n2 = T (V3 { k11 = k212; v11 = v212; k1 = k2; v1 = v2; k12 = k22; v12 = v22})})
  | T (Node { weight = _; n1 = T (V1 { k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (Node { weight = _; n1 = T (V2 { k11 = k1211; v11 = v1211; k1 = k121; v1 = v121}); k0 = k12; v0 = v12; n2 = T (V1 { k1 = k122; v1 = v122})})})
  , (T (V1 { k1 = k2; v1 = v2}) as t_6) ->
    T (Node { weight = 9; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k1211; v12 = v1211}); k0 = k121; v0 = v121; n2 = T (Node { weight = 5; n1 = T (V2 { k11 = k12; v11 = v12; k1 = k122; v1 = v122}); k0 = k0; v0 = v0; n2 = t_6})})
  | (T (V1 { k1 = k1; v1 = v1}) as t_1)
  , T (Node { weight = _; n1 = T (Node { weight = _; n1 = T (V1 { k1 = k211; v1 = v211}); k0 = k21; v0 = v21; n2 = T (V2 { k11 = k2121; v11 = v2121; k1 = k212; v1 = v212})}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})}) ->
    T (Node { weight = 9; n1 = T (Node { weight = 5; n1 = t_1; k0 = k0; v0 = v0; n2 = T (V2 { k11 = k211; v11 = v211; k1 = k21; v1 = v21})}); k0 = k2121; v0 = v2121; n2 = T (V3 { k11 = k212; v11 = v212; k1 = k2; v1 = v2; k12 = k22; v12 = v22})})
  | T (Node { weight = _; n1 = (T (V2 { k11 = k111; v11 = v111; k1 = k11; v1 = v11}) as t_1); k0 = k1; v0 = v1; n2 = T (Node { weight = _; n1 = (T (V2 { k11 = k1211; v11 = v1211; k1 = k121; v1 = v121}) as t_2); k0 = k12; v0 = v12; n2 = T (V1 { k1 = k122; v1 = v122})})})
  , T (V1 { k1 = k2; v1 = v2}) ->
    T (Node { weight = 10; n1 = T (Node { weight = 6; n1 = t_1; k0 = k1; v0 = v1; n2 = t_2}); k0 = k12; v0 = v12; n2 = T (V3 { k11 = k122; v11 = v122; k1 = k0; v1 = v0; k12 = k2; v12 = v2})})
  | T (V1 { k1 = k1; v1 = v1})
  , T (Node { weight = _; n1 = T (Node { weight = _; n1 = T (V1 { k1 = k211; v1 = v211}); k0 = k21; v0 = v21; n2 = (T (V2 { k11 = k2121; v11 = v2121; k1 = k212; v1 = v212}) as t_3)}); k0 = k2; v0 = v2; n2 = (T (V2 { k11 = k221; v11 = v221; k1 = k22; v1 = v22}) as t_5)}) ->
    T (Node { weight = 10; n1 = T (V3 { k11 = k1; v11 = v1; k1 = k0; v1 = v0; k12 = k211; v12 = v211}); k0 = k21; v0 = v21; n2 = T (Node { weight = 6; n1 = t_3; k0 = k2; v0 = v2; n2 = t_5})})
  | T (Node { weight = _; n1 = T (V1 { k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (V2 { k11 = k121; v11 = v121; k1 = k12; v1 = v12})})
  , T (Empty _) ->
    T (Node { weight = 6; n1 = T (V2 { k11 = k11; v11 = v11; k1 = k1; v1 = v1}); k0 = k121; v0 = v121; n2 = T (V2 { k11 = k12; v11 = v12; k1 = k0; v1 = v0})})
  | T (Empty _)
  , T (Node { weight = _; n1 = T (V1 { k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (V2 { k11 = k221; v11 = v221; k1 = k22; v1 = v22}) as t_2)}) ->
    T (Node { weight = 6; n1 = T (V2 { k11 = k0; v11 = v0; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = t_2})
  | T (Node { weight = _; n1 = (T (V2 { k11 = k111; v11 = v111; k1 = k11; v1 = v11}) as t_1); k0 = k1; v0 = v1; n2 = T (V1 { k1 = k12; v1 = v12})})
  , T (Empty _) ->
    T (Node { weight = 6; n1 = t_1; k0 = k1; v0 = v1; n2 = T (V2 { k11 = k12; v11 = v12; k1 = k0; v1 = v0})})
  | T (Empty _)
  , T (Node { weight = _; n1 = T (V2 { k11 = k211; v11 = v211; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})}) ->
    T (Node { weight = 6; n1 = T (V2 { k11 = k0; v11 = v0; k1 = k211; v1 = v211}); k0 = k21; v0 = v21; n2 = T (V2 { k11 = k2; v11 = v2; k1 = k22; v1 = v22})})
  | T (Node { weight = _; n1 = (T (V2 { k11 = k111; v11 = v111; k1 = k11; v1 = v11}) as t_1); k0 = k1; v0 = v1; n2 = T (V2 { k11 = k121; v11 = v121; k1 = k12; v1 = v12})})
  , T (Empty _) ->
    T (Node { weight = 7; n1 = t_1; k0 = k1; v0 = v1; n2 = T (V3 { k11 = k121; v11 = v121; k1 = k12; v1 = v12; k12 = k0; v12 = v0})})
  | T (Empty _)
  , T (Node { weight = _; n1 = T (V2 { k11 = k211; v11 = v211; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (V2 { k11 = k221; v11 = v221; k1 = k22; v1 = v22}) as t_2)}) ->
    T (Node { weight = 7; n1 = T (V3 { k11 = k0; v11 = v0; k1 = k211; v1 = v211; k12 = k21; v12 = v21}); k0 = k2; v0 = v2; n2 = t_2})
  | T (Node { weight = _; n1 = (T (V3 { k11 = k111; v11 = v111; k1 = k11; v1 = v11; k12 = k112; v12 = v112}) as t_1); k0 = k1; v0 = v1; n2 = T (V2 { k11 = k121; v11 = v121; k1 = k12; v1 = v12})})
  , T (Empty _) ->
    T (Node { weight = 8; n1 = t_1; k0 = k1; v0 = v1; n2 = T (V3 { k11 = k121; v11 = v121; k1 = k12; v1 = v12; k12 = k0; v12 = v0})})
  | T (Empty _)
  , T (Node { weight = _; n1 = T (V2 { k11 = k211; v11 = v211; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (V3 { k11 = k221; v11 = v221; k1 = k22; v1 = v22; k12 = k222; v12 = v222}) as t_2)}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k0; v11 = v0; k1 = k211; v1 = v211; k12 = k21; v12 = v21}); k0 = k2; v0 = v2; n2 = t_2})
  | T (Node { weight = _; n1 = (T (V3 { k11 = k111; v11 = v111; k1 = k11; v1 = v11; k12 = k112; v12 = v112}) as t_1); k0 = k1; v0 = v1; n2 = T (V1 { k1 = k12; v1 = v12})})
  , T (Empty _) ->
    T (Node { weight = 7; n1 = t_1; k0 = k1; v0 = v1; n2 = T (V2 { k11 = k12; v11 = v12; k1 = k0; v1 = v0})})
  | T (Empty _)
  , T (Node { weight = _; n1 = T (V1 { k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = (T (V3 { k11 = k221; v11 = v221; k1 = k22; v1 = v22; k12 = k222; v12 = v222}) as t_2)}) ->
    T (Node { weight = 7; n1 = T (V2 { k11 = k0; v11 = v0; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = t_2})
  | T (Node { weight = _; n1 = T (V1 { k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (V3 { k11 = k121; v11 = v121; k1 = k12; v1 = v12; k12 = k122; v12 = v122})})
  , T (Empty _) ->
    T (Node { weight = 7; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k121; v12 = v121}); k0 = k12; v0 = v12; n2 = T (V2 { k11 = k122; v11 = v122; k1 = k0; v1 = v0})})
  | T (Empty _)
  , T (Node { weight = _; n1 = T (V3 { k11 = k211; v11 = v211; k1 = k21; v1 = v21; k12 = k212; v12 = v212}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})}) ->
    T (Node { weight = 7; n1 = T (V2 { k11 = k0; v11 = v0; k1 = k211; v1 = v211}); k0 = k21; v0 = v21; n2 = T (V3 { k11 = k212; v11 = v212; k1 = k2; v1 = v2; k12 = k22; v12 = v22})})
  | T (V1 { k1 = _; v1 = _})
  , T (V2 { k11 = _; v11 = _; k1 = _; v1 = _}) ->
    T (Node { weight = 5; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V2 { k11 = _; v11 = _; k1 = _; v1 = _})
  , T (V1 { k1 = _; v1 = _}) ->
    T (Node { weight = 5; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V1 { k1 = _; v1 = _})
  , T (V3 { k11 = _; v11 = _; k1 = _; v1 = _; k12 = _; v12 = _}) ->
    T (Node { weight = 6; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V3 { k11 = _; v11 = _; k1 = _; v1 = _; k12 = _; v12 = _})
  , T (V1 { k1 = _; v1 = _}) ->
    T (Node { weight = 6; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V2 { k11 = _; v11 = _; k1 = _; v1 = _})
  , T (V2 { k11 = _; v11 = _; k1 = _; v1 = _}) ->
    T (Node { weight = 6; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V2 { k11 = _; v11 = _; k1 = _; v1 = _})
  , T (V3 { k11 = _; v11 = _; k1 = _; v1 = _; k12 = _; v12 = _}) ->
    T (Node { weight = 7; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V3 { k11 = _; v11 = _; k1 = _; v1 = _; k12 = _; v12 = _})
  , T (V2 { k11 = _; v11 = _; k1 = _; v1 = _}) ->
    T (Node { weight = 7; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V3 { k11 = _; v11 = _; k1 = _; v1 = _; k12 = _; v12 = _})
  , T (V3 { k11 = _; v11 = _; k1 = _; v1 = _; k12 = _; v12 = _}) ->
    T (Node { weight = 8; n1 = n1; k0 = k0; v0 = v0; n2 = n2})
  | T (V2 { k11 = k11; v11 = v11; k1 = k1; v1 = v1})
  , T (Node { weight = _; n1 = T (V2 { k11 = k211; v11 = v211; k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = T (V1 { k1 = k22; v1 = v22})}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k0; v12 = v0}); k0 = k211; v0 = v211; n2 = T (V3 { k11 = k21; v11 = v21; k1 = k2; v1 = v2; k12 = k22; v12 = v22})})
  | T (V2 { k11 = k11; v11 = v11; k1 = k1; v1 = v1})
  , T (Node { weight = _; n1 = T (V1 { k1 = k21; v1 = v21}); k0 = k2; v0 = v2; n2 = T (V2 { k11 = k221; v11 = v221; k1 = k22; v1 = v22})}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k0; v12 = v0}); k0 = k21; v0 = v21; n2 = T (V3 { k11 = k2; v11 = v2; k1 = k221; v1 = v221; k12 = k22; v12 = v22})})
  | T (Node { weight = _; n1 = T (V2 { k11 = k111; v11 = v111; k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (V1 { k1 = k12; v1 = v12})})
  , T (V2 { k11 = k21; v11 = v21; k1 = k2; v1 = v2}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k111; v11 = v111; k1 = k11; v1 = v11; k12 = k1; v12 = v1}); k0 = k12; v0 = v12; n2 = T (V3 { k11 = k0; v11 = v0; k1 = k21; v1 = v21; k12 = k2; v12 = v2})})
  | T (Node { weight = _; n1 = T (V1 { k1 = k11; v1 = v11}); k0 = k1; v0 = v1; n2 = T (V2 { k11 = k121; v11 = v121; k1 = k12; v1 = v12})})
  , T (V2 { k11 = k21; v11 = v21; k1 = k2; v1 = v2}) ->
    T (Node { weight = 8; n1 = T (V3 { k11 = k11; v11 = v11; k1 = k1; v1 = v1; k12 = k121; v12 = v121}); k0 = k12; v0 = v12; n2 = T (V3 { k11 = k0; v11 = v0; k1 = k21; v1 = v21; k12 = k2; v12 = v2})})
(*$*)
  | _, _ -> balance_deep ~n1 ~k0 ~v0 ~n2

let balance_shallow ~n1 ~k0 ~v0 ~n2 =
  (*
  let result =
     *)
  match n1, n2 with
  | T (Node _), T (Node _) -> balance_deep ~n1 ~k0 ~v0 ~n2
  | _, _ ->
    balance_shallow ~n1 ~k0 ~v0 ~n2
      (*
  in
  begin try
    Invariant.check_invariant result
  with
  | Assert_failure _ ->
    Printf.eprintf "n1=%s; n2=%s\n" (Sexplib0.Sexp.to_string (Invariant.sexp_shape n1)) (Sexplib0.Sexp.to_string (Invariant.sexp_shape n2));
    assert false
  end;
  result
         *)

  module Uopt : sig
    type 'a t

    val none : 'a t
    val some : 'a -> 'a t

    val unsafe_value : 'a t -> 'a
  end = struct
    type 'a t = 'a

    external __LOC__ : _ t = "%loc_LOC"

    let none = __LOC__

    let some v = v

    let unsafe_value t = t
  end

  (* Avoid allocating a return value at each intermediate node, just
     do it once *)
  module Extremum_return = struct
    type 'a t =
      { mutable key : K.t Uopt.t
      ; mutable value : 'a Uopt.t
      }

    let create () = { key = Uopt.none; value = Uopt.none }

    let key t = Uopt.unsafe_value t.key
    let value t = Uopt.unsafe_value t.value

    let set t k v =
      t.key <- Uopt.some k;
      t.value <- Uopt.some v
  end

  let rec split_min' ~return t =
    match t with
    | T (Empty _) -> assert false
    | T (V1 { k1; v1 }) ->
      Extremum_return.set return k1 v1;
      empty
    | T (V2 { k11; v11; k1; v1 }) ->
      Extremum_return.set return k11 v11;
      T (V1 { k1; v1 })
    | T (V3 { k11; v11; k1; v1; k12; v12 }) ->
      Extremum_return.set return k11 v11;
      T (V2 { k11 = k1; v11 = v1; k1 = k12; v1 = v12 })
    | T (Node { n1; k0; v0; n2 }) ->
      let n1' = split_min' ~return n1 in
      balance_shallow ~n1:n1' ~k0 ~v0 ~n2

  let split_min_and_balance l r =
    let return = Extremum_return.create () in
    let r' = split_min' ~return r in
    balance_shallow
      ~n1:l
      ~k0:(Extremum_return.key return) ~v0:(Extremum_return.value return)
      ~n2:r'

  let rec split_max' ~return t =
    match t with
    | T (Empty _) -> assert false
    | T (V1 { k1; v1 }) ->
      Extremum_return.set return k1 v1;
      empty
    | T (V2 { k11; v11; k1; v1 }) ->
      Extremum_return.set return k1 v1;
      T (V1 { k1 = k11; v1 = v11 })
    | T (V3 { k11; v11; k1; v1; k12; v12 }) ->
      Extremum_return.set return k12 v12;
      T (V2 { k11 = k11; v11 = v11; k1 = k1; v1 = v1 })
    | T (Node { n1; k0; v0; n2 }) ->
      let n2' = split_max' ~return n2 in
      balance_shallow ~n1 ~k0 ~v0 ~n2:n2'

  let split_max_and_balance l r =
    let return = Extremum_return.create () in
    let l' = split_max' ~return l in
    balance_shallow
      ~n1:l'
      ~k0:(Extremum_return.key return) ~v0:(Extremum_return.value return)
      ~n2:r

  module Change = struct
    let [@inline hint] unchanged t = T t

    module Empty = struct
      let [@inline hint] insert _ k1 v1 = T (V1 { k1; v1 })
    end

    module V1 = struct
      let [@inline hint] delete _ = empty

      let [@inline hint] replace (t : 'a n_v1) (v : 'a) =
        match t with
        | V1 { k1; v1 } ->
          if phys_same v1 v then T t else T (V1 { k1; v1 = v })

      let [@inline hint] insert_less (t : 'a n_v1) k11 v11 =
        match t with
        | V1 { k1; v1 } -> T (V2 { k11; v11; k1; v1 })

      let [@inline hint] insert_greater (t : 'a n_v1) k v =
        match t with
        | V1 { k1; v1 } -> T (V2 { k11 = k1; v11 = v1; k1 = k; v1 = v })
    end

    module V2 = struct
      let [@inline hint] delete_top (t : 'a n_v2) =
        match t with
        | V2 { k11; v11; _ } -> T (V1 { k1 = k11; v1 = v11 })

      let [@inline hint] delete_bottom (t : 'a n_v2) =
        match t with
        | V2 { k1; v1; _ } -> T (V1 { k1; v1 })

      let [@inline hint] replace_top (t : 'a n_v2) (v : 'a) =
        match t with
        | V2 { k11; v11; k1; v1 } ->
          if phys_same v1 v then T t else T (V2 { k11; v11; k1; v1 = v })

      let [@inline hint] replace_bottom (t : 'a n_v2) (v : 'a) =
        match t with
        | V2 { k11; v11; k1; v1 } ->
          if phys_same v11 v then T t else T (V2 { k11; v11 = v; k1; v1 })

      let [@inline hint] insert_bottom (t : 'a n_v2) k' v' =
        match t with
        | V2 { k11; v11; k1; v1 } -> T (V3 { k11 = k'; v11 = v'; k1 = k11; v1 = v11; k12 = k1; v12 = v1 })

      let [@inline hint] insert_middle (t : 'a n_v2) k' v' =
        match t with
        | V2 { k11; v11; k1; v1 } -> T (V3 { k11; v11; k1 = k'; v1 = v'; k12 = k1; v12 = v1 })

      let [@inline hint] insert_top (t : 'a n_v2) k' v' =
        match t with
        | V2 { k11; v11; k1; v1 } -> T (V3 { k11; v11; k1; v1; k12 = k'; v12 = v' })
    end


    module V3 = struct
      let [@inline hint] delete_top (t : 'a n_v3) =
        match t with
        | V3 { k11; v11; k1 = _; v1 = _; k12; v12 } ->
          T (V2 { k11; v11; k1 = k12; v1 = v12 })

      let [@inline hint] delete_left (t : 'a n_v3) =
        match t with
        | V3 { k11 = _; v11 =_; k1; v1; k12; v12 } ->
          T (V2 { k11 = k1; v11 = v1; k1 = k12; v1 = v12 })

      let [@inline hint] delete_right (t : 'a n_v3) =
        match t with
        | V3 { k11; v11; k1; v1; k12 = _; v12 = _ } ->
          T (V2 { k11; v11; k1; v1 })

      let [@inline hint] replace_top (t : 'a n_v3) (v : 'a) =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          if phys_same v1 v then T t else T (V3 { k11; v11; k1; v1 = v; k12; v12 })

      let [@inline hint] replace_left (t : 'a n_v3) (v : 'a) =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          if phys_same v11 v then T t else T (V3 { k11; v11 = v; k1; v1; k12; v12 })

      let [@inline hint] replace_right (t : 'a n_v3) (v : 'a) =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          if phys_same v12 v then T t else T (V3 { k11; v11; k1; v1; k12; v12 = v })

      let [@inline hint] insert_below_11 (t : 'a n_v3) k' v' =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          T (Node { weight = 5
                  ; n1 = T (V2 { k11 = k'; v11 = v'; k1 = k11; v1 = v11})
                  ; k0 = k1
                  ; v0 = v1
                  ; n2 = T (V1 { k1 = k12; v1 = v12 })
                  })

      let [@inline hint] insert_between_11_1 (t : 'a n_v3) k' v' =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          T (Node { weight = 5
                  ; n1 = T (V2 { k11; v11; k1 = k'; v1 = v'})
                  ; k0 = k1
                  ; v0 = v1
                  ; n2 = T (V1 { k1 = k12; v1 = v12 })
                  })

      let [@inline hint] insert_between_1_12 (t : 'a n_v3) k' v' =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          T (Node { weight = 5
               ; n1 = T (V2 { k11; v11; k1; v1 })
               ; k0 = k'
               ; v0 = v'
               ; n2 = T (V1 { k1 = k12; v1 = v12 })
               })

      let [@inline hint] insert_above_12 (t : 'a n_v3) k' v' =
        match t with
        | V3 { k11; v11; k1; v1; k12; v12 } ->
          T (Node { weight = 5
                  ; n1 = T (V2 { k11; v11; k1; v1 })
                  ; k0 = k12
                  ; v0 = v12
                  ; n2 = T (V1 { k1 = k'; v1 = v' })
                  })
    end

    module Node = struct
      let [@inline hint] delete_top (t : 'a n_node) =
        match t with
        | Node { weight = w; n1; k0 = _; v0 = _; n2 } ->
          let w1 = weight n1 in
          let w2 = w - w1 in
          let result =
            if w1 < w2
            then split_min_and_balance n1 n2
            else split_max_and_balance n1 n2
          in
          Invariant.check_invariant result;
          result

      let [@inline hint] replace_top (t : 'a n_node) (v : 'a) =
        match t with
        | Node { weight; n1; k0; v0; n2 } ->
          if phys_same v0 v then T t else T (Node { weight; n1; k0; v0 = v; n2 })


      (* Insert is only possible at leaf nodes *)

    end

  end

  module type Change_param = sig
    type 'a t_p
    type 'a user
    val existing : 'cin -> delete_fun:('cin -> 'cout) -> replace_fun:('cin -> 'a t_p -> 'cout) -> unchanged_fun : ('cin -> 'cout) -> K.t -> 'a t_p -> 'a user -> 'cout
    val missing : 'cin1 -> 'cin2 -> insert_fun:('cin1 -> 'cin2 -> 'a t_p -> 'cout) -> unchanged_fun : ('cin1 -> 'cout) -> K.t -> 'a user -> 'cout
  end

  module [@inline always] Make_change(C : Change_param) = struct
    let rec change
        (T t : 'a C.t_p t) k (user_param : 'a C.user)
      : 'a C.t_p t
      =
      let open Change in
      match t with
      | Node { weight; n1; k0; v0; n2 } ->
        begin match%compare K.compare k k0 with
          | Eq -> C.existing t ~delete_fun:Node.delete_top ~replace_fun:Node.replace_top ~unchanged_fun:unchanged k v0 user_param
          | Lt ->
            let n1' = change n1 k user_param in
            if phys_same n1 n1' then T t
            else balance_shallow ~n1:n1' ~k0 ~v0 ~n2
          | Gt ->
            let n2' = change n2 k user_param in
            if phys_same n2 n2' then T t
            else balance_shallow ~n1 ~k0 ~v0 ~n2:n2'
        end
      | _ -> change_leaf (T t) k user_param
    (* Attempting to pass a leaf to [change_leaf] is slower, maybe the multiple
       match cases are not merged properly *)
    and change_leaf
        (T t : 'a C.t_p t) k (user_param : 'a C.user)
      : 'a C.t_p t
      =
      let open Change in
      match t with
      | Empty _ -> C.missing t k ~insert_fun:Empty.insert ~unchanged_fun:unchanged k user_param
      | V1 { k1; v1 } ->
        begin match%compare K.compare k k1 with
          | Eq -> C.existing t ~delete_fun:V1.delete ~replace_fun:V1.replace ~unchanged_fun:unchanged k v1 user_param
          | Lt -> C.missing t k ~insert_fun:V1.insert_less ~unchanged_fun:unchanged k user_param
          | Gt -> C.missing t k ~insert_fun:V1.insert_greater ~unchanged_fun:unchanged k user_param
        end
      | V2 { k11; v11; k1; v1 } ->
        begin match%compare K.compare k k1 with
          | Eq -> C.existing t ~delete_fun:V2.delete_top ~replace_fun:V2.replace_top ~unchanged_fun:unchanged k v1 user_param
          | Lt ->
            begin match%compare K.compare k k11 with
              | Eq -> C.existing t ~delete_fun:V2.delete_bottom ~replace_fun:V2.replace_bottom ~unchanged_fun:unchanged k v1 user_param
              | Lt -> C.missing t k ~insert_fun:V2.insert_bottom ~unchanged_fun:unchanged k user_param
              | Gt -> C.missing t k ~insert_fun:V2.insert_middle ~unchanged_fun:unchanged k user_param
            end
          | Gt -> C.missing t k ~insert_fun:V2.insert_top ~unchanged_fun:unchanged k user_param
        end
      | V3 { k11; v11; k1; v1; k12; v12 } ->
        begin match%compare K.compare k k1 with
          | Eq -> C.existing t ~delete_fun:V3.delete_top ~replace_fun:V3.replace_top ~unchanged_fun:unchanged k v1 user_param
          | Lt ->
            begin match%compare K.compare k k11 with
              | Eq -> C.existing t ~delete_fun:V3.delete_left ~replace_fun:V3.replace_left ~unchanged_fun:unchanged k v1 user_param
              | Lt -> C.missing t k ~insert_fun:V3.insert_below_11 ~unchanged_fun:unchanged k user_param
              | Gt -> C.missing t k ~insert_fun:V3.insert_between_11_1 ~unchanged_fun:unchanged k user_param
            end
          | Gt ->
            begin match%compare K.compare k k12 with
              | Eq -> C.existing t ~delete_fun:V3.delete_right ~replace_fun:V3.replace_right ~unchanged_fun:unchanged k v1 user_param
              | Lt -> C.missing t k ~insert_fun:V3.insert_between_1_12 ~unchanged_fun:unchanged k user_param
              | Gt -> C.missing t k ~insert_fun:V3.insert_above_12 ~unchanged_fun:unchanged k user_param
            end
        end
      | Node _ -> assert false

    let [@inline hint] change
        (t : 'a C.t_p t) k (user_param : 'a C.user)
      : 'a C.t_p t
      =
      let result = change t k user_param in
      Invariant.check_invariant result;
      result
  end

  module Delete = Make_change(struct
      type 'a user = unit
      type 'a t_p = 'a

      let existing cin ~delete_fun ~replace_fun ~unchanged_fun k v' v =
        delete_fun cin

      let missing cin1 cin2 ~insert_fun ~unchanged_fun k v =
        unchanged_fun cin1
    end)

  let delete t k = Delete.change t k ()

  module Insert_or_replace = Make_change(struct
      type 'a user = 'a
      type 'a t_p = 'a

      let existing cin ~delete_fun ~replace_fun ~unchanged_fun k v' v =
        replace_fun cin v

      let missing cin1 cin2 ~insert_fun ~unchanged_fun k v =
        insert_fun cin1 cin2 v
    end)

  let insert_or_replace t k v = Insert_or_replace.change t k v

  module type Find = sig
    type 'a user
    type 'a return
    val found : K.t -> 'a -> 'a user -> 'a return
    val missing : K.t -> 'a user -> 'a return
  end

  module[@inline always] Make_find(F : Find) = struct
    let rec find (T t) k user_param =
      match t with
      | Node { weight; n1; k0; v0; n2 } ->
        begin match%compare K.compare k k0 with
          | Eq -> F.found k v0 user_param
          | Lt -> find n1 k user_param
          | Gt -> find n2 k user_param
        end
      | _ -> find_leaf (T t) k user_param
    and find_leaf (T t) k user_param =
      match t with
      | Empty _ -> F.missing k user_param
      | V1 { k1; v1 } -> final k k1 v1 user_param
      | V2 { k11; v11; k1; v1 } ->
        begin match%compare K.compare k k1 with
          | Eq -> F.found k v1 user_param
          | Lt -> final k k11 v11 user_param
          | Gt -> F.missing k user_param
        end
      | V3 { k11; v11; k1; v1; k12; v12 } ->
        begin match%compare K.compare k k1 with
          | Eq -> F.found k v1 user_param
          | Lt -> final k k11 v11 user_param
          | Gt -> final k k12 v12 user_param
        end
      | Node _ -> assert false
    and final k k' v' user_param =
      match%compare K.compare k k' with
      | Eq -> F.found k v' user_param
      | _ -> F.missing k user_param
  end

  module Find_exn = Make_find(struct
      type 'a user = unit
      type 'a return = 'a
      let found k v _ = v
      let missing k _ = raise Not_found
    end)

  let find_exn t k = Find_exn.find t k ()

  module Find_opt = Make_find(struct
      type 'a user = unit
      type 'a return = 'a option
      let [@inline always] found k v _ = Some v
      let [@inline always] missing k _ = None
    end)

  let find_opt t k = Find_opt.find t k ()

  let rec fold_low ~init ~user ~f (T t) =
    match t with
    | Empty _ -> init
    | V1 { k1; v1 } -> f init user k1 v1
    | V2 { k11; v11; k1; v1 } ->
      let init = f init user k11 v11 in
      let init = f init user k1 v1 in
      init
    | V3 { k11; v11; k1; v1; k12; v12 } ->
      let init = f init user k11 v11 in
      let init = f init user k1 v1 in
      let init = f init user k12 v12 in
      init
    | Node { weight; n1; k0; v0; n2 } ->
      let init = fold_low ~init ~user ~f n1 in
      let init = f init user k0 v0 in
      fold_low ~init ~user ~f n2

  let rec fold_high ~init ~user ~f (T t) =
    match t with
    | Empty _ -> init
    | V1 { k1; v1 } -> f init user k1 v1
    | V2 { k11; v11; k1; v1 } ->
      let init = f init user k1 v1 in
      let init = f init user k11 v11 in
      init
    | V3 { k11; v11; k1; v1; k12; v12 } ->
      let init = f init user k12 v12 in
      let init = f init user k1 v1 in
      let init = f init user k11 v11 in
      init
    | Node { weight; n1; k0; v0; n2 } ->
      let init = fold_high ~init ~user ~f n2 in
      let init = f init user k0 v0 in
      fold_high ~init ~user ~f n1

  let sexp_of_t sexp_of_k sexp_of_v t =
    let list =
      fold_high ~init:[] ~user:() ~f:(fun acc () k v ->
          Sexplib0.Sexp.List [ sexp_of_k k; sexp_of_v v ] :: acc
        ) t
    in
    Sexplib0.Sexp.List list

  let t_of_sexp k_of_sexp v_of_sexp sexp =
    match (sexp : Sexplib0.Sexp.t) with
    | Atom _ -> invalid_arg "triple.t_of_sexp"
    | List list ->
      List.fold_left (fun acc sexp ->
          match (sexp : Sexplib0.Sexp.t) with
          | List [ k_sexp; v_sexp ] ->
            insert_or_replace acc (k_of_sexp k_sexp) (v_of_sexp v_sexp)
          | _ -> invalid_arg "triple.t_of_sexp"
        ) empty list

  module type Find_extremum = sig
    type 'a user
    type 'a return
    val found : K.t -> 'a -> 'a user -> 'a return
    val missing : 'a user -> 'a return
  end

  module [@inline always] Find_min(F : Find_extremum) = struct
    let rec find (T t) user_param =
      match t with
      | Empty _ -> F.missing user_param
      | V1 { k1; v1 } -> F.found k1 v1 user_param
      | V2 { k11; v11; k1; v1 } -> F.found k11 v11 user_param
      | V3 { k11; v11; k1; v1; k12; v12 } -> F.found k11 v11 user_param
      | Node { weight; n1; k0; v0; n2 } -> find n1 user_param
  end

  module [@inline always] Find_max(F : Find_extremum) = struct
    let rec find (T t) user_param =
      match t with
      | Empty _ -> F.missing user_param
      | V1 { k1; v1 } -> F.found k1 v1 user_param
      | V2 { k11; v11; k1; v1 } -> F.found k1 v1 user_param
      | V3 { k11; v11; k1; v1; k12; v12 } -> F.found k12 v12 user_param
      | Node { weight; n1; k0; v0; n2 } -> find n2 user_param
  end

  module [@inline always] Find_first(F : Find_extremum) = struct
    let rec find (T t) ~f user_param =
      match t with
      | Empty _ -> F.missing user_param
      | V1 { k1; v1 } ->
        if f k1
        then F.found k1 v1 user_param
        else F.missing user_param
      | V2 { k11; v11; k1; v1 } ->
        if f k1
        then if f k11
          then F.found k11 v11 user_param
          else F.found k1 v1 user_param
        else F.missing user_param
      | V3 { k11; v11; k1; v1; k12; v12 } ->
        if f k1
        then if f k11
          then F.found k11 v11 user_param
          else F.found k1 v1 user_param
        else if f k12
          then F.found k12 v12 user_param
          else F.missing user_param
      | Node { weight; n1; k0; v0; n2 } ->
        if f k0
        then find_more_extreme n1 ~f ~k:k0 ~v:v0 user_param
        else find n2 ~f user_param
    and find_more_extreme (T t) ~f ~k ~v user_param =
      match t with
      | Empty _ -> assert false
      | V1 { k1; v1 } ->
        if f k1
        then F.found k1 v1 user_param
        else F.found k v user_param
      | V2 { k11; v11; k1; v1 } ->
        if f k1
        then if f k11
          then F.found k11 v11 user_param
          else F.found k1 v1 user_param
        else F.found k v user_param
      | V3 { k11; v11; k1; v1; k12; v12 } ->
        if f k1
        then if f k11
          then F.found k11 v11 user_param
          else F.found k1 v1 user_param
        else if f k12
          then F.found k12 v12 user_param
          else F.found k v user_param
      | Node { weight; n1; k0; v0; n2 } ->
        if f k0
        then find_more_extreme n1 ~f ~k:k0 ~v:v0 user_param
        else find_more_extreme n2 ~f ~k ~v user_param
  end

  module Find_last(F : Find_extremum) = struct
    let rec find (T t) ~f user_param =
      match t with
      | Empty _ -> F.missing user_param
      | V1 { k1; v1 } ->
        if f k1
        then F.found k1 v1 user_param
        else F.missing user_param
      | V2 { k11; v11; k1; v1 } ->
        if f k1
        then F.found k1 v1 user_param
        else if f k11
          then F.found k11 v11 user_param
          else F.missing user_param
      | V3 { k11; v11; k1; v1; k12; v12 } ->
        if f k1
        then if f k12
          then F.found k12 v12 user_param
          else F.found k1 v1 user_param
        else if f k11
          then F.found k11 v11 user_param
          else F.missing user_param
      | Node { weight; n1; k0; v0; n2 } ->
        if f k0
        then find_more_extreme n2 ~f ~k:k0 ~v:v0 user_param
        else find n1 ~f user_param
    and find_more_extreme (T t) ~f ~k ~v user_param =
      match t with
      | Empty _ -> assert false
      | V1 { k1; v1 } ->
        if f k1
        then F.found k1 v1 user_param
        else F.found k v user_param
      | V2 { k11; v11; k1; v1 } ->
        if f k1
        then F.found k1 v1 user_param
        else if f k11
          then F.found k11 v11 user_param
          else F.found k v user_param
      | V3 { k11; v11; k1; v1; k12; v12 } ->
        if f k1
        then if f k12
          then F.found k12 v12 user_param
          else F.found k1 v1 user_param
        else if f k11
          then F.found k11 v11 user_param
          else F.found k v user_param
      | Node { weight; n1; k0; v0; n2 } ->
        if f k0
        then find_more_extreme n2 ~f ~k:k0 ~v:v0 user_param
        else find_more_extreme n1 ~f ~k ~v user_param
  end

  let rec map ~f ~user (T t) =
    match t with
    | Empty _ -> empty
    | V1 { k1; v1 } -> T (V1 { k1; v1 = f k1 v1 user })
    | V2 { k11; v11; k1; v1 } ->
      T (V2 { k11; v11 = f k11 v11 user; k1; v1 = f k1 v1 user })
    | V3 { k11; v11; k1; v1; k12; v12 } ->
      T (V3 { k11; v11 = f k11 v11 user; k1; v1 = f k1 v1 user; k12; v12 = f k12 v12 user })
    | Node { weight; n1; k0; v0; n2 } ->
      T (Node { weight; n1 = map ~f ~user n1; k0; v0 = f k0 v0 user; n2 = map ~f ~user n2 })

  let rec join ~n1 ~k0 ~v0 ~n2 =
    let n1w = weight n1
    and n2w = weight n2
    in
    if valid_input_imbalance n1w n2w
    then balance_shallow ~n1 ~k0 ~v0 ~n2
    else begin
      if n1w > n2w
      then begin
        match n1 with
        | T (Node { weight = _; n1 = n11; k0 = k1; v0 = v1; n2 = n12 }) ->
          balance_shallow ~n1:n11 ~k0:k1 ~v0:v1
            ~n2:(join_right ~n1:n12 ~k0 ~v0 ~n2 ~n2w)
        | T (V3 _) -> balance_shallow ~n1 ~k0 ~v0 ~n2
        | _ ->
          (* Heavy side on invalid balance has to be Node/V3, see proof *)
          assert false
      end
      else begin
        match n2 with
        | T (Node { weight = _; n1 = n21; k0 = k2; v0 = v2; n2 = n22 }) ->
          balance_shallow
            ~n1:(join_left ~n1 ~n1w ~k0 ~v0 ~n2:n21)
            ~k0:k2 ~v0:v2
            ~n2:(n22)
        | T (V3 _) -> balance_shallow ~n1 ~k0 ~v0 ~n2
        | _ -> assert false
      end
    end
  and join_right ~n1 ~k0 ~v0 ~n2 ~n2w =
    let n1w = weight n1 in
    if valid_input_imbalance n1w n2w
    then balance_shallow ~n1 ~k0 ~v0 ~n2
    else match n1 with
      | T (Node { weight = _; n1 = n11; k0 = k1; v0 = v1; n2 = n12 }) ->
          balance_shallow ~n1:n11 ~k0:k1 ~v0:v1
            ~n2:(join_right ~n1:n12 ~k0 ~v0 ~n2 ~n2w)
      | T (V3 _) -> balance_shallow ~n1 ~k0 ~v0 ~n2
      | _ ->  assert false
  and join_left ~n1 ~n1w ~k0 ~v0 ~n2 =
    let n2w = weight n2 in
    if valid_input_imbalance n1w n2w
    then balance_shallow ~n1 ~k0 ~v0 ~n2
    else match n2 with
      | T (Node { weight = _; n1 = n21; k0 = k2; v0 = v2; n2 = n22 }) ->
        balance_shallow
          ~n1:(join_left ~n1 ~n1w ~k0 ~v0 ~n2:n21)
          ~k0:k2 ~v0:v2
          ~n2:(n22)
      | T (V3 _) -> balance_shallow ~n1 ~k0 ~v0 ~n2
      | _ -> assert false

  let rec to_seq = function
    | T (Node { weight = _; n1; k0; v0; n2; }) ->
      Seq.append
        (to_seq n1)
        (Seq.append
           (Seq.singleton (k0,v0))
           (to_seq n2))
    | T (V1 {k1; v1;}) ->
      Seq.singleton (k1, v1)
    | T (V2 {k11; v11; k1; v1;}) ->
      Seq.cons (k11,v11) (Seq.cons (k1,v1) Seq.empty)
    | T (V3 {k11; v11; k1; v1; k12; v12; }) ->
      Seq.cons (k11,v11) (Seq.cons (k1,v1) (Seq.cons (k12, v12) Seq.empty))
    | T (Empty _) -> Seq.empty

  let rec to_rev_seq = function
    | T (Node { weight = _; n1; k0; v0; n2; }) ->
      Seq.append
        (to_rev_seq n2)
        (Seq.append
           (Seq.singleton (k0,v0))
           (to_rev_seq n1))
    | T (V1 {k1; v1;}) ->
      Seq.singleton (k1, v1)
    | T (V2 {k11; v11; k1; v1;}) ->
      Seq.cons (k1,v1) (Seq.cons (k11,v11) Seq.empty)
    | T (V3 {k11; v11; k1; v1; k12; v12; }) ->
      Seq.cons (k12,v12) (Seq.cons (k1,v1) (Seq.cons (k11, v11) Seq.empty))
    | T (Empty _) -> Seq.empty

  let rec to_seq_from from_k = function
    | T (Empty _) -> Seq.empty
    | T (Node { weight = _; n1; k0; v0; n2; }) ->
      begin match%compare K.compare from_k k0 with
        | Eq -> Seq.append (Seq.singleton (k0, v0)) (to_seq n2)
        | Gt -> to_seq_from from_k n2
        | Lt ->
          Seq.append
            (to_seq_from from_k n1)
            (Seq.append
               (Seq.singleton (k0,v0))
               (to_seq n2))
      end
    | T (V1 {k1; v1;}) ->
      begin match%compare K.compare from_k k1 with
        | Gt -> Seq.empty 
        | _ -> Seq.singleton (k1, v1)
      end
    | T (V2 {k11; v11; k1; v1;}) ->
      Seq.append
        begin match%compare K.compare from_k k11 with
          | Gt -> Seq.empty 
          | _ -> Seq.singleton (k11, v11)
        end
        begin match%compare K.compare from_k k1 with
          | Gt -> Seq.empty 
          | _ -> Seq.singleton (k1, v1)
        end
    | T (V3 {k11; v11; k1; v1; k12; v12; }) ->
      Seq.append
        begin match%compare K.compare from_k k11 with
          | Gt -> Seq.empty 
          | _ -> Seq.singleton (k11, v11)
        end
        (Seq.append
           begin match%compare K.compare from_k k1 with
             | Gt -> Seq.empty 
             | _ -> Seq.singleton (k1, v1)
           end
           begin match%compare K.compare from_k k12 with
             | Gt -> Seq.empty 
             | _ -> Seq.singleton (k12, v12)
           end)

  module type Iterator_consumer = sig
    type 'a final
    type 'a state0
    type 'a state1
    type 'a state2
    type 'a state3

    val consume
      : k:K.t -> v:'a
      -> next:('np0 -> 'np1 -> state0:'a state0 -> state1:'a state1 -> state2:'a state2 -> state3:'a state3 -> 'a final) 
      -> 'np0
      -> 'np1
      -> state0:'a state0
      -> state1:'a state1
      -> state2:'a state2
      -> state3:'a state3
      -> 'a final

    val final
      :  state0:'a state0
      -> state1:'a state1
      -> state2:'a state2
      -> state3:'a state3
      -> 'a final

  end

  module Iterator_stack = struct
    type 'v t = (c_node, n_interior, 'v) node list

    let empty = []
  end

  module Iterator(C : Iterator_consumer) = struct
    module Stack = Iterator_stack

    let rec step_down (stack : 'v Stack.t) (T t) ~state0 ~state1 ~state2 ~state3 =
      match t with
      | Node { weight = _; n1; k0; v0; n2 } as n0 ->
        let stack = n0 :: stack in
        step_down stack n1 ~state0 ~state1 ~state2 ~state3
      | V1 { k1; v1; } ->
        C.consume ~k:k1 ~v:v1 ~next:step_up stack () ~state0 ~state1 ~state2 ~state3
      | V2 { k11; v11; k1; v1; } as n ->
        C.consume ~k:k11 ~v:v11 ~next:step_v2_1 stack n ~state0 ~state1 ~state2 ~state3
      | V3 { k11; v11; k1; v1; k12; v12; } as n ->
        C.consume ~k:k11 ~v:v11 ~next:step_v3_1 stack n ~state0 ~state1 ~state2 ~state3
      | Empty _ ->
        step_up stack () ~state0 ~state1 ~state2 ~state3
    and step_up (stack : 'v Stack.t) () ~state0 ~state1 ~state2 ~state3 =
      match stack with
      | [] -> C.final ~state0 ~state1 ~state2 ~state3
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack ->
        C.consume ~k:k0 ~v:v0 ~next:step_down stack n2 ~state0 ~state1 ~state2 ~state3
    and step_v2_1 (stack : 'v Stack.t) (V2 { k11; v11; k1; v1; }) ~state0 ~state1 ~state2 ~state3 =
      C.consume ~k:k1 ~v:v1 ~next:step_up stack () ~state0 ~state1 ~state2 ~state3
    and step_v3_1 (stack : 'v Stack.t) (V3 { k11; v11; k1; v1; k12; v12; } as n) ~state0 ~state1 ~state2 ~state3 =
      C.consume ~k:k1 ~v:v1 ~next:step_v3_12 stack n ~state0 ~state1 ~state2 ~state3
    and step_v3_12 (stack : 'v Stack.t) (V3 { k11; v11; k1; v1; k12; v12; }) ~state0 ~state1 ~state2 ~state3 =
      C.consume ~k:k12 ~v:v12 ~next:step_up stack () ~state0 ~state1 ~state2 ~state3
  end

  (* TODO: The performance of this one is very bad, even though allocaiton is really good.
     Most likely due to too many indirect calls through caml_apply *)
  module Iterator2 = struct
    module Stack = Iterator_stack

    type ('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) with_st =
      st0:'s0 -> st1:'s1 -> st2:'s2 -> st3:'s3 -> st4:'s4 -> st5:'s5 -> st6:'s6 -> 'final

    type ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, 'np0, 'np1) consume_f
      =  k:K.t
      -> v:'a
      -> next:(('a, 'np0, 'np1) next)
      -> 'np0
      -> 'np1
      -> ('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) with_st
    and ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, 'np0, 'np1) next_f
      =  'np0
      -> 'np1
      -> consume:(('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) consume)
      -> final:(('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) final_f)
      -> ('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) with_st
    and ('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) final_f =
      ('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) with_st
    and ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) consume =
      { f : 'np0 'np1. ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, 'np0, 'np1) consume_f }
      [@@unboxed]
    and ('a, 'np0, 'np1) next =
      { f : 's0 's1 's2 's3 's4 's5 's6 'final. ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, 'np0, 'np1) next_f }
      [@@unboxed]

    let rec step_down : 's0 's1 's2 's3 's4 's5 's6 'final . ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, _, _) next_f =
        fun (stack : 'v Stack.t) (T t) ~consume ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6 ->
      match t with
      | Node { weight = _; n1; k0; v0; n2 } as n0 ->
        let stack = n0 :: stack in
        step_down stack n1 ~consume ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
      | V1 { k1; v1; } ->
        consume.f ~k:k1 ~v:v1 ~next:{f = step_up } stack () ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
      | V2 { k11; v11; k1; v1; } as n ->
        consume.f ~k:k11 ~v:v11 ~next:{f = step_v2_1} stack n ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
      | V3 { k11; v11; k1; v1; k12; v12; } as n ->
        consume.f ~k:k11 ~v:v11 ~next:{f = step_v3_1} stack n ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
      | Empty _ ->
        final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
    and step_up : 's0 's1 's2 's3 's4 's5 's6 'final . ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, _, _) next_f =
      fun (stack : 'v Stack.t) () ~consume ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6 ->
      match stack with
      | [] -> final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack ->
        consume.f ~k:k0 ~v:v0 ~next:{f = step_down} stack n2 ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
    and step_v2_1 : 's0 's1 's2 's3 's4 's5 's6 'final . ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, _, _) next_f =
      fun (stack : 'v Stack.t) (V2 { k11; v11; k1; v1; }) ~consume ~final:_ ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6 ->
      consume.f ~k:k1 ~v:v1 ~next:{f = step_up} stack () ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
    and step_v3_1 : 's0 's1 's2 's3 's4 's5 's6 'final . ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, _, _) next_f =
      fun (stack : 'v Stack.t) (V3 { k11; v11; k1; v1; k12; v12; } as n) ~consume ~final:_ ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6 ->
      consume.f ~k:k1 ~v:v1 ~next:{ f = step_v3_12} stack n ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
    and step_v3_12 : 's0 's1 's2 's3 's4 's5 's6 'final . ('a, 's0, 's1, 's2, 's3, 's4, 's5, 's6, 'final, _, _) next_f =
      fun (stack : 'v Stack.t) (V3 { k11; v11; k1; v1; k12; v12; }) ~consume ~final:_ ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6 ->
      consume.f ~k:k12 ~v:v12 ~next:{f = step_up } stack () ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6

    let iter t ~consume ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6 =
      step_down Stack.empty t ~consume ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6
  end


  module type Fold2_folder = sig
    type ('a1, 'a2) acc
    type ('a1, 'a2) user_param

    val both_present : ('a1, 'a2) acc -> ('a1, 'a2) user_param -> k:K.t -> v1:'a1 -> v2:'a2 -> ('a1, 'a2) acc
    val present_1 : ('a1, 'a2) acc -> ('a1, 'a2) user_param -> is_tail:bool -> k:K.t -> v:'a1 -> ('a1, 'a2) acc
    val present_2 : ('a1, 'a2) acc -> ('a1, 'a2) user_param -> is_tail:bool -> k:K.t -> v:'a2 -> ('a1, 'a2) acc
  end

  module [@inline hint] Fold_low2(F : Fold2_folder) = struct
    let fold =
      let rec
        consume_t1_initial : 'np0 'np1. (_, _, _, _, _, _, _, _, 'final, 'np0, 'np1) Iterator2.consume_f =
        fun ~k ~v ~next np0 np1 ~st0:t2 ~st1 ~st2 ~st3 ~st4 ~st5:user_param ~st6:acc ->
        Iterator2.iter t2
          ~consume:{ f = consume_t2 }
          ~final:consume_t1_final (* Should be consume remainder of t1 ? *)
          ~st0:k
          ~st1:v
          ~st2:next
          ~st3:np0
          ~st4:np1
          ~st5:user_param
          ~st6:acc
      and consume_t2 : 'np20 'np21 'np10 'np11. (_, _, _, (_, 'np10, 'np11) Iterator2.next, 'np10, 'np11, 's25, 's26, 'final, 'np20, 'np21) Iterator2.consume_f =
        fun ~k:k2 ~v:v2 ~next:next2 np20 np21 ~st0:k1 ~st1:v1 ~st2:next1 ~st3:np10 ~st4:np11 ~st5:user_param ~st6:acc ->
        match%compare K.compare k1 k2 with
        | Eq ->
          let acc = F.both_present acc user_param ~k:k1 ~v1:v1 ~v2:v2 in
          consume_t1_t2 ~next1 ~np10 ~np11 ~next2 ~np20 ~np21 ~user_param ~acc
        | Lt ->
          let acc = F.present_1 acc user_param ~is_tail:false ~k:k1 ~v:v1 in
          next1.f np10 np11 ~consume:{f = consume_t1} ~final:consume_t2_final ~st0:k2 ~st1:v2 ~st2:next2 ~st3:np20 ~st4:np21 ~st5:user_param ~st6:acc
        | Gt ->
          let acc = F.present_2 acc user_param ~is_tail:false ~k:k2 ~v:v2 in
          next2.f np20 np21 ~consume:{f = consume_t2} ~final:consume_t1_final ~st0:k1 ~st1:v1 ~st2:next1 ~st3:np10 ~st4:np11 ~st5:user_param ~st6:acc
      and consume_t1 : 'np10 'np11 'np20 'np21. (_, _, _, (_, 'np20, 'np21) Iterator2.next, 'np20, 'np21, 's25, 's26, 'final, 'np10, 'np11) Iterator2.consume_f =
        fun ~k:k1 ~v:v1 ~next:next1 np10 np11 ~st0:k2 ~st1:v2 ~st2:next2 ~st3:np20 ~st4:np21 ~st5:user_param ~st6:acc ->
        match%compare K.compare k1 k2 with
        | Eq ->
          let acc = F.both_present acc user_param ~k:k1 ~v1:v1 ~v2:v2 in
          consume_t1_t2 ~next1 ~np10 ~np11 ~next2 ~np20 ~np21 ~acc ~user_param
        | Lt ->
          let acc = F.present_1 acc user_param ~is_tail:false ~k:k1 ~v:v1 in
          next1.f np10 np11 ~consume:{f = consume_t1} ~final:consume_t2_final ~st0:k2 ~st1:v2 ~st2:next2 ~st3:np20 ~st4:np21 ~st5:user_param ~st6:acc
        | Gt ->
          let acc = F.present_2 acc user_param ~is_tail:false ~k:k2 ~v:v2 in
          next2.f np20 np21 ~consume:{f = consume_t2} ~final:consume_t1_final ~st0:k1 ~st1:v1 ~st2:next1 ~st3:np10 ~st4:np11 ~st5:user_param ~st6:acc
      and final : 's0 's1 's2 's3 's4 's5 . ('s0, 's1, 's2, 's3, 's4, 's5, 's6, 'final) Iterator2.final_f =
        fun ~st0 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6:acc ->
        acc
      and consume_t1_final : 'np0 'np1 . (_,_,(_, 'np0, 'np1) Iterator2.next, 'np0, 'np1, _, _, _) Iterator2.final_f =
        fun ~st0:k ~st1:v ~st2:next ~st3:np0 ~st4:np1 ~st5:user_param ~st6:acc ->
        let acc = F.present_1 ~is_tail:true acc user_param ~k ~v in
        next.f np0 np1 ~consume:{f = consume_t1_final_finish} ~final ~st0:() ~st1:() ~st2:() ~st3:() ~st4:() ~st5:user_param ~st6:acc
      and consume_t1_final_finish : 'np0 'np1 . (_, _, _, _, _, _, _, _, _, 'np0, 'np1) Iterator2.consume_f =
        fun ~k ~v ~next np0 np1 ~st0 ~st1 ~st2 ~st3 ~st4 ~st5:user_param ~st6:acc ->
        let acc = F.present_1 ~is_tail:true acc user_param ~k ~v in
        next.f np0 np1 ~consume:{f = consume_t1_final_finish} ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5:user_param ~st6:acc
      and consume_t2_final : 'st0 'st1 'np0 'np1 . (_,_,(_, 'np0, 'np1) Iterator2.next, 'np0, 'np1, _, _, _) Iterator2.final_f =
        fun ~st0:k ~st1:v ~st2:next ~st3:np0 ~st4:np1 ~st5:user_param ~st6:acc ->
        let acc = F.present_2 ~is_tail:true acc user_param ~k ~v in
        next.f np0 np1 ~consume:{f = consume_t2_final_finish} ~final ~st0:() ~st1:() ~st2:() ~st3:() ~st4:() ~st5:user_param ~st6:acc
      and consume_t2_final_no_elem : 'st0 'st1 'np0 'np1 . (_,_,(_, 'np0, 'np1) Iterator2.next, 'np0, 'np1, _, _, _) Iterator2.final_f =
        fun ~st0:() ~st1:() ~st2:next ~st3:np0 ~st4:np1 ~st5:user_param ~st6:acc ->
        next.f np0 np1 ~consume:{f = consume_t2_final_finish} ~final ~st0:() ~st1:() ~st2:() ~st3:() ~st4:() ~st5:user_param ~st6:acc
      and consume_t2_final_finish : 'np0 'np1 . (_, _, _, _, _, _, _, _, _, 'np0, 'np1) Iterator2.consume_f =
        fun ~k ~v ~next np0 np1 ~st0 ~st1 ~st2 ~st3 ~st4 ~st5:user_param ~st6:acc ->
        let acc = F.present_2 ~is_tail:true acc user_param ~k ~v in
        next.f np0 np1 ~consume:{f = consume_t2_final_finish} ~final ~st0 ~st1 ~st2 ~st3 ~st4 ~st5:user_param ~st6:acc
      and consume_t1_t2 : 'np10 'np11 'np20 'np21. next1:((_, 'np10, 'np11) Iterator2.next) -> np10:'np10 -> np11:'np11 -> next2:((_, 'np20, 'np21) Iterator2.next) -> np20:'np20 -> np21:'np21 -> acc:'acc -> user_param:_ -> 'acc =
        fun ~next1 ~np10 ~np11 ~next2 ~np20 ~np21 ~acc ~user_param ->
        next1.f np10 np11 ~consume:{f = consume_t1_t2_phase2 } ~final:consume_t2_final_no_elem ~st0:() ~st1:() ~st2:next2 ~st3:np20 ~st4:np21 ~st5:user_param ~st6:acc
      and consume_t1_t2_phase2 : 'np10 'np11 'np20 'np21. (_,_,_, (_, 'np20, 'np21) Iterator2.next, 'np20, 'np21, _, _, _, 'np10, 'np11) Iterator2.consume_f =
        fun ~k ~v ~next:next1 np10 np11 ~st0 ~st1 ~st2:next2 ~st3:np20 ~st4:np21 ~st5 ~st6:acc ->
        next2.f np20 np21 ~consume:{f = consume_t2} ~final:consume_t1_final ~st0:k ~st1:v ~st2:next1 ~st3:np10 ~st4:np11 ~st5 ~st6:acc
      and final_consume_only_t2 : (_,_,_,_,_,_,_,_) Iterator2.final_f =
        fun ~st0:t2 ~st1 ~st2 ~st3 ~st4 ~st5 ~st6:acc ->
        Iterator2.iter t2
          ~consume:{ f = consume_t2_final_finish }
          ~final:final
          ~st0:()
          ~st1:()
          ~st2:()
          ~st3:()
          ~st4:()
          ~st5
          ~st6:acc
      in
      fun ~init:acc ~user_param t1 t2 ->
        Iterator2.iter t1
          ~consume:{ f = consume_t1_initial }
          ~st0:t2
          ~st1:()
          ~st2:()
          ~st3:()
          ~st4:()
          ~st5:user_param
          ~st6:acc
          ~final:final_consume_only_t2
  end

  module FolderX_2(F : Fold2_folder) = struct
    module Stack = Iterator_stack

    let present1_tail acc user k v = F.present_1 acc user ~is_tail:true ~k ~v
    let present2_tail acc user k v = F.present_2 acc user ~is_tail:true ~k ~v

    type 'c state =
      | Start : _ state
      | Empty : c_empty state
      | V2_1 : c_v2 state
      | V3_1 : c_v3 state
      | V3_12 : c_v3 state

    let rec step :
      'c1 'c2 'nk1 'nk2 'v1 'v2 .
      acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> t1:('c1, 'nk1, 'v1) node -> state1:'c1 state 
      -> stack2:'v2 Stack.t -> t2:('c2, 'nk2, 'v2) node -> state2:'c2 state -> ('v1, 'v2) F.acc =
      fun
        (type c1 c2 nk1 nk2 v1 v2)
        ~(acc : (v1, v2) F.acc) ~user
        ~stack1 ~(t1 : (c1, nk1, v1) node) ~(state1 : c1 state)
        ~stack2 ~(t2 : (c2, nk2, v2) node) ~(state2 : c2 state) ->
        match t1, state1, t2, state2 with
        | Empty _, Empty, _, _ -> finish2 ~acc ~user ~stack2 ~t2 ~state2
        | Empty _, Start, _, _ -> finish2 ~acc ~user ~stack2 ~t2 ~state2
        | _, _, Empty _, Empty -> finish1 ~acc ~user ~stack1 ~t1 ~state1
        | _, _, Empty _, Start -> finish1 ~acc ~user ~stack1 ~t1 ~state1
        | V1 { k1 = k1; v1 = v1; }, _, V1 { k1 = k1'; v1 = v1'; }, _ ->
          begin match%compare K.compare k1 k1' with
            | Eq ->
              let acc = F.both_present acc user ~k:k1 ~v1:v1 ~v2:v1' in
              step_up12 ~acc ~user ~stack1 ~stack2
            | Lt ->
              assert false
            | Gt ->
              assert false
          end
        | _, _, _, _ -> assert false
    and step_value_initial
      : 'c1 'c2 'nk1 'nk2 'v1 'v2 .
      acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> t1:('c1, 'nk1, 'v1) node -> state1:'c1 state -> k1:K.t -> v1:'v1
      -> stack2:'v2 Stack.t -> t2:('c2, 'nk2, 'v2) node -> state2:'c2 state -> k2:K.t -> v2:'v2
      -> ('v1, 'v2) F.acc =
      fun
        (type c1 c2 nk1 nk2 v1 v2)
        ~(acc : (v1, v2) F.acc) ~user
        ~stack1 ~(t1 : (c1, nk1, v1) node) ~(state1 : c1 state) ~k1 ~(v1 : v1)
        ~stack2 ~(t2 : (c2, nk2, v2) node) ~(state2 : c2 state) ~k2 ~(v2 : v2) ->
        match%compare K.compare k1 k2 with
        | Eq ->
          let acc = F.both_present acc user ~k:k1 ~v1 ~v2 in
          step_next_12 ~acc ~user ~stack1 ~t1 ~state1 ~stack2 ~t2 ~state2
        | Lt ->
          let acc = F.present_1 acc user ~is_tail:false ~k:k1 ~v:v1 in
          step_next_1 ~acc ~user ~stack1 ~t1 ~state1 ~stack2 ~t2 ~state2 ~k2 ~v2
    and step_next_12
      : 'c1 'c2 'nk1 'nk2 'v1 'v2 .
      acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> t1:('c1, 'nk1, 'v1) node -> state1:'c1 state
      -> stack2:'v2 Stack.t -> t2:('c2, 'nk2, 'v2) node -> state2:'c2 state
      -> ('v1, 'v2) F.acc =
      fun 
        (type c1 c2 nk1 nk2 v1 v2)
        ~(acc : (v1, v2) F.acc) ~user
        ~stack1 ~(t1 : (c1, nk1, v1) node) ~(state1 : c1 state)
        ~stack2 ~(t2 : (c2, nk2, v2) node) ~(state2 : c2 state) ->
      acc
    and step_next_1
      : 'c1 'c2 'nk1 'nk2 'v1 'v2 .
      acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> t1:('c1, 'nk1, 'v1) node -> state1:'c1 state
      -> stack2:'v2 Stack.t -> t2:('c2, 'nk2, 'v2) node -> state2:'c2 state -> k2:K.t -> v2:'v2
      -> ('v1, 'v2) F.acc =
      fun
        (type c1 c2 nk1 nk2 v1 v2)
        ~(acc : (v1, v2) F.acc) ~user
        ~stack1 ~(t1 : (c1, nk1, v1) node) ~(state1 : c1 state)
        ~stack2 ~(t2 : (c2, nk2, v2) node) ~(state2 : c2 state) ~k2 ~(v2 : v2) ->
        acc
    and step_next_2
      : 'c1 'c2 'nk1 'nk2 'v1 'v2 .
      acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> t1:('c1, 'nk1, 'v1) node -> state1:'c1 state -> k1:K.t -> v1:'v1
      -> stack2:'v2 Stack.t -> t2:('c2, 'nk2, 'v2) node -> state2:'c2 state
      -> ('v1, 'v2) F.acc =
      fun
        (type c1 c2 nk1 nk2 v1 v2)
        ~(acc : (v1, v2) F.acc) ~user
        ~stack1 ~(t1 : (c1, nk1, v1) node) ~(state1 : c1 state) ~k1 ~(v1 : v1)
        ~stack2 ~(t2 : (c2, nk2, v2) node) ~(state2 : c2 state) ->
        acc
    and finish2 :
      'c2 'nk2 'v2 'v1.
      acc:('v1, 'v2) F.acc -> user:('v1, 'v2) F.user_param
      -> stack2:'v2 Stack.t -> t2:('c2, 'nk2, 'v2) node -> state2:'c2 state -> ('v1, 'v2) F.acc =
      fun (type c2 nk2 v1 v2) ~(acc : (v1, v2) F.acc) ~(user : (v1, v2) F.user_param) ~(stack2 : v2 Stack.t) ~(t2 : (c2, nk2, v2) node) ~(state2 : c2 state) ->
      acc
    and finish1 :
      'c1 'nk1 'v2 'v1 .
      acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> t1:('c1, 'nk1, 'v1) node -> state1:'c1 state -> ('v1, 'v2) F.acc =
      fun (type c1 nk1 v1 v2) ~acc ~user ~stack1 ~(t1 : (c1, nk1, v1) node) ~(state1 : c1 state) ->
      acc
    and step_up12 :
      'v1 'v2 .
        acc:('v1, 'v2) F.acc -> user:('v1 , 'v2) F.user_param
      -> stack1:'v1 Stack.t -> stack2:'v2 Stack.t -> ('v1, 'v2) F.acc =
      fun ~acc ~user ~stack1 ~stack2 ->
      acc

    (*{[
    let rec step ~acc ~user ~stack1 ~t1 ~state1 ~stack2 ~t2 ~state2 =
      let T t1, T t2 = t1, t2 in
      match t1, state1, t2, state2 with
      | Node { weight = _; n1; k0; v0; n2 } as n0, _, _, _ ->
        let stack1 = n0 :: stack1 in
        step ~acc ~user ~stack1 ~t1:n1 ~stack2 ~t2
      | _, _, Node { weight = _; n1; k0; v0; n2 } as n0, _ ->
        let stack2 = n0 :: stack2 in
        step ~acc ~user ~stack1 ~t1 ~stack2 ~t2:n1
      | V1 { k1 = k1; v1 = v1; }, _, V1 { k1 = k1'; v1 = v1'; }, _ ->
        begin match%compare K.compare k1 k1' with
          | Eq ->
            let acc = F.both_present acc user ~k:k1 ~v1:v1 ~v2:v1' in
            ()
          | Lt ->
            let acc = F.present_1 acc user ~is_tail:false ~k:k1 ~v:v1 in
            step_up1 ~acc ~user ~stack1 ~stack2 ~t2
          | Gt ->
            let acc = F.present_2 acc user ~is_tail:false ~k:k1' ~v:v1' in
            step_up2 ~acc ~user ~stack1 ~t1 ~stack2
        end
    and step_up12 ~acc ~user ~stack1 ~stack2  =
      match stack1, stack2 with
      | [], [] -> acc
      | [], Node { weight = _; n1 = _; k0; v0; n2 } :: stack2 ->
        let acc = F.present_2 acc user ~is_tail:true ~k:k0 ~v:v0 in
        finish2 ~acc ~user ~stack2 ~t2:n2
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack1, [] ->
        let acc = F.present_1 acc user ~is_tail:true ~k:k0 ~v:v0 in
        finish1 ~acc ~user ~stack1 ~t1:n2
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack1' , Node { weight = _; n1 = _; k0'; v0'; n2' } :: stack2' ->
        match%compare K.compare k0 k0' with
        | Eq ->
          let acc = F.both_present acc user ~k:k0 ~v1:v0 ~v2:v0' in
          step ~acc ~user ~stack1:stack1' ~t1:n2 ~state1:Start ~stack2:stack2' ~t2:n2' ~state2:Start
        | Lt ->
          let acc = F.present_1 acc user ~is_tail:false ~k:k0 ~v:v0 in
          step ~acc ~user ~stack1:stack1' ~t1:n2 ~state1:Start ~stack2 ~t2
        | Gt ->
          let acc = F.present_2 acc user ~is_tail:false ~k:k0' ~v:v0' in
          step ~acc ~user ~stack1 ~t1 ~state1:Start ~stack2:stack2' ~t2:n2' ~state2:Start
    and step_up1 ~acc ~user ~stack1 ~stack2 ~t2 ~state2 =
      match stack1 with
      | [] -> finish2 ~acc ~user ~stack2 ~t2 ~state2
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack1 ->
        let acc = F.present_1 acc user ~is_tail:false ~k:k0 ~v:v0 in
        step ~acc ~user ~stack1 ~t1:n2 ~stack2 ~t2
    and step_up2 ~acc ~user ~stack1 ~t1 ~stack2 =
      match stack2 with
      | [] -> finish1 ~acc ~user ~stack1 ~t1
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack2 ->
        let acc = F.present_2 acc user ~is_tail:false ~k:k0 ~v:v0 in
        step ~acc ~user ~stack1 ~t1 ~stack2 ~t2:n2
    and finish2 ~acc ~user ~stack2 ~t2 =
      ()
    and finish1 ~acc ~user ~stack1 ~t1 =
      ()





    let rec step_down (stack : 'v Stack.t) (T t) ~state0 ~state1 ~state2 ~state3 =
      match t with
      | Node { weight = _; n1; k0; v0; n2 } as n0 ->
        let stack = n0 :: stack in
        step_down stack n1 ~state0 ~state1 ~state2 ~state3
      | V1 { k1; v1; } ->
        C.consume ~k:k1 ~v:v1 ~next:step_up stack () ~state0 ~state1 ~state2 ~state3
      | V2 { k11; v11; k1; v1; } as n ->
        C.consume ~k:k11 ~v:v11 ~next:step_v2_1 stack n ~state0 ~state1 ~state2 ~state3
      | V3 { k11; v11; k1; v1; k12; v12; } as n ->
        C.consume ~k:k11 ~v:v11 ~next:step_v3_1 stack n ~state0 ~state1 ~state2 ~state3
      | Empty _ ->
        step_up stack () ~state0 ~state1 ~state2 ~state3
    and step_up (stack : 'v Stack.t) () ~state0 ~state1 ~state2 ~state3 =
      match stack with
      | [] -> C.final ~state0 ~state1 ~state2 ~state3
      | Node { weight = _; n1 = _; k0; v0; n2 } :: stack ->
        C.consume ~k:k0 ~v:v0 ~next:step_down stack n2 ~state0 ~state1 ~state2 ~state3
    and step_v2_1 (stack : 'v Stack.t) (V2 { k11; v11; k1; v1; }) ~state0 ~state1 ~state2 ~state3 =
      C.consume ~k:k1 ~v:v1 ~next:step_up stack () ~state0 ~state1 ~state2 ~state3
    and step_v3_1 (stack : 'v Stack.t) (V3 { k11; v11; k1; v1; k12; v12; } as n) ~state0 ~state1 ~state2 ~state3 =
      C.consume ~k:k1 ~v:v1 ~next:step_v3_12 stack n ~state0 ~state1 ~state2 ~state3
    and step_v3_12 (stack : 'v Stack.t) (V3 { k11; v11; k1; v1; k12; v12; }) ~state0 ~state1 ~state2 ~state3 =
      C.consume ~k:k12 ~v:v12 ~next:step_up stack () ~state0 ~state1 ~state2 ~state3
       ]} *)
  end

end

module type S_stdlib = sig
  module Ordered : Map.OrderedType

  module M : module type of Make(Ordered)

  include Map.S with type key = Ordered.t
                 and type 'a t = 'a M.t
end

module [@inline always] Stdlib_make(O : Map.OrderedType)
    : S_stdlib with module Ordered = O
= struct
  module Ordered = O
  module M = Make(Ordered)

  let compare_x a b = O.compare a b

  type key = O.t

  type 'a t = 'a M.t

  let empty = M.empty

  let add k v t = M.insert_or_replace t k v

  module Add_to_list = M.Make_change(struct
      type 'a user = 'a

      type 'a t_p = 'a list

      let existing cin ~delete_fun ~replace_fun ~unchanged_fun k v' v =
        replace_fun cin (v :: v')

      let missing cin1 cin2 ~insert_fun ~unchanged_fun k v =
        insert_fun cin1 cin2 [ v ]

      end)

  let add_to_list k v t = Add_to_list.change t k v

  module Update = M.Make_change(struct
      type 'a user = 'a option -> 'a option
      type 'a t_p = 'a

      let existing cin ~delete_fun ~replace_fun ~unchanged_fun k v f =
        match f (Some v) with
        | None -> delete_fun cin
        | Some v' -> replace_fun cin v'

      let missing cin1 cin2 ~insert_fun ~unchanged_fun k f =
        match f None with
        | None -> unchanged_fun cin1
        | Some v' -> insert_fun cin1 cin2 v'
    end)

  let update k f t =
    Update.change t k f

  let singleton k1 v1 = M.T (V1 { k1; v1})

  let remove k t = M.delete t k

  let merge _ = assert false

  (*
  let union a b =
    let a,b =
      if M.weight a > M.weight b
      then b, a
      else a, b
    in
    M.fold_high ~init:b
      ~user:()
      ~f:(fun b () k v -> M.insert_or_replace b k v)
      a
     *)
  let union _ _ = assert false

  let cardinal t = M.size t

  let bindings t : _ list =
    M.fold_high ~init:[] ~user:()
      ~f:(fun acc () k v -> (k, v) :: acc) t

  module Min_binding = M.Find_min(struct
      type 'a user = unit
      type 'a return = key * 'a
      let found k v _ = (k, v)
      let missing _ = raise Not_found
    end)

  let min_binding t = Min_binding.find t ()

  module Min_binding_opt = M.Find_min(struct
      type 'a user = unit
      type 'a return = (key * 'a) option
      let found k v _ = Some (k, v)
      let missing _ = None
    end)

  let min_binding_opt t = Min_binding_opt.find t ()

  module Max_binding = M.Find_max(struct
      type 'a user = unit
      type 'a return = key * 'a
      let found k v _ = (k, v)
      let missing _ = raise Not_found
    end)

  let max_binding t = Max_binding.find t ()

  module Max_binding_opt = M.Find_max(struct
      type 'a user = unit
      type 'a return = (key * 'a) option
      let found k v _ = Some (k, v)
      let missing _ = None
    end)

  let max_binding_opt t = Max_binding_opt.find t ()

  let choose = min_binding
  let choose_opt = min_binding_opt

  let find k t = M.find_exn t k

  let find_opt k t = M.find_opt t k

  module Find_first = M.Find_first(struct
      type 'a user = unit
      type 'a return = key * 'a
      let found k v _ = (k, v)
      let missing _ = raise Not_found
    end)

  let find_first f t = Find_first.find t ~f ()

  module Find_first_opt = M.Find_first(struct
      type 'a user = unit
      type 'a return = (key * 'a) option
      let found k v _ = Some (k, v)
      let missing _ = None
    end)

  let find_first_opt f t = Find_first_opt.find t ~f ()

  module Find_last = M.Find_last(struct
      type 'a user = unit
      type 'a return = key * 'a
      let found k v _ = (k, v)
      let missing _ = raise Not_found
    end)

  let find_last f t = Find_last.find t ~f ()

  module Find_last_opt = M.Find_last(struct
      type 'a user = unit
      type 'a return = (key * 'a) option
      let found k v _ = Some (k, v)
      let missing _ = None
    end)

  let find_last_opt f t = Find_last_opt.find t ~f ()

  let iter f t =
    M.fold_low ~init:() ~user:f
      ~f:(fun () f k v -> f k v) t

  let fold f t acc =
    M.fold_low ~init:acc ~user:f
      ~f:(fun acc f k v -> f k v acc) t

  let map f t =
    M.map ~f:(fun _k v f -> f v) ~user:f t

  let mapi f t =
    M.map ~f:(fun k v f -> f k v) ~user:f t

  let filter _ = assert false

  let filter_map _ = assert false

  let partition _ = assert false

  let split _ = assert false

  let is_empty = function
    | M.T (Empty _) -> true
    | _ -> false

  let is_singleton = function
    | M.T (V1 _) -> true
    | _ -> false

  let singleton_to_binding = function
    | M.T (V1 { k1; v1 }) -> Some (k1, v1)
    | _ ->  None

  module Mem = M.Make_find(struct
      type 'a user = unit
      type 'a return = bool
      let found _ _ _ = true
      let missing _ _ = false
    end)

  let mem k t = Mem.find t k ()

  module Equal_folder = struct
    type ('a1, 'a2) acc = exn
    type ('a1, 'a2) user_param = 'a1 -> 'a2 -> bool

    let both_present e f ~k ~v1 ~v2 =
      if f v1 v2
      then e
      else raise e

    let present_1 e f ~is_tail ~k ~v =
      raise e

    let present_2 e f ~is_tail ~k ~v =
      raise e
  end

  module Equal = M.Fold_low2(Equal_folder)

  let equal f t1 t2 = 
    let exception Unequal in
    try
      Equal.fold
        ~init:Unequal
        ~user_param:f
        t1 t2
      |> (ignore : exn -> unit);
      true
    with
    | Unequal -> false

  module Compare_folder = struct
    type ('a1, 'a2) acc = { f : 'a . (int -> 'a) } [@@unboxed]
    type ('a1, 'a2) user_param = 'a1 -> 'a2 -> int

    let both_present (e : (_,_) acc) f ~k ~v1 ~v2 =
      match%compare f v1 v2 with
      | Eq -> e
      | Lt -> e.f (-1)
      | Gt -> e.f 1

    let present_1 e f ~is_tail ~k ~v =
      if is_tail
      then e.f (1)
      else e.f (-1)

    let present_2 e f ~is_tail ~k ~v =
      if is_tail
      then e.f (-1)
      else e.f (1)
  end

  module Compare = M.Fold_low2(Compare_folder)

  let compare f t1 t2 =
    let exception Compare of int in
    let e i = raise (Compare i) in
    try
      Compare.fold
        ~init:{f = e }
        ~user_param:f
        t1 t2
      |> (ignore : (_,_) Compare_folder.acc -> unit);
      0
    with
    | Compare i -> i


  let for_all f t = assert false

  let exists f t = assert false

  let to_list = bindings

  let of_list l =
    List.fold_left
      (fun t (k, v) -> add k v t) empty l

  let to_seq = M.to_seq

  let to_rev_seq = M.to_rev_seq

  let to_seq_from = M.to_seq_from

  let add_seq s t = Seq.fold_left (fun acc (k, v) -> M.insert_or_replace acc k v)  empty s

  let of_seq s = add_seq s empty
end


module Std_int = Stdlib_make(Int)
