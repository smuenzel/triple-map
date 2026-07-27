open! Base
open! Ppxlib
open! Ast_builder.Default

module M = struct
  module T = struct
    type t = | Lt | Eq | Gt
    let compare = Stdlib.compare
    let sexp_of_t _ = assert false
  end
  include T
  include Comparator.Make(T)
end

let e = Set.empty (module M)
open M

let expand_match ~match_loc matched_expr (cases : cases) =
  let _, cases' =
    List.fold_map ~init:e cases ~f:(fun acc pcase ->
        let loc = pcase.pc_rhs.pexp_loc in
        let merge_guard c guard' = 
          match pcase.pc_guard with
          | None ->
            let acc' = Set.add acc c in
            if Set.length acc' = 3
            then acc', [%pat? _], None
            else acc', [%pat? __mc_v], Some guard'
          | Some guard ->
            acc
          , [%pat? __mc_v]
          , Some [%expr [%e guard'] && [%e guard]]
        in
        match pcase.pc_lhs with
        | [%pat? _ ] ->
          let acc' =
            match pcase.pc_guard with
            | None -> Set.of_list (module M) [ Lt; Eq; Gt ]
            | Some _ -> acc
          in
          acc'
        , case ~lhs:[%pat? _] ~guard:pcase.pc_guard ~rhs:pcase.pc_rhs
        | [%pat? Lt ] ->
          let acc', lhs, guard = merge_guard Lt [%expr __mc_v < 0] in
          acc'
        , case ~lhs
            ~guard
            ~rhs:pcase.pc_rhs
        | [%pat? Eq ] ->
          let acc' =
            match pcase.pc_guard with
            | None -> Set.add acc Eq
            | Some _ -> acc
          in
          acc'
        , case ~lhs:[%pat? 0] 
            ~guard:pcase.pc_guard
            ~rhs:pcase.pc_rhs
        | [%pat? Gt ] -> 
          let acc', lhs, guard = merge_guard Gt [%expr __mc_v > 0] in
          acc'
        , case ~lhs
            ~guard
            ~rhs:pcase.pc_rhs
        | _ ->
          Location.raise_errorf ~loc "can only match _,Lt,Eq,Gt"
      )
  in
  pexp_match ~loc:match_loc
    matched_expr
    cases'

let expand_match ~loc ~path:_ ~arg:_ e =
  Ast_pattern.parse
    Ast_pattern.(pexp_match __ __)
    loc
    e
    ~on_error:(fun () ->
      Location.raise_errorf ~loc "[%%compare ] must apply to a match statement")
    (expand_match ~match_loc:e.pexp_loc)

let match_compare =
  Extension.declare_with_path_arg
    "compare"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    expand_match

let () = Driver.register_transformation "compare" ~extensions:[ match_compare ]
