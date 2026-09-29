
module type StandardOrdered = sig
  type t

  val compare : t -> t -> int
end

module Param = struct
  module type Change = sig
    module K : StandardOrdered

    type 'a t_p
    type 'a user

    val existing
      :  'cin
      -> delete_fun:('cin -> 'cout)
      -> replace_fun:('cin -> 'a t_p -> 'cout)
      -> unchanged_fun : ('cin -> 'cout)
      -> K.t
      -> 'a t_p
      -> 'a user
      -> 'cout

    val missing
      :  'cin1
      -> 'cin2
      -> insert_fun:('cin1 -> 'cin2 -> 'a t_p -> 'cout)
      -> unchanged_fun : ('cin1 -> 'cout)
      -> K.t
      -> 'a user
      -> 'cout
  end

  module type Find = sig
    module K : StandardOrdered

    type ('a, 'r) user
    type ('a, 'r) return

    val found : K.t -> 'a -> ('a, 'r) user -> ('a, 'r) return
    val missing : K.t -> ('a, 'r) user -> ('a, 'r) return
  end

  module type Find_extremum = sig
    module K : StandardOrdered

    type 'a user
    type 'a return

    val found : K.t -> 'a -> 'a user -> 'a return
    val missing : 'a user -> 'a return
  end

  module type Iterator = sig
    module K : StandardOrdered

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

  module type Fold2 = sig
    module K : StandardOrdered

    type ('a1, 'a2) acc
    type ('a1, 'a2) user_param

    val both_present : ('a1, 'a2) acc -> ('a1, 'a2) user_param -> k:K.t -> v1:'a1 -> v2:'a2 -> ('a1, 'a2) acc
    val present_1 : ('a1, 'a2) acc -> ('a1, 'a2) user_param -> is_tail:bool -> k:K.t -> v:'a1 -> ('a1, 'a2) acc
    val present_2 : ('a1, 'a2) acc -> ('a1, 'a2) user_param -> is_tail:bool -> k:K.t -> v:'a2 -> ('a1, 'a2) acc
  end

  module type Merge = sig
    module K : StandardOrdered

    type ('a1, 'a2, 'r) res
    type ('a1, 'a2, 'r) user_param

    val both_present : ('a1, 'a2, 'r) user_param -> k:K.t -> v1:'a1 -> v2:'a2 -> erase:'cout -> map:(('a1, 'a2, 'r) res -> 'cout) -> 'cout
    val present_1 : ('a1, 'a2, 'r) user_param -> k:K.t -> v:'a1 -> erase:'cout -> map:(('a1, 'a2, 'r) res -> 'cout) -> 'cout
    val present_2 : ('a1, 'a2, 'r) user_param -> k:K.t -> v:'a2 -> erase:'cout -> map:(('a1, 'a2, 'r) res -> 'cout) -> 'cout
  end
end

module Operation = struct
  module type Change = sig
    module K : StandardOrdered
    module C : Param.Change with module K := K
    type +!'v t

    val change : 'a C.t_p t -> K.t -> 'a C.user -> 'a C.t_p t
  end

  module type Find = sig
    module K : StandardOrdered
    module C : Param.Find with module K := K
    type +!'v t

    val find : 'v t -> K.t -> ('v, 'r) C.user -> ('v, 'r) C.return
  end

  module type Find_extremum = sig
    module K : StandardOrdered
    module C : Param.Find_extremum with module K := K
    type +!'v t

    val find : 'v t -> 'v C.user -> 'v C.return
  end

  module type Find_extremum_f = sig
    module K : StandardOrdered
    module C : Param.Find_extremum with module K := K
    type +!'v t

    (* CR smuenzel: [f] should take user as arg *)
    val find : 'v t -> f:(K.t -> bool) -> 'v C.user -> 'v C.return
  end

  module type Iterator = sig
    module K : StandardOrdered
    module C : Param.Iterator with module K := K
    module Stack : sig
      type 'v t
      val empty : 'v t
    end
    type +!'v t

    val step_down : 'v Stack.t -> 'v t -> state0:'v C.state0 -> state1:'v C.state1 -> state2:'v C.state2 -> state3:'v C.state3 -> 'v C.final
  end

  module type Fold2 = sig
    module K : StandardOrdered
    module C : Param.Fold2 with module K := K
    type +!'v1 t

    val fold
      :  init: ('v1, 'v2) C.acc
      -> user_param: ('v1, 'v2) C.user_param
      -> 'v1 t
      -> 'v2 t
      -> ('v1, 'v2) C.acc
  end
end

module type S = sig
  module K : StandardOrdered

  type +!'v t

  val empty : 'v t
  val size : 'v t -> int

  val join : n1:'v t -> k0:K.t -> v0:'v -> n2:'v t -> 'v t

  module Make_change(C : Param.Change with module K := K)
    : Operation.Change with module K := K
                        and module C = C
                        and type 'v t := 'v t

  module Delete
    : Operation.Change with module K := K
                        and type 'a C.user = unit
                        and type 'v C.t_p = 'v
                        and type 'v t := 'v t

  val delete : 'v t -> K.t -> 'v t

  module Insert_or_replace
    : Operation.Change with module K := K
                        and type 'a C.user = 'a
                        and type 'v C.t_p = 'v
                        and type 'v t := 'v t

  val insert_or_replace : 'v t -> K.t -> 'v -> 'v t

  module Make_find(C : Param.Find with module K := K)
    : Operation.Find with module K := K
                      and module C = C
                      and type 'v t := 'v t

  module Find_exn
    : Operation.Find with module K := K
                      and type 'v t := 'v t
                      and type ('a, 'r) C.user = unit
                      and type ('a, 'r) C.return = 'a

  val find_exn : 'v t -> K.t -> 'v

  module Find_opt
    : Operation.Find with module K := K
                      and type 'v t := 'v t
                      and type ('a, 'r) C.user = unit
                      and type ('a, 'r) C.return = 'a option

  val find_opt : 'v t -> K.t -> 'v option

  val fold_low : init:'a -> user:'b -> f:('a -> 'b -> K.t -> 'c -> 'a) -> 'c t -> 'a
  val fold_high : init:'a -> user:'b -> f:('a -> 'b -> K.t -> 'c -> 'a) -> 'c t -> 'a

  val sexp_of_t : (K.t -> Sexplib0.Sexp.t) -> ('a -> Sexplib0.Sexp.t) -> 'a t -> Sexplib0.Sexp.t
  val t_of_sexp : (Sexplib0.Sexp.t -> K.t) -> (Sexplib0.Sexp.t -> 'a) -> Sexplib0.Sexp.t -> 'a t

  module Find_min(C : Param.Find_extremum with module K := K)
    : Operation.Find_extremum with module K := K
                               and module C := C
                               and type 'v t := 'v t

  module Find_max(C : Param.Find_extremum with module K := K)
    : Operation.Find_extremum with module K := K
                               and module C := C
                               and type 'v t := 'v t

  module Find_first(C : Param.Find_extremum with module K := K)
    : Operation.Find_extremum_f with module K := K
                                 and module C := C
                                 and type 'v t := 'v t

  module Find_last(C : Param.Find_extremum with module K := K)
    : Operation.Find_extremum_f with module K := K
                                 and module C := C
                                 and type 'v t := 'v t

  val map: f:(K.t -> 'a -> 'user -> 'b) -> user:'user -> 'a t -> 'b t

  val to_seq: 'a t -> (K.t * 'a) Seq.t
  val to_rev_seq: 'a t -> (K.t * 'a) Seq.t
  val to_seq_from : K.t -> 'a t -> (K.t * 'a) Seq.t

  module Make_fold2(C : Param.Fold2 with module K := K)
    : Operation.Fold2 with module K := K
                        and module C := C
                        and type 'v t := 'v t
end

module type S_stdlib = sig
  module Ordered : Map.OrderedType

  module M : S with module K = Ordered

  include Map.S with type key = Ordered.t
                 and type 'a t = 'a M.t
end

module type Triple = sig
  module Make(K : StandardOrdered) : S with module K = K
  module Stdlib_make(O : Map.OrderedType) : S_stdlib with module Ordered = O
end
