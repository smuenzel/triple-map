open! Core
open! Core_bench

module Test_data = struct
  let lengths = [ 1; 8;10;16;20;64;100;1000;1024;65536; 100_000; 1_000_000; 16_777_216 ]

  module Int = struct
    module Sorted = struct
      let make length =
        lazy begin
          Array.init length ~f:(fun i -> 2*i)
        end

      let args =
        List.map lengths ~f:(fun length ->
          Int.to_string_hum length, make length)
    end
  end
end

module type Map_functor = functor (M : Stdlib.Map.OrderedType) -> Stdlib.Map.S with type key = M.t

module Make (Make : Map_functor) = struct
  module IntMap = Make (Int)

  let find =
    Bench.Test.create_parameterised
      ~name:"find_opt(in-order).found"
      ~args:Test_data.Int.Sorted.args
      (fun ar ->
         let ar = Lazy.force ar in
         let map = Array.fold ~init:IntMap.empty ar ~f:(fun acc i -> IntMap.add i i acc) in
         let length = Array.length ar in
         let i = ref 0 in
         Staged.stage
           (fun () ->
              let (_ : int option) = Sys.opaque_identity (IntMap.find_opt ar.(!i mod length) map) in
              incr i
           )
      )

  let find_half =
    Bench.Test.create_parameterised
      ~name:"find_opt(in-order).half_found"
      ~args:Test_data.Int.Sorted.args
      (fun ar ->
         let ar = Lazy.force ar in
         let map = Array.fold ~init:IntMap.empty ar ~f:(fun acc i -> IntMap.add i i acc) in
         let length = Array.length ar in
         let i = ref 0 in
         Staged.stage
           (fun () ->
              let (_ : int option) = Sys.opaque_identity (IntMap.find_opt (ar.(!i mod length)/2) map) in
              incr i
           )
      )

  let find_neg =
    Bench.Test.create_parameterised
      ~name:"find_opt(in-order).not_found"
      ~args:Test_data.Int.Sorted.args
      (fun ar ->
         let ar = Lazy.force ar in
         let map = Array.fold ~init:IntMap.empty ar ~f:(fun acc i -> IntMap.add i i acc) in
         let length = Array.length ar in
         let i = ref 0 in
         Staged.stage
           (fun () ->
              let (_ : int option) = Sys.opaque_identity (IntMap.find_opt (1 + ar.(!i mod length)) map) in
              incr i
           )
      )

  let tests =
    [ find
    ; find_neg
    ; find_half
    ]
end

module Stdlib_test = Make (Stdlib.Map.Make)
module Triple_test = Make (Triple_map.Triple.Stdlib_make)

let command =
  Command.group
    ~summary:""
    [ "stdlib", Bench.make_command Stdlib_test.tests
    ; "triple", Bench.make_command Triple_test.tests
    ]

let () =
  Command_unix.run
    command
