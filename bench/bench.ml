open! Core
open! Core_bench

module Test_data = struct
  let lengths = [ 1; 8; 10;16;20;64;100;1000;1024;65536; 100_000; 1_000_000; 16_777_216 ]

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

let get_coe0 kind a =
  let regressions = Bench.Analysis_result.regressions a in
  let regression =
    Array.find_exn
      ~f:(fun r ->
          Poly.equal kind (Bench.Analysis_result.Regression.responder r)
        )
      regressions
  in
  let coe =
    Bench.Analysis_result.Regression.coefficients regression
  in
  coe.(0)

let responder_ratio kind a b =
  let coe_a = get_coe0 kind a in
  let coe_b = get_coe0 kind b in
  let estimate_a =
    Bench.Analysis_result.Coefficient.estimate
      coe_a
  in
  let estimate_b =
    Bench.Analysis_result.Coefficient.estimate
      coe_b
  in
  Percent.of_mult
    (estimate_b /. estimate_a)
  |> Percent.to_string

let span_string s =
  Time_float.Span.(of_ns s |> to_string_hum)

let word_string s =
  Printf.sprintf "%0.2fwd" s

let responder_string to_string kind a =
  let coe = get_coe0 kind a in
  let estimate =
    Bench.Analysis_result.Coefficient.estimate
      coe
  in
  (* Approx, don't care about unequal span*)
  let plus_minus =
    Bench.Analysis_result.Coefficient.ci95 coe
    |> Option.value_exn
    |> Bench.Analysis_result.Ci95.ci95_abs_err ~estimate
    |> fun (lower, upper) ->
    (Float.abs upper +. Float.abs lower) /. 2.0
  in
  Printf.sprintf "%s ± %s"
    (to_string estimate)
    (to_string plus_minus)

let run ~stdlib ~triple =
  let quota =
    Bench.Quota.Span (Time_float.Span.of_sec 2.)
  in
  let bootstrap_trials = 4 in
  let analysis_timing =
    Bench.Analysis_config.create
      ~bootstrap_trials
      ~responder:`Nanos
      ~predictors:[ `Runs ]
      ()
  in
  let analysis_minor_words =
    Bench.Analysis_config.create
      ~bootstrap_trials
      ~responder:`Minor_allocated
      ~predictors:[ `Runs ]
      ()
  in
  let run_config =
    Bench.Run_config.create
      ~quota
      ()
  in
  let measurements_stdlib =
    Bench.measure
      ~run_config
      stdlib
  in
  let measurements_triple =
    Bench.measure
      ~run_config
      triple
  in
  let analyze test =
    Bench.analyze
      ~analysis_configs:[ analysis_timing; analysis_minor_words ]
      test
    |> Or_error.ok_exn
  in
  let analysis_stdlib = List.map measurements_stdlib ~f:analyze in
  let analysis_triple = List.map measurements_triple ~f:analyze in
  let analysis = List.zip_exn analysis_stdlib analysis_triple in
  let columns =
    [ Ascii_table.Column.create "Name"
        (fun (a,_) ->
           Bench.Analysis_result.name a
        )
    ; Ascii_table.Column.create "timing (stdlib)"
        (fun (a,_) ->
           responder_string span_string `Nanos a
        )
    ; Ascii_table.Column.create "timing (triple)"
        (fun (_,a) ->
           responder_string span_string `Nanos a
        )
    ; Ascii_table.Column.create "timing ratio"
        (fun (a,b) ->
           responder_ratio `Nanos a b
        )
    ; Ascii_table.Column.create "minor words (stdlib)"
        (fun (a,_) ->
           responder_string word_string `Minor_allocated a
        )
    ; Ascii_table.Column.create "minor words (triple)"
        (fun (_,a) ->
           responder_string word_string `Minor_allocated a
        )
    ; Ascii_table.Column.create "minor words ratio"
        (fun (a,b) ->
           responder_ratio `Minor_allocated a b
        )
    ]
  in
  Ascii_table.output
    ~limit_width_to:180
    ~oc:Stdlib.stdout
    columns
    analysis

let find_command =
  Command.basic
    ~summary:""
    [%map_open.Command
      let () = return ()
      in
      fun () ->
        run
          ~stdlib:Stdlib_test.tests
          ~triple:Triple_test.tests
    ]


let command =
  Command.group
    ~summary:""
    [ "stdlib", Bench.make_command Stdlib_test.tests
    ; "triple", Bench.make_command Triple_test.tests
    ; "find", find_command
    ]

let () =
  Command_unix.run
    command
