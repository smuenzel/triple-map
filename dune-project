(lang dune 3.22)
(using rocq 0.12)
(using cinaps 1.3)

(name triple_map)

(generate_opam_files true)

(source
 (github smuenzel/triple-map))

(authors "Stefan Muenzel <source@s.muenzel.net>")

(maintainers "Stefan Muenzel <source@s.muenzel.net>")

(license MPL-2.0)

(package
 (name triple_map)
 (synopsis "An efficient map implementation")
 (description "An efficient map implementation")
 (depends (ocaml (>= 5.1.0)) ppx_expect ppx_jane base ppxlib core ppx_sexp_conv ocaml-option-flambda)
 (tags
  (map)))
