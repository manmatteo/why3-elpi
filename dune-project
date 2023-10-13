(lang dune 3.7)

(name why3_elpi)

(generate_opam_files true)

(source
 (github manmatteo/why3-elpi))

(authors "Matteo Manighetti")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name why3_elpi)
 (synopsis "Access the Why3 API from Elpi")
 (description "Bindings to the Why3 API in λProlog using the Elpi library.")
 (depends ocaml dune why3 elpi)
(allow_empty)
 (tags
  (topics "to describe" your project)))