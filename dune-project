(lang dune 3.7)

(name why3_elpi)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name why3_elpi)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune why3 elpi)
 (allow_empty)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
