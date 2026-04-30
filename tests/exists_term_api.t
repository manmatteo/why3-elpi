typed term argument wrapper

  $ why3 prove exists_term.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_exists_term 1" 2>&1 | sed -n -E '/^goal exists_term_simple|^  1 = 1/p'
  goal exists_term_simple : 1 = 1
