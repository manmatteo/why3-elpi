typed case wrapper

  $ why3 prove case_api.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_case p" 2>&1 | sed -n -E '/^axiom h[0-9]* : (not )?p$/p;/^goal split_case : q$/p'
  axiom h : p
  goal split_case : q
  axiom h1 : not p
  goal split_case : q
