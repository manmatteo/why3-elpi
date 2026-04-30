Extracted subterms should retain recoverable attrs when a transform opens binders.

  $ why3 prove term_attrs_demo.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_check_open_term_attrs" 2>&1 | sed -n '/goal one\|\[@body\]\|\[@test\]\|k 0 1 w = 0/p'
  goal one :
     [@body]
     (infix_at (infix_at ([@test] fun (y0:c) (y1:c) (y2:c) -> ff y0 y1 y2) u) v)
     w = True -> k 0 1 w = 0
