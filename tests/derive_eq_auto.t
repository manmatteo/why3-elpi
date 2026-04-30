Deriving structural equality for algebraic datatypes

The color type has no type parameters so synthesis always succeeds.
The synthesized equality constant must appear in the task:
  $ why3 prove derive_eq_auto.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_derive_eq_auto" 2>&1 | sed -n -E '/^(goal test_color_eq|constant eq_color )/p'
  constant eq_color : color -> color -> bool =
  goal test_color_eq : color_eq_works eq_color

The tree type is polymorphic; synthesis is not yet implemented for it,
so the existential remains open:
  $ why3 prove derive_eq_auto.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_derive_eq_auto" 2>&1 | sed -n '/^goal test_tree_eq/,/^end$/p'
  goal test_tree_eq :
    exists eq_tree:tree int -> tree int -> bool. tree_eq_works eq_tree
  
  end


