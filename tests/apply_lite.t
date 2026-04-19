Simple apply tactic

  $ WHY3_ELPI_PROGRAM=../examples/apply_lite.elpi why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "lp apply-lite" 2>&1 | sed -n -E '/^goal (two|go1|plus)/p'
  goal two : p -> q
  goal go1 : (a -> b) -> a -> b
  goal plus :

  $ WHY3_ELPI_PROGRAM=../examples/apply_lite.elpi why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "lp apply-lite" 2>&1 | sed -n '/Undeclared globals/p' | wc -l
  0
