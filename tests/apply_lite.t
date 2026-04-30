Simple apply tactic

  $ why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_lite" 2>&1 | sed -n -E '/^goal (two|go1|plus)/p'
  goal two : p -> q
  goal go1 : (a -> b) -> a -> b
  goal plus :

  $ why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_lite" 2>&1 | sed -n '/Undeclared globals/p' | wc -l
  0

Typed prsymbol wrapper

  $ why3 prove apply_lite_by.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_lite_by hpq" 2>&1 | sed -n -E '/^goal g/p'
  goal g : p
