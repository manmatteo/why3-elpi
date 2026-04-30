The branch API should support explicit reconstruction of as-pattern branches.

  $ why3 prove pattern_as_goal.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_rebuild_case_as" 2>&1 | sed -n -E '/^goal rebuild_case_as|match xs with|Cons x tl as whole|whole = whole \/\\ tl = tl \/\\ x = x/p'
  goal rebuild_case_as :
    match xs with
    | Cons x tl as whole -> whole = whole /\ tl = tl /\ x = x

  $ why3 prove pattern_as_goal.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_rebuild_case_as" 2>&1 | sed -n '/Undeclared globals/p' | wc -l
  0
