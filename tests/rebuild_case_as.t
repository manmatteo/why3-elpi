The branch API should support explicit reconstruction of as-pattern branches.

  $ WHY3_ELPI_PROGRAM=../examples/rebuild_case_as.elpi why3 prove pattern_as_goal.mlw --extra-config why3extra.test.conf -D why3 -a "lp rebuild-case-as" 2>&1 | sed -n -E '/^goal rebuild_case_as|match xs with|Cons x tl as whole|whole = whole \/\\ tl = tl \/\\ x = x/p'
  goal rebuild_case_as :
    match xs with
    | Cons x tl as whole -> whole = whole /\ tl = tl /\ x = x

  $ WHY3_ELPI_PROGRAM=../examples/rebuild_case_as.elpi why3 prove pattern_as_goal.mlw --extra-config why3extra.test.conf -D why3 -a "lp rebuild-case-as" 2>&1 | sed -n '/Undeclared globals/p' | wc -l
  0
