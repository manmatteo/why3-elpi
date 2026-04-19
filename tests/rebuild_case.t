The branch API should support structural reconstruction of Why3 match terms.

  $ WHY3_ELPI_PROGRAM=../examples/rebuild_case.elpi why3 prove pattern_goal.mlw --extra-config why3extra.test.conf -D why3 -a "lp rebuild-case" 2>&1 | sed -n -E '/^goal rebuild_case|match xs with|Cons x tl|Nil -> x = x|Cons y ys -> y = y \/\\ ys = ys/p'
  goal rebuild_case :
    match xs with
    | Cons x tl ->
        | Nil -> x = x
        | Cons y ys -> y = y /\ ys = ys

  $ WHY3_ELPI_PROGRAM=../examples/rebuild_case.elpi why3 prove pattern_goal.mlw --extra-config why3extra.test.conf -D why3 -a "lp rebuild-case" 2>&1 | sed -n '/Undeclared globals/p' | wc -l
  0
