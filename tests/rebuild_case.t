The branch API should support structural reconstruction of Why3 match terms.

  $ why3 prove pattern_goal.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_rebuild_case" 2>&1 | sed -n -E '/^goal rebuild_case|match xs with|Cons x tl|Nil -> x = x|Cons y ys -> y = y \/\\ ys = ys/p'
  goal rebuild_case :
    match xs with
    | Cons x tl ->
        | Nil -> x = x
        | Cons y ys -> y = y /\ ys = ys

  $ why3 prove pattern_goal.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_rebuild_case" 2>&1 | sed -n '/Undeclared globals/p' | wc -l
  0
