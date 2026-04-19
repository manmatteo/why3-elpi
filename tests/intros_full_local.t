The focused-goal API should be sufficient to implement a declarative
introduction transform with explicit local-symbol allocation in Elpi code.

  $ WHY3_ELPI_PROGRAM=../examples/intros_full_local.elpi why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "lp intros-full-local" 2>&1 | sed 's/[[:space:]]*$//' | sed -n -E '/^opened-(forall|premise|goal)|^goal (two|go1|plus)/p'
  opened-goal pairs
  opened-goal t
  opened-forall `u`
  opened-forall `v`
  opened-forall `w`
  opened-premise H ff u1 v1 w1
  opened-goal one
  opened-premise H p
  opened-goal two
  goal two : q
  opened-forall `x`
  opened-forall `y`
  opened-goal test2
  opened-goal fib
  opened-goal test
  opened-goal ciao
  opened-premise H a -> b
  opened-premise H a
  opened-goal go1
  goal go1 : b
  opened-premise H forall y2:n. sum z y2 y2
  opened-premise H forall x2:n, y2:n. sum (s x2) y2 (s y2)
  opened-goal plus
  goal plus : exists x2:n. sum (s (s z)) (s z) x2
  opened-goal fib2
  opened-forall `x2`
  opened-forall `y2`
  opened-forall `z1`
  opened-premise H sum x3 y3 z2
  opened-goal typed
