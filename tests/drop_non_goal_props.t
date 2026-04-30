The semantic declaration kinds should be sufficient to filter out
non-goal proposition declarations while keeping the rest of the task.

User axioms (tata, oe) must be absent from every task after the transform:
  $ why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_drop_non_goal_props" 2>&1 | grep "^axiom tata\|^axiom oe" | wc -l | tr -d ' '
  0

Non-proposition declarations and goals must still be present:
  $ why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_drop_non_goal_props" 2>&1 | sed -n -E '/^goal (two|go1|plus)|^predicate p$|^predicate q$|^function zz/p' | sort -u
  function zz int int int : int
  goal go1 : (a -> b) -> a -> b
  goal plus :
  goal two : p -> q
  predicate p
  predicate q
