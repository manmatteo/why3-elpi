The semantic declaration kinds should be sufficient to filter out
non-goal proposition declarations while keeping the rest of the task.

  $ WHY3_ELPI_PROGRAM=../examples/drop_non_goal_props.elpi why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "lp drop-non-goal-props" 2>&1 | sed -n -E '/^goal (two|go1|plus)|^axiom tata \[@useraxiom\]/p' | sort -u
  axiom tata [@useraxiom] : forall us:b. forall us1:a 'a. true
  goal go1 : (a -> b) -> a -> b
  goal plus :
  goal two : p -> q
