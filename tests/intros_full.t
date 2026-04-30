The full intros transform should introduce quantifiers and implications with
trigger wrappers ignored by traversal.

  $ why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_intros_full" 2>&1 | sed -n -E '/^goal (two|go1|typed)/p'
  goal two : q
  goal go1 : b
  goal typed : sum y1 x2 z1
