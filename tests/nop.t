The "lp nop" transformation should remain textually identical to plain Why3,
except for accepted quantifier grouping changes
(`forall x, y. ...` vs `forall x. forall y. ...`, similarly for `exists`).
The normalize_quantifiers script normalizes only that grouping form.

mini
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove mini.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove mini.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

simple
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

tc
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove tc.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove tc.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

linked_list_rev
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove linked_list_rev.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove linked_list_rev.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

mccarthy
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove mccarthy.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove mccarthy.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

fibonacci
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove fibonacci.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove fibonacci.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

triggers
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove triggers.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove triggers.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)

verifythis_2024_challenge1
  $ diff -w <(WHY3_ELPI_PROGRAM=../transform.elpi why3 prove verifythis_2024_challenge1.mlw --extra-config why3extra.test.conf -D why3 -a "lp nop" 2>&1 | sed '/^elpi: success$/d' | ./normalize_quantifiers) <(why3 prove verifythis_2024_challenge1.mlw --extra-config why3extra.test.conf -D why3 2>&1 | ./normalize_quantifiers)
