The "elpi_nop" transformation should produce output identical to plain Why3
(modulo the "elpi: success" status line which is filtered below).
The only known acceptable discrepancy is a quantifier grouping difference in
simple.mlw: the embed/readback round-trip groups the last two quantifiers as
`forall u:c, v:c, w:c.` while Why3 prints `forall u:c, v:c. forall w:c.`
That difference is documented explicitly in the simple test case below.

mini
  $ diff <(why3 prove mini.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove mini.mlw --extra-config why3extra.test.conf -D why3 2>&1)

simple: one known quantifier-grouping difference on goal one
  $ diff <(why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove simple.mlw --extra-config why3extra.test.conf -D why3 2>&1)
  217c217
  < goal one : forall u:c, v:c, w:c. ff u v w -> k 0 1 w = 0
  ---
  > goal one : forall u:c, v:c. forall w:c. ff u v w -> k 0 1 w = 0
  [1]

tc
  $ diff <(why3 prove tc.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove tc.mlw --extra-config why3extra.test.conf -D why3 2>&1)

linked_list_rev
  $ diff <(why3 prove linked_list_rev.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove linked_list_rev.mlw --extra-config why3extra.test.conf -D why3 2>&1)

mccarthy
  $ diff <(why3 prove mccarthy.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove mccarthy.mlw --extra-config why3extra.test.conf -D why3 2>&1)

fibonacci
  $ diff <(why3 prove fibonacci.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove fibonacci.mlw --extra-config why3extra.test.conf -D why3 2>&1)

triggers
  $ diff <(why3 prove triggers.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove triggers.mlw --extra-config why3extra.test.conf -D why3 2>&1)

verifythis_2024_challenge1
  $ diff <(why3 prove verifythis_2024_challenge1.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_nop" 2>&1 | grep -v '^elpi: success$') <(why3 prove verifythis_2024_challenge1.mlw --extra-config why3extra.test.conf -D why3 2>&1)
