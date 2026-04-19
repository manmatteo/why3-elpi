basic typeclass resolution

  $ WHY3_ELPI_PROGRAM=../examples/tc.elpi why3 prove tc.mlw --extra-config why3extra.test.conf -D why3 -a "lp tc" 2>&1 | sed -n -E '/^goal test_tc|^goal test_tc2|^  let [ijkl] =/p'
  goal test_tc :
    let i = pair_eq int_eq bool_eq in
  goal test_tc2 :
    let i = int_eq in
    let j = int_monoid in
    let k = int_group in
    let l = int_monoid in

  $ WHY3_ELPI_PROGRAM=../examples/tc.elpi why3 prove tc.mlw --extra-config why3extra.test.conf -D why3 -a "lp tc" 2>&1 | sed -n '/^yay$/p' | wc -l
  5
