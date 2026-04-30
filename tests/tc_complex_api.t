complex typeclass resolution

  $ why3 prove tc_complex.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_tc" 2>&1 | sed -n -E '/^goal (list_relqtvc|tree_relqtvc)/p'
  goal list_relqtvc [@expl:VC for list_rel] :
  goal tree_relqtvc [@expl:VC for tree_rel] :

  $ why3 prove tc_complex.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_tc" 2>&1 | sed -n -E '/^goal test_tc_(nested_eq|list_eq|tree_eq|nested_monoid|nested_group|lex_nested)|^  let [imgo] =|^    pair_monoid|^    \(pair_monoid/p'
  goal test_tc_nested_eq :
    let i = pair_eq (pair_eq int_eq bool_eq) (pair_eq int_eq bool_eq) in
  goal test_tc_list_eq :
    let i = list_eq (pair_eq int_eq bool_eq) in
  goal test_tc_tree_eq :
    let i = tree_eq (list_eq (pair_eq int_eq bool_eq)) in
  goal test_tc_nested_monoid :
    let m =
      pair_monoid (pair_monoid int_monoid bool_monoid)
      (pair_monoid int_monoid bool_monoid)
  goal test_tc_nested_group :
    let g = pair_group (pair_group int_group int_group) int_group in
  goal test_tc_lex_nested :
    let o = pair_ord (pair_ord int_ord bool_ord) (pair_ord int_ord bool_ord) in

  $ why3 prove tc_complex.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_tc" 2>&1 | sed -n '/^yay$/p' | wc -l
  6
