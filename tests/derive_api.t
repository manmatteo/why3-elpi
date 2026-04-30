structural derivation from helper signatures

  $ why3 prove derive.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_derive_eq" 2>&1 | sed -n -E '/^goal (list_relqtvc|tree_relqtvc|derive_tree_eq|derive_maybe_tree_eq)/p;/^  let e =/p'
  goal list_relqtvc [@expl:VC for list_rel] :
  goal tree_relqtvc [@expl:VC for tree_rel] :
  goal derive_tree_eq :
    let e = tree_eq (list_eq (pair_eq int_eq bool_eq)) in
  goal derive_maybe_tree_eq :
    let e = maybe_eq (tree_eq (list_eq (pair_eq int_eq bool_eq))) in

  $ why3 prove derive.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_derive_ord" 2>&1 | sed -n -E '/^goal (derive_list_pair_ord|derive_maybe_list_ord)/p;/^  let o =/p'
  goal derive_list_pair_ord :
    let o = list_ord (pair_ord int_ord bool_ord) in
  goal derive_maybe_list_ord :
    let o = maybe_ord (list_ord (pair_ord int_ord bool_ord)) in

  $ why3 prove derive.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_derive" 2>&1 | sed -n -E '/^goal (derive_maybe_tree_eq|derive_maybe_list_ord)/p;/^  let [eo] = maybe_(eq|ord)/p'
  goal derive_maybe_tree_eq :
    let e = maybe_eq (tree_eq (list_eq (pair_eq int_eq bool_eq))) in
  goal derive_maybe_list_ord :
    let o = maybe_ord (list_ord (pair_ord int_ord bool_ord)) in
