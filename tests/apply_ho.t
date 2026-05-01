apply_ho tactic: higher-order unification via HOAS binders

  $ why3 prove apply_ho.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_ho nice_trans" 2>&1 | sed -n -E '/^goal g|^axiom hyp/p'
  axiom hyp : nice 3
  goal g1 : infix_lseq 3 7
  goal g2 : nice 10 -> nice 50 -> nice 10 /\ nice 50
  goal g3 : reaches 1 2 -> reaches 2 3 -> reaches 3 4 -> reaches 1 4

Transitivity with an unknown middle point

  $ why3 prove apply_ho.mlw --extra-config why3extra.test.conf -D why3 -a "apply reaches_trans" 2>&1 | sed -n '/Arg_trans_term2/p'
  anomaly: Why3.Generic_arg_trans_utils.Arg_trans_term2(_)

  $ why3 prove apply_ho.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_ho reaches_trans" 2>&1 | sed -n -E '/^goal g3|^axiom hyp/p'
  axiom hyp : reaches 1 2
  axiom hyp1 : reaches 2 3
  axiom hyp2 : reaches 3 4
  goal g3 : reaches 2 4

Let-opened conclusion with hypothesis discharge

  $ why3 prove apply_ho_let.mlw --extra-config why3extra.test.conf -D why3 -a "apply let_imp" 2>&1 | sed -n '/Arg_trans_term2/p'
  anomaly: Why3.Generic_arg_trans_utils.Arg_trans_term2(_)

  $ why3 prove apply_ho_let.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_ho let_imp" 2>&1 | sed -n -E '/^goal g|^axiom hyp/p'
  axiom hyp : q 17
  goal g : r 17

Let-opened aliases reused in premises

  $ why3 prove apply_ho_let_alias.mlw --extra-config why3extra.test.conf -D why3 -a "apply let_alias_imp" 2>&1 | sed -n '/Arg_trans_term2/p'
  anomaly: Why3.Generic_arg_trans_utils.Arg_trans_term2(_)

  $ why3 prove apply_ho_let_alias.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_ho let_alias_imp" 2>&1 | sed -n -E '/^goal g|^axiom hyp/p'
  axiom hyp : q 17
  goal g : r 17

Atomic goal with let-opened aliases

  $ why3 prove apply_ho_atomic.mlw --extra-config why3extra.test.conf -D why3 -a "apply let_alias_tri" 2>&1 | sed -n '/Arg_trans_missing/p'
  anomaly: Why3.Generic_arg_trans_utils.Arg_trans_missing(_)

  $ why3 prove apply_ho_atomic.mlw --extra-config why3extra.test.conf -D why3 -a "elpi_apply_ho let_alias_tri" 2>&1 | sed -n -E '/^elpi: success|^goal /p'
  elpi: success
