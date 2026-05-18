(* Registration tables *)

let entrypoint_transform_specs : (string * string * Why3.Pp.formatted) list =
  [ ("elpi_nop", "transform.elpi", "Run@ the@ identity@ ELPI@ transformation.")
  ; ( "elpi_intro_implies"
    , "examples/intro_implies.elpi"
    , "Run@ the@ ELPI@ intro-implies@ example." )
  ; ( "elpi_intros_full"
    , "examples/intros_full.elpi"
    , "Run@ the@ ELPI@ intros-full@ example." )
  ; ( "elpi_intros_full_local"
    , "examples/intros_full_local.elpi"
    , "Run@ the@ ELPI@ intros-full-local@ example." )
  ; ( "elpi_split_goal_and"
    , "examples/split_goal_and.elpi"
    , "Run@ the@ ELPI@ split-goal-and@ example." )
  ; ( "elpi_drop_non_goal_props"
    , "examples/drop_non_goal_props.elpi"
    , "Run@ the@ ELPI@ drop-non-goal-props@ example." )
  ; ("elpi_tc", "examples/tc.elpi", "Run@ the@ ELPI@ tc@ example.")
  ; ("elpi_derive", "examples/derive.elpi", "Run@ the@ ELPI@ derive@ example.")
  ; ( "elpi_derive_eq_auto"
    , "examples/derive_eq.elpi"
    , "Run@ the@ ELPI@ derive-eq-auto@ example." )
  ; ( "elpi_open_forall_ctx"
    , "examples/open_forall_ctx.elpi"
    , "Run@ the@ ELPI@ open-forall-ctx@ example." )
  ; ( "elpi_rebuild_case"
    , "examples/rebuild_case.elpi"
    , "Run@ the@ ELPI@ rebuild-case@ example." )
  ; ( "elpi_rebuild_case_as"
    , "examples/rebuild_case_as.elpi"
    , "Run@ the@ ELPI@ rebuild-case-as@ example." )
  ; ( "elpi_check_open_term_attrs"
    , "tests/check_open_term_attrs.elpi"
    , "Run@ the@ ELPI@ check-open-term-attrs@ test@ helper." )
  ; ( "elpi_derive_eq"
    , "examples/derive.elpi"
    , "Run@ the@ ELPI@ derive-eq@ example." )
  ; ( "elpi_derive_ord"
    , "examples/derive.elpi"
    , "Run@ the@ ELPI@ derive-ord@ example." )
  ]

(* All registrations at module initialisation time *)

let () =
  List.iter
    (fun (name, file, desc) ->
      Why3_elpi.register_transform ~name ~file
        ~arg_type:Why3.Args_wrapper.Ttrans_l ~desc)
    entrypoint_transform_specs;

  Why3_elpi.register_transform ~name:"elpi_apply" ~file:"examples/apply.elpi"
    ~arg_type:Why3.Args_wrapper.(Tprsymbol (Topt ("with", Ttermlist Ttrans_l)))
    ~desc:
      "Run@ the@ ELPI@ apply-ho@ tactic@ with@ a@ typed@ proposition@ symbol@ \
       and@ optional@ witness@ terms@ (with@ t1,@ ...,@ tn).";

  Why3_elpi.register_transform ~name:"elpi_exists_term"
    ~file:"examples/exists_term.elpi"
    ~arg_type:Why3.Args_wrapper.(Tterm Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ exists-term@ example@ with@ a@ typed@ term@ argument.";

  Why3_elpi.register_transform ~name:"elpi_exists"
    ~file:"examples/exists_term.elpi"
    ~arg_type:Why3.Args_wrapper.(Tterm Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ exists@ example@ with@ a@ typed@ witness@ term@ \
       argument.";

  Why3_elpi.register_transform ~name:"elpi_case" ~file:"examples/case.elpi"
    ~arg_type:Why3.Args_wrapper.(Tformula Ttrans_l)
    ~desc:"Run@ the@ ELPI@ case@ example@ with@ a@ typed@ formula@ argument.";

  Why3_elpi.register_transform ~name:"elpi_assert" ~file:"examples/assert.elpi"
    ~arg_type:Why3.Args_wrapper.(Tformula Ttrans_l)
    ~desc:"Run@ the@ ELPI@ assert@ example@ with@ a@ typed@ formula@ argument.";

  Why3_elpi.register_transform ~name:"elpi_destruct"
    ~file:"examples/destruct.elpi"
    ~arg_type:Why3.Args_wrapper.(Tprsymbol Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ destruct@ prototype@ on@ a@ selected@ local@ \
       hypothesis@ symbol."
