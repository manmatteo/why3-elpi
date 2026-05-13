let run_c =
  Why3_elpi.declare_external_symbol ~name:"w3_run"
    ~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let derive_eq_c =
  Why3_elpi.declare_external_symbol ~name:"w3_derive_eq"
    ~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let derive_ord_c =
  Why3_elpi.declare_external_symbol ~name:"w3_derive_ord"
    ~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let apply_lite_by_c =
  Why3_elpi.declare_external_symbol ~name:"w3_apply_lite_by"
    ~ty:"prsymbol -> list tdecl -> focused-goal -> list focused-task -> prop"

let apply_ho_c =
  Why3_elpi.declare_external_symbol ~name:"w3_apply_ho"
    ~ty:
      "prsymbol -> list term -> list tdecl -> focused-goal -> list \
       focused-task -> prop"

let exists_term_c =
  Why3_elpi.declare_external_symbol ~name:"w3_exists_term"
    ~ty:"term -> list tdecl -> focused-goal -> list focused-task -> prop"

let case_c =
  Why3_elpi.declare_external_symbol ~name:"w3_case"
    ~ty:"term -> list tdecl -> focused-goal -> list focused-task -> prop"

let assert_c =
  Why3_elpi.declare_external_symbol ~name:"w3_assert"
    ~ty:"term -> list tdecl -> focused-goal -> list focused-task -> prop"

let destruct_c =
  Why3_elpi.declare_external_symbol ~name:"w3_destruct"
    ~ty:"prsymbol -> list tdecl -> focused-goal -> list focused-task -> prop"

(* Registration tables *)

let entrypoint_transform_specs :
    (string * string * Elpi.API.RawData.constant * Why3.Pp.formatted) list =
  [ ( "elpi_nop"
    , "transform.elpi"
    , run_c
    , "Run@ the@ identity@ ELPI@ transformation." )
  ; ( "elpi_intro_implies"
    , "examples/intro_implies.elpi"
    , run_c
    , "Run@ the@ ELPI@ intro-implies@ example." )
  ; ( "elpi_intros_full"
    , "examples/intros_full.elpi"
    , run_c
    , "Run@ the@ ELPI@ intros-full@ example." )
  ; ( "elpi_intros_full_local"
    , "examples/intros_full_local.elpi"
    , run_c
    , "Run@ the@ ELPI@ intros-full-local@ example." )
  ; ( "elpi_split_goal_and"
    , "examples/split_goal_and.elpi"
    , run_c
    , "Run@ the@ ELPI@ split-goal-and@ example." )
  ; ( "elpi_drop_non_goal_props"
    , "examples/drop_non_goal_props.elpi"
    , run_c
    , "Run@ the@ ELPI@ drop-non-goal-props@ example." )
  ; ( "elpi_apply_lite"
    , "examples/apply_lite.elpi"
    , run_c
    , "Run@ the@ ELPI@ apply-lite@ example." )
  ; ("elpi_tc", "examples/tc.elpi", run_c, "Run@ the@ ELPI@ tc@ example.")
  ; ( "elpi_derive"
    , "examples/derive.elpi"
    , run_c
    , "Run@ the@ ELPI@ derive@ example." )
  ; ( "elpi_derive_eq_auto"
    , "examples/derive_eq.elpi"
    , run_c
    , "Run@ the@ ELPI@ derive-eq-auto@ example." )
  ; ( "elpi_open_forall_ctx"
    , "examples/open_forall_ctx.elpi"
    , run_c
    , "Run@ the@ ELPI@ open-forall-ctx@ example." )
  ; ( "elpi_rebuild_case"
    , "examples/rebuild_case.elpi"
    , run_c
    , "Run@ the@ ELPI@ rebuild-case@ example." )
  ; ( "elpi_rebuild_case_as"
    , "examples/rebuild_case_as.elpi"
    , run_c
    , "Run@ the@ ELPI@ rebuild-case-as@ example." )
  ; ( "elpi_check_open_term_attrs"
    , "tests/check_open_term_attrs.elpi"
    , run_c
    , "Run@ the@ ELPI@ check-open-term-attrs@ test@ helper." )
  ; ( "elpi_derive_eq"
    , "examples/derive.elpi"
    , derive_eq_c
    , "Run@ the@ ELPI@ derive-eq@ example." )
  ; ( "elpi_derive_ord"
    , "examples/derive.elpi"
    , derive_ord_c
    , "Run@ the@ ELPI@ derive-ord@ example." )
  ]

(* All registrations at module initialisation time *)

let () =
  List.iter
    (fun (name, file, entrypoint, desc) ->
      Why3_elpi.register_transform ~name ~file ~entrypoint ~desc)
    entrypoint_transform_specs;

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_apply_ho"
    ~file:"examples/apply_ho.elpi"
    ~arg_type:Why3.Args_wrapper.(Tprsymbol (Topt ("with", Ttermlist Ttrans_l)))
    ~entrypoint:apply_ho_c
    ~desc:
      "Run@ the@ ELPI@ apply-ho@ tactic@ with@ a@ typed@ proposition@ symbol@ \
       and@ optional@ witness@ terms@ (with@ t1,@ ...,@ tn).";

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_apply_lite_by"
    ~file:"examples/apply_lite.elpi"
    ~arg_type:Why3.Args_wrapper.(Tprsymbol Ttrans_l)
    ~entrypoint:apply_lite_by_c
    ~desc:
      "Run@ the@ ELPI@ apply-lite@ example@ with@ a@ typed@ proposition@ \
       symbol@ argument.";

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_exists_term"
    ~file:"examples/exists_term.elpi"
    ~arg_type:Why3.Args_wrapper.(Tterm Ttrans_l)
    ~entrypoint:exists_term_c
    ~desc:
      "Run@ the@ ELPI@ exists-term@ example@ with@ a@ typed@ term@ argument.";

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_exists"
    ~file:"examples/exists.elpi"
    ~arg_type:Why3.Args_wrapper.(Tterm Ttrans_l)
    ~entrypoint:exists_term_c
    ~desc:
      "Run@ the@ ELPI@ exists@ example@ with@ a@ typed@ witness@ term@ \
       argument.";

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_case"
    ~file:"examples/case.elpi"
    ~arg_type:Why3.Args_wrapper.(Tformula Ttrans_l)
    ~entrypoint:case_c
    ~desc:"Run@ the@ ELPI@ case@ example@ with@ a@ typed@ formula@ argument.";

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_assert"
    ~file:"examples/assert.elpi"
    ~arg_type:Why3.Args_wrapper.(Tformula Ttrans_l)
    ~entrypoint:assert_c
    ~desc:"Run@ the@ ELPI@ assert@ example@ with@ a@ typed@ formula@ argument.";

  Why3_elpi.build_and_register_transform_with_args ~name:"elpi_destruct"
    ~file:"examples/destruct.elpi"
    ~arg_type:Why3.Args_wrapper.(Tprsymbol Ttrans_l)
    ~entrypoint:destruct_c
    ~desc:
      "Run@ the@ ELPI@ destruct@ prototype@ on@ a@ selected@ local@ \
       hypothesis@ symbol."
