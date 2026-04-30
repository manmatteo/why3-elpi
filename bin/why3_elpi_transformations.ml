open Why3
open Why3_elpi

module T = Why3_elpi_trans

let derive_eq_c =
  declare_external_symbol
    ~name:"w3_derive_eq"
    ~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let derive_ord_c =
  declare_external_symbol
    ~name:"w3_derive_ord"
    ~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let apply_lite_by_c =
  declare_external_symbol
    ~name:"w3_apply_lite_by"
    ~ty:"prsymbol -> list tdecl -> focused-goal -> list focused-task -> prop"

let exists_term_c =
  declare_external_symbol
    ~name:"w3_exists_term"
    ~ty:"term -> list tdecl -> focused-goal -> list focused-task -> prop"

(* Registration tables *)

let file_transform_specs : (string * string * Pp.formatted) list =
  [ ("elpi_nop",               "transform.elpi",                      "Run@ the@ identity@ ELPI@ transformation.");
    ("elpi_intro_implies",     "examples/intro_implies.elpi",         "Run@ the@ ELPI@ intro-implies@ example.");
    ("elpi_intros_full",        "examples/intros_full.elpi",           "Run@ the@ ELPI@ intros-full@ example.");
    ("elpi_intros_full_local",  "examples/intros_full_local.elpi",     "Run@ the@ ELPI@ intros-full-local@ example.");
    ("elpi_split_goal_and",     "examples/split_goal_and.elpi",        "Run@ the@ ELPI@ split-goal-and@ example.");
    ("elpi_drop_non_goal_props","examples/drop_non_goal_props.elpi",   "Run@ the@ ELPI@ drop-non-goal-props@ example.");
    ("elpi_apply_lite",         "examples/apply_lite.elpi",            "Run@ the@ ELPI@ apply-lite@ example.");
    ("elpi_tc",                 "examples/tc.elpi",                    "Run@ the@ ELPI@ tc@ example.");
    ("elpi_derive",             "examples/derive.elpi",                "Run@ the@ ELPI@ derive@ example.");
    ("elpi_derive_eq_auto",     "examples/derive_eq.elpi",             "Run@ the@ ELPI@ derive-eq-auto@ example.");
    ("elpi_local_logic",        "examples/local_logic.elpi",           "Run@ the@ ELPI@ local-logic@ example.");
    ("elpi_local_logic_named",  "examples/local_logic_named.elpi",     "Run@ the@ ELPI@ local-logic-named@ example.");
    ("elpi_open_forall_ctx",    "examples/open_forall_ctx.elpi",       "Run@ the@ ELPI@ open-forall-ctx@ example.");
    ("elpi_rebuild_case",       "examples/rebuild_case.elpi",          "Run@ the@ ELPI@ rebuild-case@ example.");
    ("elpi_rebuild_case_as",    "examples/rebuild_case_as.elpi",       "Run@ the@ ELPI@ rebuild-case-as@ example.");
    ("elpi_check_open_term_attrs","tests/check_open_term_attrs.elpi",  "Run@ the@ ELPI@ check-open-term-attrs@ test@ helper.");
  ]

let entrypoint_transform_specs : (string * string * Elpi.API.RawData.constant * Pp.formatted) list =
  [ ("elpi_derive_eq",  "examples/derive.elpi", derive_eq_c,  "Run@ the@ ELPI@ derive-eq@ example.");
    ("elpi_derive_ord", "examples/derive.elpi", derive_ord_c, "Run@ the@ ELPI@ derive-ord@ example.");
  ]

(* All registrations at module initialisation time *)

let () =
  List.iter
    (fun (name, file, desc) -> T.register_transform ~name ~file ~entrypoint:T.run_c ~desc)
    file_transform_specs;

  List.iter
    (fun (name, file, entrypoint, desc) -> T.register_transform ~name ~file ~entrypoint ~desc)
    entrypoint_transform_specs;

  T.register_transform_with_arg
    ~name:"elpi_apply_lite_by"
    ~file:"examples/apply_lite.elpi"
    ~entrypoint:apply_lite_by_c
    ~embed:prsymbol.embed
    ~arg_type:Args_wrapper.(Tprsymbol Ttrans_l)
    ~desc:"Run@ the@ ELPI@ apply-lite@ example@ with@ a@ typed@ proposition@ symbol@ argument.";

  T.register_transform_with_arg
    ~name:"elpi_exists_term"
    ~file:"examples/exists_term.elpi"
    ~entrypoint:exists_term_c
    ~embed:term.embed
    ~arg_type:Args_wrapper.(Tterm Ttrans_l)
    ~desc:"Run@ the@ ELPI@ exists-term@ example@ with@ a@ typed@ term@ argument."