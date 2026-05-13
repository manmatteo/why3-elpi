open Why3
module T = Why3_elpi_trans

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
    (string * string * Elpi.API.RawData.constant * Pp.formatted) list =
  [ ( "elpi_nop"
    , "transform.elpi"
    , T.run_c
    , "Run@ the@ identity@ ELPI@ transformation." )
  ; ( "elpi_intro_implies"
    , "examples/intro_implies.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ intro-implies@ example." )
  ; ( "elpi_intros_full"
    , "examples/intros_full.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ intros-full@ example." )
  ; ( "elpi_intros_full_local"
    , "examples/intros_full_local.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ intros-full-local@ example." )
  ; ( "elpi_split_goal_and"
    , "examples/split_goal_and.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ split-goal-and@ example." )
  ; ( "elpi_drop_non_goal_props"
    , "examples/drop_non_goal_props.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ drop-non-goal-props@ example." )
  ; ( "elpi_apply_lite"
    , "examples/apply_lite.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ apply-lite@ example." )
  ; ("elpi_tc", "examples/tc.elpi", T.run_c, "Run@ the@ ELPI@ tc@ example.")
  ; ( "elpi_derive"
    , "examples/derive.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ derive@ example." )
  ; ( "elpi_derive_eq_auto"
    , "examples/derive_eq.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ derive-eq-auto@ example." )
  ; ( "elpi_open_forall_ctx"
    , "examples/open_forall_ctx.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ open-forall-ctx@ example." )
  ; ( "elpi_rebuild_case"
    , "examples/rebuild_case.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ rebuild-case@ example." )
  ; ( "elpi_rebuild_case_as"
    , "examples/rebuild_case_as.elpi"
    , T.run_c
    , "Run@ the@ ELPI@ rebuild-case-as@ example." )
  ; ( "elpi_check_open_term_attrs"
    , "tests/check_open_term_attrs.elpi"
    , T.run_c
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
      T.register_transform ~name ~file ~entrypoint ~desc)
    entrypoint_transform_specs;

  let make_apply_ho target withed_terms_opt =
    let withed_terms = Option.value ~default:[] withed_terms_opt in
    let embeds =
      [ (fun ~depth state ->
          Why3_elpi.prsymbol.embed ~depth [] Elpi.API.RawData.no_constraints
            state target)
      ; (fun ~depth state ->
          (Elpi_api_compat.BuiltInContextualData.list Why3_elpi.term).embed
            ~depth [] Elpi.API.RawData.no_constraints state withed_terms)
      ]
    in
    T.build_transform_with_embedded_args ~file:"examples/apply_ho.elpi"
      ~entrypoint:apply_ho_c embeds
  in
  T.register_transform_with_args ~name:"elpi_apply_ho"
    ~arg_type:Args_wrapper.(Tprsymbol (Topt ("with", Ttermlist Ttrans_l)))
    ~desc:
      "Run@ the@ ELPI@ apply-ho@ tactic@ with@ a@ typed@ proposition@ symbol@ \
       and@ optional@ witness@ terms@ (with@ t1,@ ...,@ tn)."
    make_apply_ho;

  let make_apply_lite_by target =
    let embeds =
      [ (fun ~depth state ->
          Why3_elpi.prsymbol.embed ~depth [] Elpi.API.RawData.no_constraints
            state target)
      ]
    in
    T.build_transform_with_embedded_args ~file:"examples/apply_lite.elpi"
      ~entrypoint:apply_lite_by_c embeds
  in
  T.register_transform_with_args ~name:"elpi_apply_lite_by"
    ~arg_type:Args_wrapper.(Tprsymbol Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ apply-lite@ example@ with@ a@ typed@ proposition@ \
       symbol@ argument."
    make_apply_lite_by;

  let make_exists_term witness =
    let embeds =
      [ (fun ~depth state ->
          Why3_elpi.term.embed ~depth [] Elpi.API.RawData.no_constraints state
            witness)
      ]
    in
    T.build_transform_with_embedded_args ~file:"examples/exists_term.elpi"
      ~entrypoint:exists_term_c embeds
  in
  T.register_transform_with_args ~name:"elpi_exists_term"
    ~arg_type:Args_wrapper.(Tterm Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ exists-term@ example@ with@ a@ typed@ term@ argument."
    make_exists_term;

  T.register_transform_with_args ~name:"elpi_exists"
    ~arg_type:Args_wrapper.(Tterm Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ exists@ example@ with@ a@ typed@ witness@ term@ \
       argument."
    make_exists_term;

  let make_case cond =
    let embeds =
      [ (fun ~depth state ->
          Why3_elpi.term.embed ~depth [] Elpi.API.RawData.no_constraints state
            cond)
      ]
    in
    T.build_transform_with_embedded_args ~file:"examples/case.elpi"
      ~entrypoint:case_c embeds
  in
  T.register_transform_with_args ~name:"elpi_case"
    ~arg_type:Args_wrapper.(Tformula Ttrans_l)
    ~desc:"Run@ the@ ELPI@ case@ example@ with@ a@ typed@ formula@ argument."
    make_case;

  let make_assert cond =
    let embeds =
      [ (fun ~depth state ->
          Why3_elpi.term.embed ~depth [] Elpi.API.RawData.no_constraints state
            cond)
      ]
    in
    T.build_transform_with_embedded_args ~file:"examples/assert.elpi"
      ~entrypoint:assert_c embeds
  in
  T.register_transform_with_args ~name:"elpi_assert"
    ~arg_type:Args_wrapper.(Tformula Ttrans_l)
    ~desc:"Run@ the@ ELPI@ assert@ example@ with@ a@ typed@ formula@ argument."
    make_assert;

  let make_destruct target =
    let embeds =
      [ (fun ~depth state ->
          Why3_elpi.prsymbol.embed ~depth [] Elpi.API.RawData.no_constraints
            state target)
      ]
    in
    T.build_transform_with_embedded_args ~file:"examples/destruct.elpi"
      ~entrypoint:destruct_c embeds
  in
  T.register_transform_with_args ~name:"elpi_destruct"
    ~arg_type:Args_wrapper.(Tprsymbol Ttrans_l)
    ~desc:
      "Run@ the@ ELPI@ destruct@ prototype@ on@ a@ selected@ local@ \
       hypothesis@ symbol."
    make_destruct
