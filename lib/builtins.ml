open Term
open Ty
open Decl
open Theory

let in_ctx_for_ty = Ty.in_ctx_for_why_simple_ty
let in_ctx_for_term = Term.in_ctx_for_why_simple_term
let pp_ctx_for_term = Term.pp_ctx_for_term

let option_map_decl_data d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Ddata ds -> Some ds
      | _ -> None

let option_map_decl_ind d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Dind ds -> Some ds
      | _ -> None

let option_map_decl_logic d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Dlogic ds -> Some ds
      | _ -> None

let option_map_decl_const d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Dparam ls -> Some ls
      | _ -> None

let option_map_decl_typ d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Dtype ts -> Some ts
      | _ -> None

let option_map_decl_prop_pr d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Dprop (_, pr, _) -> Some pr
      | _ -> None

let option_map_decl_prop_tm d =
      match d.Why3.Decl.d_node with
      | Why3.Decl.Dprop (_, _, tm) -> Some tm
      | _ -> None

let option_map_tdecl_decl td =
      match td.Why3.Theory.td_node with
      | Why3.Theory.Decl d -> Some d
      | _ -> None

let option_map_tdecl_use td =
      match td.Why3.Theory.td_node with
      | Why3.Theory.Use th -> Some th
      | _ -> None

let option_map_tdecl_meta td =
      match td.Why3.Theory.td_node with
      | Why3.Theory.Meta (m, _) -> Some m
      | _ -> None

let option_map_tdecl_meta_args td =
      match td.Why3.Theory.td_node with
      | Why3.Theory.Meta (_, args) -> Some args
      | _ -> None

let option_map_tdecl_clone td =
      match td.Why3.Theory.td_node with
      | Why3.Theory.Clone (th, _) -> Some th
      | _ -> None

let why3_builtin_declarations =
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInData in
  let open Elpi.API.BuiltInPredicate in
  let open Elpi.API.BuiltInPredicate.Notation in
  [MLCode
      ( Pred ( "why3.var-type",
            CIn  (vsymbol, "V",
            COut (ty, "T",
            Read (in_ctx_for_ty, "Get the type of a variable"))),
            fun var _ ~depth:_ _ctx _ _ -> !: (var.vs_ty)),
        DocAbove );
  MLCode
  ( Pred ( "why3.ls-type",
            CIn  (lsymbol, "L",
            COut (ty, "T",
            Read (in_ctx_for_ty, "Get the value type of a logic symbol. Fails if the symbol has no value type (i.e. is a proposition)"))),
            fun ls _ ~depth:_ _ctx _ _ -> ?: (ls.ls_value)),
        DocAbove );
  MLCode
  ( Pred ( "why3.var-name",
            CIn  (vsymbol, "V",
            COut (Elpi_api_compat.BuiltInContextualData.string, "N",
            Read (in_ctx_for_term, "Get the identifier string of a variable symbol."))),
            fun v _ ~depth:_ _ctx _ _ -> !: ((v.vs_name).id_string)),
        DocAbove );
  MLCode
  ( Pred ( "why3.ls-name",
            CIn  (lsymbol, "L",
            COut (Elpi_api_compat.BuiltInContextualData.string, "N",
            Read (in_ctx_for_term, "Get the identifier string of a logic symbol."))),
            fun ls _ ~depth:_ _ctx _ _ -> !: ((ls.ls_name).id_string)),
        DocAbove );
  MLCode
  ( Pred ( "why3.tysymbol-name",
            CIn  (tysymbol, "Ts",
            COut (Elpi_api_compat.BuiltInContextualData.string, "N",
            Read (in_ctx_for_ty, "Get the identifier string of a type symbol."))),
            fun ts _ ~depth:_ _ctx _ _ -> !: ((ts.ts_name).id_string)),
        DocAbove );
  MLCode
  ( Pred ( "why3.prsymbol-name",
            CIn  (prsymbol, "Pr",
            COut (Elpi_api_compat.BuiltInContextualData.string, "N",
            Read (in_ctx_for_term, "Get the identifier string of a proposition symbol."))),
            fun pr _ ~depth:_ _ctx _ _ -> !: ((pr.pr_name).id_string)),
        DocAbove );
  MLCode
  ( Pred ( "why3.theory-name",
            CIn  (theory, "Th",
            COut (Elpi_api_compat.BuiltInContextualData.string, "N",
            Read (in_ctx_for_term, "Get the identifier string of a theory."))),
            fun th _ ~depth:_ _ctx _ _ -> !: ((th.th_name).id_string)),
        DocAbove );
  MLCode
  ( Pred ( "why3.meta-name",
            CIn  (meta, "M",
            COut (Elpi_api_compat.BuiltInContextualData.string, "N",
            Read (in_ctx_for_term, "Get the name string of a meta declaration."))),
            fun m _ ~depth:_ _ctx _ _ -> !: (m.meta_name)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-kind",
            CIn  (decl, "D",
            COut (Elpi_api_compat.BuiltInContextualData.string, "K",
            Read (in_ctx_for_term, "Classify a declaration: goal|lemma|axiom|typ|data|dind|declls|const."))),
            fun d _ ~depth:_ _ctx _ _ -> !:
                                          (match d.Why3.Decl.d_node with
               | Why3.Decl.Dprop (Why3.Decl.Pgoal, _, _) -> "goal"
               | Why3.Decl.Dprop (Why3.Decl.Plemma, _, _) -> "lemma"
               | Why3.Decl.Dprop (Why3.Decl.Paxiom, _, _) -> "axiom"
               | Why3.Decl.Dtype _ -> "typ"
               | Why3.Decl.Ddata _ -> "data"
               | Why3.Decl.Dind _ -> "dind"
               | Why3.Decl.Dlogic _ -> "declls"
               | Why3.Decl.Dparam _ -> "const")),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-prop-kind",
            CIn  (decl, "D",
            COut (Elpi_api_compat.BuiltInContextualData.string, "K",
            Read (in_ctx_for_term, "Get proposition kind for a proposition declaration: goal|lemma|axiom."))),
            fun d _ ~depth:_ _ctx _ _ -> ?:
                                          (match d.Why3.Decl.d_node with
               | Why3.Decl.Dprop (Why3.Decl.Pgoal, _, _) -> Some "goal"
               | Why3.Decl.Dprop (Why3.Decl.Plemma, _, _) -> Some "lemma"
               | Why3.Decl.Dprop (Why3.Decl.Paxiom, _, _) -> Some "axiom"
               | _ -> None)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-prop-symbol",
            CIn  (decl, "D",
            COut (prsymbol, "Pr",
            Read (in_ctx_for_term, "Project proposition symbol from a proposition declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_prop_pr d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-prop-term",
            CIn  (decl, "D",
            COut (term, "T",
            Read (in_ctx_for_term, "Project proposition term from a proposition declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_prop_tm d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-typ",
            CIn  (decl, "D",
            COut (tysymbol, "Ts",
            Read (in_ctx_for_term, "Project type symbol from a type declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_typ d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-const",
            CIn  (decl, "D",
            COut (lsymbol, "L",
            Read (in_ctx_for_term, "Project logic symbol from a constant declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_const d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-data",
            CIn  (decl, "D",
            COut ((Elpi_api_compat.BuiltInContextualData.list data_decl), "DD",
            Read (in_ctx_for_term, "Project data declaration payload from a data declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_data d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-ind",
            CIn  (decl, "D",
            COut (ind_list, "ID",
            Read (in_ctx_for_term, "Project inductive declaration payload from an inductive declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_ind d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.decl-logic",
            CIn  (decl, "D",
            COut ((Elpi_api_compat.BuiltInContextualData.list logic_decl), "LD",
            Read (in_ctx_for_term, "Project logic declaration payload from a logic declaration."))),
            fun d _ ~depth:_ _ctx _ _ -> ?: (option_map_decl_logic d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-decl",
            CIn  (decl, "D",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a declaration."))),
                  fun d _ ~depth:_ _ctx _ _ -> !: (Format.asprintf "%a" Why3.Pretty.print_decl d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-logic-decl",
            CIn  (logic_decl, "LD",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a logic declaration payload."))),
                  fun ld _ ~depth:_ _ctx _ _ -> !: (Format.asprintf "%a" Why3.Pretty.print_logic_decl ld)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-data-decl",
            CIn  (data_decl, "DD",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a data declaration payload."))),
            fun (ts, _ as dd) _ ~depth:_ _ctx _ _ ->
              let _ = dd in
                                          !: (Format.asprintf "data %a" Why3.Pretty.print_ts ts)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-ind-list",
            CIn  (ind_list, "ID",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print an inductive declaration payload."))),
            fun (sgn, decls) _ ~depth:_ _ctx _ _ ->
                                          let d = Why3.Decl.create_ind_decl sgn decls in
                                          !: (Format.asprintf "%a" Why3.Pretty.print_decl d)),
        DocAbove );
  MLCode
  ( Pred ( "why3.tdecl-kind",
            CIn  (tdecl, "TD",
            COut (Elpi_api_compat.BuiltInContextualData.string, "K",
            Read (in_ctx_for_term, "Classify a task declaration: decl|use|meta|clone."))),
            fun td _ ~depth:_ _ctx _ _ -> !:
                                          (match td.Why3.Theory.td_node with
               | Why3.Theory.Decl _ -> "decl"
               | Why3.Theory.Use _ -> "use"
               | Why3.Theory.Meta _ -> "meta"
               | Why3.Theory.Clone _ -> "clone")),
        DocAbove );
  MLCode
  ( Pred ( "why3.tdecl-decl",
            CIn  (tdecl, "TD",
            COut (decl, "D",
            Read (in_ctx_for_term, "Project declaration payload from a task declaration node of kind decl."))),
            fun td _ ~depth:_ _ctx _ _ -> ?: (option_map_tdecl_decl td)),
        DocAbove );
  MLCode
  ( Pred ( "why3.tdecl-use",
            CIn  (tdecl, "TD",
            COut (theory, "Th",
            Read (in_ctx_for_term, "Project theory payload from a task declaration node of kind use."))),
            fun td _ ~depth:_ _ctx _ _ -> ?: (option_map_tdecl_use td)),
        DocAbove );
  MLCode
  ( Pred ( "why3.tdecl-meta",
            CIn  (tdecl, "TD",
            COut (meta, "M",
            Read (in_ctx_for_term, "Project meta payload from a task declaration node of kind meta."))),
            fun td _ ~depth:_ _ctx _ _ -> ?: (option_map_tdecl_meta td)),
        DocAbove );
  MLCode
  ( Pred ( "why3.tdecl-meta-args",
            CIn  (tdecl, "TD",
            COut ((Elpi_api_compat.BuiltInContextualData.list meta_arg), "Args",
            Read (in_ctx_for_term, "Project meta-argument payload from a task declaration node of kind meta."))),
            fun td _ ~depth:_ _ctx _ _ -> ?: (option_map_tdecl_meta_args td)),
        DocAbove );
  MLCode
  ( Pred ( "why3.tdecl-clone",
            CIn  (tdecl, "TD",
            COut (theory, "Th",
            Read (in_ctx_for_term, "Project cloned theory payload from a task declaration node of kind clone."))),
            fun td _ ~depth:_ _ctx _ _ -> ?: (option_map_tdecl_clone td)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-tdecl",
            CIn  (tdecl, "TD",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a task declaration."))),
                  fun td _ ~depth:_ _ctx _ _ -> !: (Format.asprintf "%a" Why3.Pretty.print_tdecl td)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-theory",
            CIn  (theory, "Th",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a theory symbol."))),
                  fun th _ ~depth:_ _ctx _ _ -> !: (Format.asprintf "%a" Why3.Pretty.print_th th)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-meta",
            CIn  (meta, "M",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a meta symbol."))),
            fun m _ ~depth:_ _ctx _ _ -> !: (Format.asprintf "%s" m.meta_name)),
        DocAbove );
  MLCode
  ( Pred ( "why3.pp-meta-arg",
            CIn  (meta_arg, "A",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Pretty-print a meta argument."))),
                  fun a _ ~depth:_ _ctx _ _ -> !: (Format.asprintf "%a" Why3.Pretty.print_meta_arg a)),
        DocAbove );
  MLCode
  ( Pred ("why3.pp-term",
            CIn  (term, "T",
            COut (Elpi_api_compat.BuiltInContextualData.string, "S",
            Read (in_ctx_for_term, "Convert a term to string using Why3's pretty printer"))),
            fun t _ ~depth:_ ctx _ _ -> !: 
             (Format.asprintf "@[<hov>%a@ |-@ %a@]@\n%!"
      (Elpi_api_compat.pp_ctx_field pp_ctx_for_term) ctx#ctx_for_term
       term.pp t)),
        DocAbove );
  ]