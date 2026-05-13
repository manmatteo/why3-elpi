open Term
open Ty
open Decl
open Theory

let in_ctx_for_ty = Ty.in_ctx_for_why_simple_ty
let in_ctx_for_term = Term.in_ctx_for_why_simple_term
let pp_ctx_for_term = Term.pp_ctx_for_term
let option_map_decl_body d g = decl_body_of_gref d g
let attrs_of_sattr attrs = Why3.Ident.Sattr.elements attrs
let attrs_of_ident id = attrs_of_sattr id.Why3.Ident.id_attrs

let sattr_of_attrs attrs =
  List.fold_left
    (fun sattr attr -> Why3.Ident.Sattr.add attr sattr)
    Why3.Ident.Sattr.empty attrs

let why3_builtin_declarations =
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInData in
  let open Elpi.API.BuiltInPredicate in
  let open Elpi.API.BuiltInPredicate.Notation in
  [ MLCode
      ( Pred
          ( "why3.mk-var"
          , CIn
              ( Elpi_api_compat.BuiltInContextualData.string
              , "Name"
              , CIn
                  ( ty
                  , "T"
                  , COut
                      ( vsymbol
                      , "V"
                      , Read
                          ( in_ctx_for_ty
                          , "Create a fresh Why3 variable symbol from a \
                             printed name and type." ) ) ) )
          , fun name ty _ ~depth:_ _ctx _ _ ->
              !:(Why3.Term.create_vsymbol (Why3.Ident.id_fresh name) ty) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.mk-tv"
          , CIn
              ( Elpi_api_compat.BuiltInContextualData.string
              , "Name"
              , COut
                  ( tvsymbol
                  , "Tv"
                  , Read
                      ( in_ctx_for_ty
                      , "Create a fresh Why3 type variable symbol from a \
                         printed name." ) ) )
          , fun name _ ~depth:_ _ctx _ _ ->
              !:(Why3.Ty.create_tvsymbol (Why3.Ident.id_fresh name)) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.mk-ts"
          , CIn
              ( Elpi_api_compat.BuiltInContextualData.string
              , "Name"
              , CIn
                  ( Elpi_api_compat.BuiltInContextualData.list tvsymbol
                  , "TvArgs"
                  , COut
                      ( tysymbol
                      , "Ts"
                      , Read
                          ( in_ctx_for_ty
                          , "Create a fresh abstract type symbol with the \
                             given name and type-variable arguments. Pass [] \
                             for a monomorphic (arity-0) type symbol." ) ) ) )
          , fun name tvargs _ ~depth:_ _ctx _ _ ->
              !:(Why3.Ty.create_tysymbol (Why3.Ident.id_fresh name) tvargs
                   Why3.Ty.NoDef) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.mk-ls"
          , CIn
              ( Elpi_api_compat.BuiltInContextualData.string
              , "Name"
              , CIn
                  ( Elpi_api_compat.BuiltInContextualData.list ty
                  , "Args"
                  , CIn
                      ( Elpi_api_compat.PPX.option ty
                      , "Result"
                      , COut
                          ( lsymbol
                          , "Ls"
                          , Read
                              ( in_ctx_for_ty
                              , "Create a fresh Why3 logic symbol. When Result \
                                 is (some T) creates a function symbol with \
                                 return type T; when Result is none creates a \
                                 predicate symbol (ls_value = None)." ) ) ) ) )
          , fun name args result _ ~depth:_ _ctx _ _ ->
              let ls =
                match result with
                | None ->
                  Why3.Term.create_psymbol (Why3.Ident.id_fresh name) args
                | Some ret ->
                  Why3.Term.create_fsymbol (Why3.Ident.id_fresh name) args ret
              in
              !:ls )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.var-name"
          , CIn
              ( vsymbol
              , "V"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "Name"
                  , Read
                      ( in_ctx_for_term
                      , "Project the printed name of a variable symbol." ) ) )
          , fun var _ ~depth:_ _ctx _ _ -> !:(var.vs_name.Why3.Ident.id_string)
          )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.var-attrs"
          , CIn
              ( vsymbol
              , "V"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list attribute
                  , "Attrs"
                  , Read
                      ( in_ctx_for_term
                      , "Project the attributes attached to a variable symbol."
                      ) ) )
          , fun var _ ~depth:_ _ctx _ _ -> !:(attrs_of_ident var.vs_name) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.prsymbol-name"
          , CIn
              ( prsymbol
              , "Pr"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "Name"
                  , Read
                      ( in_ctx_for_term
                      , "Project the printed name of a proposition symbol." ) )
              )
          , fun pr _ ~depth:_ _ctx _ _ -> !:(pr.pr_name.Why3.Ident.id_string) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.prsymbol-attrs"
          , CIn
              ( prsymbol
              , "Pr"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list attribute
                  , "Attrs"
                  , Read
                      ( in_ctx_for_term
                      , "Project the attributes attached to a proposition \
                         symbol." ) ) )
          , fun pr _ ~depth:_ _ctx _ _ -> !:(attrs_of_ident pr.pr_name) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.ls-name"
          , CIn
              ( lsymbol
              , "Ls"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "Name"
                  , Read
                      ( in_ctx_for_term
                      , "Project the printed name of a logic symbol." ) ) )
          , fun ls _ ~depth:_ _ctx _ _ -> !:(ls.ls_name.Why3.Ident.id_string) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.ls-attrs"
          , CIn
              ( lsymbol
              , "Ls"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list attribute
                  , "Attrs"
                  , Read
                      ( in_ctx_for_term
                      , "Project the attributes attached to a logic symbol." )
                  ) )
          , fun ls _ ~depth:_ _ctx _ _ -> !:(attrs_of_ident ls.ls_name) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.ls-args"
          , CIn
              ( lsymbol
              , "Ls"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list ty
                  , "Args"
                  , Read
                      ( in_ctx_for_ty
                      , "Return the argument types of a logic symbol." ) ) )
          , fun ls _ ~depth:_ _ctx _ _ -> !:(ls.ls_args) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.tysymbol-name"
          , CIn
              ( tysymbol
              , "Ts"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "Name"
                  , Read
                      ( in_ctx_for_ty
                      , "Project the printed name of a type symbol." ) ) )
          , fun ts _ ~depth:_ _ctx _ _ -> !:(ts.ts_name.Why3.Ident.id_string) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.tysymbol-attrs"
          , CIn
              ( tysymbol
              , "Ts"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list attribute
                  , "Attrs"
                  , Read
                      ( in_ctx_for_ty
                      , "Project the attributes attached to a type symbol." ) )
              )
          , fun ts _ ~depth:_ _ctx _ _ -> !:(attrs_of_ident ts.ts_name) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.ts-args"
          , CIn
              ( tysymbol
              , "Ts"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list tvsymbol
                  , "TvArgs"
                  , Read
                      ( in_ctx_for_ty
                      , "Return the type variable arguments (ts_args) of a \
                         type symbol." ) ) )
          , fun ts _ ~depth:_ _ctx _ _ -> !:(ts.ts_args) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.tv-name"
          , CIn
              ( tvsymbol
              , "Tv"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "Name"
                  , Read
                      ( in_ctx_for_ty
                      , "Project the printed name of a type variable symbol." )
                  ) )
          , fun tv _ ~depth:_ _ctx _ _ -> !:(tv.tv_name.Why3.Ident.id_string) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.tv-attrs"
          , CIn
              ( tvsymbol
              , "Tv"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list attribute
                  , "Attrs"
                  , Read
                      ( in_ctx_for_ty
                      , "Project the attributes attached to a type variable \
                         symbol." ) ) )
          , fun tv _ ~depth:_ _ctx _ _ -> !:(attrs_of_ident tv.tv_name) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.var-type"
          , CIn
              ( vsymbol
              , "V"
              , COut
                  (ty, "T", Read (in_ctx_for_ty, "Get the type of a variable"))
              )
          , fun var _ ~depth:_ _ctx _ _ -> !:(var.vs_ty) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.ls-type"
          , CIn
              ( lsymbol
              , "L"
              , COut
                  ( ty
                  , "T"
                  , Read
                      ( in_ctx_for_ty
                      , "Get the value type of a logic symbol. Fails if the \
                         symbol has no value type (i.e. is a proposition)" ) )
              )
          , fun ls _ ~depth:_ _ctx _ _ -> ?:(ls.ls_value) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.attr"
          , CIn
              ( Elpi_api_compat.BuiltInContextualData.string
              , "S"
              , COut
                  ( attribute
                  , "Attr"
                  , Read
                      ( in_ctx_for_term
                      , "Create a Why3 attribute from its string \
                         representation." ) ) )
          , fun name _ ~depth:_ _ctx _ _ -> !:(Why3.Ident.create_attribute name)
          )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.attr-string"
          , CIn
              ( attribute
              , "Attr"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read
                      ( in_ctx_for_term
                      , "Project the string representation of a Why3 attribute."
                      ) ) )
          , fun attr _ ~depth:_ _ctx _ _ -> !:(attr.Why3.Ident.attr_string) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.decl-kind"
          , CIn
              ( decl
              , "D"
              , COut
                  ( decl_kind
                  , "K"
                  , Read (in_ctx_for_term, "Classify a declaration.") ) )
          , fun d _ ~depth:_ _ctx _ _ ->
              !:(match d.Why3.Decl.d_node with
                | Why3.Decl.Dprop _ -> Decl_prop
                | Why3.Decl.Dtype _ -> Decl_type
                | Why3.Decl.Ddata _ -> Decl_data
                | Why3.Decl.Dind _ -> Decl_ind
                | Why3.Decl.Dlogic _ -> Decl_logic
                | Why3.Decl.Dparam _ -> Decl_param) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.decl-defines"
          , CIn
              ( decl
              , "D"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list gref
                  , "Refs"
                  , Read
                      ( in_ctx_for_term
                      , "Enumerate the global references defined by a \
                         declaration." ) ) )
          , fun d _ ~depth:_ _ctx _ _ -> !:(decl_defined_grefs d) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.decl-body"
          , CIn
              ( decl
              , "D"
              , CIn
                  ( gref
                  , "Ref"
                  , COut
                      ( decl_body
                      , "Body"
                      , Read
                          ( in_ctx_for_term
                          , "Project the opened body attached to a \
                             declaration/reference pair. Succeeds for \
                             proposition declarations and defined logic \
                             symbols." ) ) ) )
          , fun d g _ ~depth:_ _ctx _ _ -> ?:(option_map_decl_body d g) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-decl"
          , CIn
              ( decl
              , "D"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read (in_ctx_for_term, "Pretty-print a declaration.") ) )
          , fun d _ ~depth:_ _ctx _ _ ->
              !:(Format.asprintf "%a" Why3.Pretty.print_decl d) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-tdecl"
          , CIn
              ( tdecl
              , "TD"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read (in_ctx_for_term, "Pretty-print a task declaration.")
                  ) )
          , fun td _ ~depth:_ _ctx _ _ ->
              !:(Format.asprintf "%a" Why3.Pretty.print_tdecl td) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-theory"
          , CIn
              ( theory
              , "Th"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read (in_ctx_for_term, "Pretty-print a theory symbol.") ) )
          , fun th _ ~depth:_ _ctx _ _ ->
              !:(Format.asprintf "%a" Why3.Pretty.print_th th) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-meta"
          , CIn
              ( meta
              , "M"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read (in_ctx_for_term, "Pretty-print a meta symbol.") ) )
          , fun m _ ~depth:_ _ctx _ _ -> !:(Format.asprintf "%s" m.meta_name) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-meta-arg"
          , CIn
              ( meta_arg
              , "A"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read (in_ctx_for_term, "Pretty-print a meta argument.") ) )
          , fun a _ ~depth:_ _ctx _ _ ->
              !:(Format.asprintf "%a" Why3.Pretty.print_meta_arg a) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-term"
          , CIn
              ( term
              , "T"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read
                      ( in_ctx_for_term
                      , "Convert a term to string using Why3's pretty printer"
                      ) ) )
          , fun t _ ~depth:_ ctx _ _ -> !:(Format.asprintf "%a@\n%!" term.pp t)
          )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.pp-ty"
          , CIn
              ( ty
              , "T"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.string
                  , "S"
                  , Read
                      ( in_ctx_for_ty
                      , "Convert a type to string using Why3's pretty printer."
                      ) ) )
          , fun t _ ~depth:_ _ctx _ _ ->
              !:(Format.asprintf "%a" Why3.Pretty.print_ty t) )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.ls-full-type"
          , CIn
              ( lsymbol
              , "Ls"
              , COut
                  ( ty
                  , "Ty"
                  , Read
                      ( in_ctx_for_ty
                      , "Get the full arrow type of a logic symbol: arg1 -> \
                         ... -> argN -> result. Fails for predicates (no value \
                         type)." ) ) )
          , fun ls _ ~depth:_ _ctx _ _ ->
              match ls.Why3.Term.ls_value with
              | None -> raise Elpi.API.BuiltInPredicate.No_clause
              | Some ret ->
                let full =
                  List.fold_right Why3.Ty.ty_func ls.Why3.Term.ls_args ret
                in
                !:full )
      , DocAbove )
  ; MLCode
      ( Pred
          ( "why3.decl-data-constructors"
          , CIn
              ( decl
              , "D"
              , COut
                  ( Elpi_api_compat.BuiltInContextualData.list
                      (Elpi_api_compat.PPX.pair lsymbol
                         (Elpi_api_compat.BuiltInContextualData.list
                            (Elpi_api_compat.PPX.option lsymbol)))
                  , "Ctors"
                  , Read
                      ( in_ctx_for_ty
                      , "If D is a Ddata declaration, return the list of \
                         (constructor, projections) pairs. Each projection \
                         list entry is none if the field has no projection \
                         function, or some Proj otherwise. Fails if D is not a \
                         Ddata declaration." ) ) )
          , fun d _ ~depth:_ _ctx _ _ ->
              match d.Why3.Decl.d_node with
              | Why3.Decl.Ddata ddecls ->
                let ctors = List.concat_map (fun (_, ctors) -> ctors) ddecls in
                !:ctors
              | _ -> raise Elpi.API.BuiltInPredicate.No_clause )
      , DocAbove )
  ; LPDoc {|Convenience macros for working with the focused-goal API.|}
  ; LPCode
      {|
% [w3-ls-of-var! V Ls] Allocate a fresh lsymbol whose name and type are taken
% from variable symbol V. Shorthand for the three-step
%   why3.var-name V Name, why3.var-type V Ty, why3.mk-ls Name [] (some Ty) Ls
% preamble needed before introducing a local constant.
macro @w3-ls-of-var! V Ls :-
  why3.var-name V Name, why3.var-type V Ty, why3.mk-ls Name [] (some Ty) Ls.
|}
  ; LPCode
      {|
% [@pi-local-param! Ls GoalOut Next F] Build a local-symbol node for the
% uninterpreted constant Ls, bind a fresh ELPI nominal `x` for it in
% ctx-ls, and evaluate F x.  GoalOut is unified with the focused-goal wrapper
% and Next is the continuation binder.  Mirrors the coq-elpi @pi-decl macro.
%
% Typical usage for opening a forall as a local parameter:
%
%   inspect GoalPr (tquant tforall V Bnd) GoalOut :-
%     @w3-ls-of-var! V Ls,
%     @pi-local-param! Ls GoalOut Next (x\
%       inspect GoalPr (Bnd (tapp Ls [] none)) (Next x)).
macro @pi-local-param! Ls GoalOut Next F :-
  GoalOut = local-symbol Ls (_\ symbol-param) Next,
  pi x\ ctx-ls x Ls => F x.
|}
  ; LPCode
      {|
% [@pi-local-param-goal! Ls GoalOut F] Same as @pi-local-param!, but hides
% the continuation binder from the caller. F receives InnerGoal: the
% focused-goal hole to fill under the local-symbol wrapper.
%
% Note: `x` is a context token for ctx-ls lookup, not a term to embed.
% To open a binder body, keep using (tapp Ls [] none).
%
% Typical usage:
%
%   @pi-local-param-goal! Ls GoalOut (InnerGoal\
%     inspect GoalPr (Bnd (tapp Ls [] none)) InnerGoal).
macro @pi-local-param-goal! Ls GoalOut F :-
      GoalOut = local-symbol Ls (_\ symbol-param) (x\ Inner x),
      pi x\ ctx-ls x Ls => F (Inner x).
|}
  ; LPCode
      {|
% [@open-forall-local-param! V Bnd GoalOut F] Open a forall binder as a
% local-symbol parameter in one step. F receives:
% - Body: the binder body opened as Bnd (tapp Ls [] none)
% - InnerGoal: the focused-goal hole under the local-symbol wrapper.
%
% If you also need access to the freshly allocated lsymbol itself, use
% @w3-ls-of-var! followed by @pi-local-param-goal! directly.
%
% Typical usage:
%
%   @open-forall-local-param! V Bnd GoalOut (Body\ InnerGoal\
%     inspect GoalPr Body InnerGoal).
macro @open-forall-local-param! V Bnd GoalOut F :-
  @w3-ls-of-var! V Ls,
  @pi-local-param-goal! Ls GoalOut (InnerGoal\
    F (Bnd (tapp Ls [] none)) InnerGoal).
|}
  ]
