open Term
open Ty
open Decl
open Theory

let in_ctx_for_ty = Ty.in_ctx_for_why_simple_ty
let in_ctx_for_term = Term.in_ctx_for_why_simple_term
let pp_ctx_for_term = Term.pp_ctx_for_term
let option_map_decl_body d g = decl_body_of_gref d g
let attrs_of_sattr = Term.attrs_of_sattr
let attrs_of_ident id = attrs_of_sattr id.Why3.Ident.id_attrs

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
  ; LPDoc
      {|The w3lp library: declarative helpers layered over the builtins.
Everything below is ordinary λProlog code; it is part of the same why3.*
namespace as the builtins on purpose, so that user code does not need to
know which predicates are external and which are not.|}
  ; LPCode
      {|
% ---- Formula classifiers ---------------------------------------------------
%
% Shape analysis on formulas, with no dedicated view types: a classifier is
% a total function from a term to an option over existing types (option,
% pair, the binop/quant tags, binders as term -> term). (some ...) carries
% the decomposed connective, none means "any other shape". Both are
% positive patterns, so a tactic that handles a few connectives and keeps
% everything else untouched dispatches on the classifier output with
% disjoint clauses — no cut and no negation as failure. All classifiers
% look through tattr/ttrigger wrappers.
%
% Every test below is plain unification in a clause head. Unification alone
% can only observe the succeeding side of a test, so the none clauses spell
% out the complement — here, in the library. This is the finite-type
% analogue of deciding string disequality with the s< order: reifying
% "does not match" as data needs the other cases stated positively.
%
% A tactic that only needs the succeeding side does not need a classifier
% at all: unify the stripped term against the wanted shape, e.g.
% (why3.strip T (tquant tforall V Bnd)), or match several disjoint shapes
% with one clause each (see examples/destruct.elpi).

% [why3.strip T T1] Remove the leading tattr/ttrigger wrappers of T.
func why3.strip term -> term.
why3.strip (tattr _ T) T1 :- why3.strip T T1.
why3.strip (ttrigger _ T) T1 :- why3.strip T T1.
why3.strip (tquant Q V Bnd) (tquant Q V Bnd).
why3.strip (tbinop Op A B) (tbinop Op A B).
why3.strip (tnot T) (tnot T).
why3.strip (tlet Def V Bnd) (tlet Def V Bnd).
why3.strip (tif C A B) (tif C A B).
why3.strip (tcase T Bs) (tcase T Bs).
why3.strip (tapp Ls Args Ty) (tapp Ls Args Ty).
why3.strip ttrue ttrue.
why3.strip tfalse tfalse.
why3.strip (tconst C Ty) (tconst C Ty).
why3.strip (teps V B) (teps V B).

% [why3.as-binop T O] some (pr Op (pr A B)) when T is the binary connective
% Op applied to A and B, none for any other shape. One clause covers the
% four connectives: the tag is returned, not matched.
func why3.as-binop term -> option (pair binop (pair term term)).
why3.as-binop (tattr _ T) O :- why3.as-binop T O.
why3.as-binop (ttrigger _ T) O :- why3.as-binop T O.
why3.as-binop (tbinop Op A B) (some (pr Op (pr A B))).
why3.as-binop (tquant _ _ _) none.
why3.as-binop (tnot _) none.
why3.as-binop (tlet _ _ _) none.
why3.as-binop (tif _ _ _) none.
why3.as-binop (tcase _ _) none.
why3.as-binop (tapp _ _ _) none.
why3.as-binop ttrue none.
why3.as-binop tfalse none.
why3.as-binop (tconst _ _) none.
why3.as-binop (teps _ _) none.

% [why3.as-quant T O] some (pr Q (pr V Bnd)) when T is the quantifier Q
% binding the variable symbol V in Bnd, none for any other shape.
func why3.as-quant term -> option (pair quant (pair var (term -> term))).
why3.as-quant (tattr _ T) O :- why3.as-quant T O.
why3.as-quant (ttrigger _ T) O :- why3.as-quant T O.
why3.as-quant (tquant Q V Bnd) (some (pr Q (pr V Bnd))).
why3.as-quant (tbinop _ _ _) none.
why3.as-quant (tnot _) none.
why3.as-quant (tlet _ _ _) none.
why3.as-quant (tif _ _ _) none.
why3.as-quant (tcase _ _) none.
why3.as-quant (tapp _ _ _) none.
why3.as-quant ttrue none.
why3.as-quant tfalse none.
why3.as-quant (tconst _ _) none.
why3.as-quant (teps _ _) none.

% [why3.as-let T O] some (pr Def (pr V Bnd)) when T is a let-binder, none
% for any other shape.
func why3.as-let term -> option (pair term (pair var (term -> term))).
why3.as-let (tattr _ T) O :- why3.as-let T O.
why3.as-let (ttrigger _ T) O :- why3.as-let T O.
why3.as-let (tlet Def V Bnd) (some (pr Def (pr V Bnd))).
why3.as-let (tquant _ _ _) none.
why3.as-let (tbinop _ _ _) none.
why3.as-let (tnot _) none.
why3.as-let (tif _ _ _) none.
why3.as-let (tcase _ _) none.
why3.as-let (tapp _ _ _) none.
why3.as-let ttrue none.
why3.as-let tfalse none.
why3.as-let (tconst _ _) none.
why3.as-let (teps _ _) none.

% Per-connective classifiers: some (pr A B), respectively some (pr V Bnd),
% when the head of the formula is the named connective, none otherwise.
% All the testing is unification in the clause heads: the some clause
% matches the connective, the none clauses spell out every other shape.

func why3.as-implies term -> option (pair term term).
why3.as-implies (tattr _ T) O :- why3.as-implies T O.
why3.as-implies (ttrigger _ T) O :- why3.as-implies T O.
why3.as-implies (tbinop timplies A B) (some (pr A B)).
why3.as-implies (tbinop tand _ _) none.
why3.as-implies (tbinop tor _ _) none.
why3.as-implies (tbinop tiff _ _) none.
why3.as-implies (tquant _ _ _) none.
why3.as-implies (tnot _) none.
why3.as-implies (tlet _ _ _) none.
why3.as-implies (tif _ _ _) none.
why3.as-implies (tcase _ _) none.
why3.as-implies (tapp _ _ _) none.
why3.as-implies ttrue none.
why3.as-implies tfalse none.
why3.as-implies (tconst _ _) none.
why3.as-implies (teps _ _) none.

func why3.as-and term -> option (pair term term).
why3.as-and (tattr _ T) O :- why3.as-and T O.
why3.as-and (ttrigger _ T) O :- why3.as-and T O.
why3.as-and (tbinop tand A B) (some (pr A B)).
why3.as-and (tbinop tor _ _) none.
why3.as-and (tbinop timplies _ _) none.
why3.as-and (tbinop tiff _ _) none.
why3.as-and (tquant _ _ _) none.
why3.as-and (tnot _) none.
why3.as-and (tlet _ _ _) none.
why3.as-and (tif _ _ _) none.
why3.as-and (tcase _ _) none.
why3.as-and (tapp _ _ _) none.
why3.as-and ttrue none.
why3.as-and tfalse none.
why3.as-and (tconst _ _) none.
why3.as-and (teps _ _) none.

func why3.as-or term -> option (pair term term).
why3.as-or (tattr _ T) O :- why3.as-or T O.
why3.as-or (ttrigger _ T) O :- why3.as-or T O.
why3.as-or (tbinop tor A B) (some (pr A B)).
why3.as-or (tbinop tand _ _) none.
why3.as-or (tbinop timplies _ _) none.
why3.as-or (tbinop tiff _ _) none.
why3.as-or (tquant _ _ _) none.
why3.as-or (tnot _) none.
why3.as-or (tlet _ _ _) none.
why3.as-or (tif _ _ _) none.
why3.as-or (tcase _ _) none.
why3.as-or (tapp _ _ _) none.
why3.as-or ttrue none.
why3.as-or tfalse none.
why3.as-or (tconst _ _) none.
why3.as-or (teps _ _) none.

func why3.as-iff term -> option (pair term term).
why3.as-iff (tattr _ T) O :- why3.as-iff T O.
why3.as-iff (ttrigger _ T) O :- why3.as-iff T O.
why3.as-iff (tbinop tiff A B) (some (pr A B)).
why3.as-iff (tbinop tand _ _) none.
why3.as-iff (tbinop tor _ _) none.
why3.as-iff (tbinop timplies _ _) none.
why3.as-iff (tquant _ _ _) none.
why3.as-iff (tnot _) none.
why3.as-iff (tlet _ _ _) none.
why3.as-iff (tif _ _ _) none.
why3.as-iff (tcase _ _) none.
why3.as-iff (tapp _ _ _) none.
why3.as-iff ttrue none.
why3.as-iff tfalse none.
why3.as-iff (tconst _ _) none.
why3.as-iff (teps _ _) none.

func why3.as-forall term -> option (pair var (term -> term)).
why3.as-forall (tattr _ T) O :- why3.as-forall T O.
why3.as-forall (ttrigger _ T) O :- why3.as-forall T O.
why3.as-forall (tquant tforall V Bnd) (some (pr V Bnd)).
why3.as-forall (tquant texists _ _) none.
why3.as-forall (tbinop _ _ _) none.
why3.as-forall (tnot _) none.
why3.as-forall (tlet _ _ _) none.
why3.as-forall (tif _ _ _) none.
why3.as-forall (tcase _ _) none.
why3.as-forall (tapp _ _ _) none.
why3.as-forall ttrue none.
why3.as-forall tfalse none.
why3.as-forall (tconst _ _) none.
why3.as-forall (teps _ _) none.

func why3.as-exists term -> option (pair var (term -> term)).
why3.as-exists (tattr _ T) O :- why3.as-exists T O.
why3.as-exists (ttrigger _ T) O :- why3.as-exists T O.
why3.as-exists (tquant texists V Bnd) (some (pr V Bnd)).
why3.as-exists (tquant tforall _ _) none.
why3.as-exists (tbinop _ _ _) none.
why3.as-exists (tnot _) none.
why3.as-exists (tlet _ _ _) none.
why3.as-exists (tif _ _ _) none.
why3.as-exists (tcase _ _) none.
why3.as-exists (tapp _ _ _) none.
why3.as-exists ttrue none.
why3.as-exists tfalse none.
why3.as-exists (tconst _ _) none.
why3.as-exists (teps _ _) none.

% [why3.app F X FX] Higher-order application through Why3's function
% application symbol (infix @).
func why3.app term, term -> term.
why3.app F X (tapp infix_at [F, X] none).
|}
  ; LPCode
      {|
% ---- Local symbols --------------------------------------------------------

% [why3.intro-var V Bnd Body Wrap] Open the binder Bnd, whose bound variable
% symbol is V, by introducing a local constant with V's printed name and
% type. Body is the binder body with the constant substituted for the bound
% variable, and (Wrap G) wraps a focused goal G with the constant's
% declaration. Typical use, opening a universally quantified goal:
%
%   intro GoalPr T (Wrap Inner) :-
%     why3.strip T (tquant tforall V Bnd),
%     why3.intro-var V Bnd Body Wrap,
%     intro GoalPr Body Inner.
func why3.intro-var var, (term -> term) -> term, (focused-goal -> focused-goal).
why3.intro-var V Bnd (Bnd Occ) (g\ local-symbol Ls symbol-param g) :-
  why3.var-name V Name,
  why3.var-type V Ty,
  why3.mk-ls Name [] (some Ty) Ls,
  Occ = tapp Ls [] none.

% [why3.intro-def V Def Occ Wrap] Introduce a local defined symbol carrying
% V's printed name and type, with definition body Def. Occ is the term
% standing for the new symbol and (Wrap G) wraps a focused goal G with the
% definition.
func why3.intro-def var, decl_body -> term, (focused-goal -> focused-goal).
why3.intro-def V Def (tapp Ls [] none) (g\ local-symbol Ls (symbol-logic Def) g) :-
  why3.var-name V Name,
  why3.var-type V Ty,
  why3.mk-ls Name [] (some Ty) Ls.
|}
  ; LPCode
      {|
% ---- The task context as clauses ------------------------------------------
%
% [why3.with-context Decls K] runs K with one (why3.defines Ref D) clause
% per global reference defined by the task prefix Decls. Lookups then are
% indexed clause resolution instead of list traversal:
%
%   why3.with-context Decls (why3.premise Lemma Statement, ...)

:index (2)
pred why3.defines o:gref, o:decl.

pred why3.with-context i:list tdecl, i:prop.
why3.with-context [] K :- K.
why3.with-context [decl D | Rest] K :-
  why3.decl-defines D Refs,
  why3.load-refs Refs D Rest K.
why3.with-context [use _ | Rest] K :- why3.with-context Rest K.
why3.with-context [meta _ _ | Rest] K :- why3.with-context Rest K.
why3.with-context [clone _ | Rest] K :- why3.with-context Rest K.

pred why3.load-refs i:list gref, i:decl, i:list tdecl, i:prop.
why3.load-refs [] _ Rest K :- why3.with-context Rest K.
why3.load-refs [Ref | Refs] D Rest K :-
  why3.defines Ref D => why3.load-refs Refs D Rest K.

% Relational views of the loaded context; they enumerate on backtracking.

% [why3.premise Pr T] The task prefix declares the proposition Pr (an axiom
% or previously proved lemma) with statement T.
pred why3.premise o:prsymbol, o:term.
why3.premise Pr T :- why3.defines (gpr Pr) D, why3.decl-body D (gpr Pr) (dterm T).

% [why3.param Ls] The task prefix declares Ls as an uninterpreted symbol.
pred why3.param o:lsymbol.
why3.param Ls :- why3.defines (gls Ls) D, why3.decl-kind D decl-param.

% [why3.defined Ls Body] The task prefix defines the logic symbol Ls.
pred why3.defined o:lsymbol, o:decl_body.
why3.defined Ls B :-
  why3.defines (gls Ls) D, why3.decl-kind D decl-logic, why3.decl-body D (gls Ls) B.

% [why3.datatype Ts D] The task prefix declares the algebraic type Ts; D is
% its declaration, for use with why3.decl-data-constructors.
pred why3.datatype o:tysymbol, o:decl.
why3.datatype Ts D :- why3.defines (gty Ts) D, why3.decl-kind D decl-data.
|}
  ; LPCode
      {|
% ---- Local hypotheses as clauses -------------------------------------------
%
% The local counterpart of why3.with-context: the wrappers of a focused
% goal become clauses, so premise lookup and hypothesis lookup are both
% clause resolution.

% [why3.hyp Name T] A local hypothesis Name : T is in scope.
pred why3.hyp o:string, o:term.

% [why3.local-def Ls D] A local symbol declaration for Ls is in scope.
pred why3.local-def o:lsymbol, o:local-symbol-decl.

% [why3.local-ty Ts] A local type symbol Ts is in scope.
pred why3.local-ty o:tysymbol.

% [why3.with-hyps G K] Walk the local declarations of the focused goal G,
% loading one clause (why3.hyp, why3.local-def, why3.local-ty) per wrapper,
% and run (K Pr Conclusion) on the conclusion.
pred why3.with-hyps i:focused-goal, i:(pred i:prsymbol, i:term).
why3.with-hyps (goal-formula Pr T) K :- K Pr T.
why3.with-hyps (local-prop Name H Rest) K :- why3.hyp Name H => why3.with-hyps Rest K.
why3.with-hyps (local-symbol Ls D Rest) K :- why3.local-def Ls D => why3.with-hyps Rest K.
why3.with-hyps (local-type Ts Rest) K :- why3.local-ty Ts => why3.with-hyps Rest K.

% [why3.assume-hyps Hs K] Run K with one extra why3.hyp clause per pair.
pred why3.assume-hyps i:list (pair string term), i:prop.
why3.assume-hyps [] K :- K.
why3.assume-hyps [pr Name T | Hs] K :- why3.hyp Name T => why3.assume-hyps Hs K.

% [why3.hypothesis Name T] Uniform lookup over both hypothesis sources:
% the local hypotheses of the focused goal and the premises of the task
% prefix.
pred why3.hypothesis o:string, o:term.
why3.hypothesis Name T :- why3.hyp Name T.
why3.hypothesis Name T :- why3.premise Pr T, why3.prsymbol-name Pr Name.

% [why3.split-hyp Name G Wrap Hyp Tail] Zipper on the goal spine at the
% outermost local hypothesis named Name:
%   G = Wrap (local-prop Name Hyp Tail).
% The first two clauses are exclusive through positive tests only: the
% nonlinear head of the first one requires the hypothesis name to be the
% target, the why3.string-neq guard of the second one requires it not to
% be (string disequality is decided by the total order on strings).
pred why3.split-hyp i:string, i:focused-goal, o:(focused-goal -> focused-goal), o:term, o:focused-goal.
why3.split-hyp Name (local-prop Name Hyp Tail) (g\ g) Hyp Tail.
why3.split-hyp Name (local-prop N H Rest) (g\ local-prop N H (Wrap g)) Hyp Tail :-
  why3.string-neq N Name,
  why3.split-hyp Name Rest Wrap Hyp Tail.
why3.split-hyp Name (local-symbol Ls D Rest) (g\ local-symbol Ls D (Wrap g)) Hyp Tail :-
  why3.split-hyp Name Rest Wrap Hyp Tail.
why3.split-hyp Name (local-type Ts Rest) (g\ local-type Ts (Wrap g)) Hyp Tail :-
  why3.split-hyp Name Rest Wrap Hyp Tail.
|}
  ; LPCode
      {|
% ---- Focused-goal spine helpers -------------------------------------------

% [why3.goal-conclusion G Pr T] Project the conclusion formula and its
% proposition symbol out of a focused goal.
func why3.goal-conclusion focused-goal -> prsymbol, term.
why3.goal-conclusion (goal-formula Pr T) Pr T.
why3.goal-conclusion (local-prop _ _ G) Pr T :- why3.goal-conclusion G Pr T.
why3.goal-conclusion (local-symbol _ _ G) Pr T :- why3.goal-conclusion G Pr T.
why3.goal-conclusion (local-type _ G) Pr T :- why3.goal-conclusion G Pr T.

% [why3.goal-hyps G Hs] Collect the local hypotheses of a focused goal,
% outermost first, as (pr Name Formula) pairs.
func why3.goal-hyps focused-goal -> list (pair string term).
why3.goal-hyps (goal-formula _ _) [].
why3.goal-hyps (local-prop N H G) [pr N H | Hs] :- why3.goal-hyps G Hs.
why3.goal-hyps (local-symbol _ _ G) Hs :- why3.goal-hyps G Hs.
why3.goal-hyps (local-type _ G) Hs :- why3.goal-hyps G Hs.

% [why3.set-conclusion G T Out] Replace the conclusion formula of G by T,
% keeping the goal symbol and all local declarations.
func why3.set-conclusion focused-goal, term -> focused-goal.
why3.set-conclusion (goal-formula Pr _) T (goal-formula Pr T).
why3.set-conclusion (local-prop N H G) T (local-prop N H G1) :- why3.set-conclusion G T G1.
why3.set-conclusion (local-symbol L D G) T (local-symbol L D G1) :- why3.set-conclusion G T G1.
why3.set-conclusion (local-type Ts G) T (local-type Ts G1) :- why3.set-conclusion G T G1.

% [why3.graft-conclusion G New Out] Replace the goal-formula node at the end
% of the spine of G with the focused goal New, keeping all local
% declarations of G.
func why3.graft-conclusion focused-goal, focused-goal -> focused-goal.
why3.graft-conclusion (goal-formula _ _) New New.
why3.graft-conclusion (local-prop N H G) New (local-prop N H G1) :- why3.graft-conclusion G New G1.
why3.graft-conclusion (local-symbol L D G) New (local-symbol L D G1) :- why3.graft-conclusion G New G1.
why3.graft-conclusion (local-type Ts G) New (local-type Ts G1) :- why3.graft-conclusion G New G1.

% [why3.wrap-hyps Hs G Out] Wrap the focused goal G with the local
% hypotheses Hs, outermost first.
func why3.wrap-hyps list (pair string term), focused-goal -> focused-goal.
why3.wrap-hyps [] G G.
why3.wrap-hyps [pr N H | Hs] G (local-prop N H G1) :- why3.wrap-hyps Hs G G1.
|}
  ; LPCode
      {|
% ---- Decidable string and attribute tests -----------------------------------
%
% Disequality of strings is defined positively through the total order s<,
% so the boolean tests below involve no negation as failure. Some of them
% are declared pred rather than func only because their clauses are
% exclusive through guards or nonlinear heads, which the determinacy
% checker cannot verify; they are still functional relations.

pred why3.string-neq i:string, i:string.
why3.string-neq S1 S2 :- S1 s< S2.
why3.string-neq S1 S2 :- S2 s< S1.

% [why3.string-eq S1 S2 B] Total boolean string equality.
pred why3.string-eq i:string, i:string, o:bool.
why3.string-eq S S tt.
why3.string-eq S1 S2 ff :- why3.string-neq S1 S2.

% [why3.has-attr Attrs Name B] Total boolean test: does Attrs contain the
% attribute whose printed string is Name?
pred why3.has-attr i:list attribute, i:string, o:bool.
why3.has-attr [] _ ff.
why3.has-attr [attr S | As] Name B :-
  why3.string-eq S Name Eq,
  why3.has-attr-cont Eq As Name B.

pred why3.has-attr-cont i:bool, i:list attribute, i:string, o:bool.
why3.has-attr-cont tt _ _ tt.
why3.has-attr-cont ff As Name B :- why3.has-attr As Name B.

% [why3.term-attrs T Attrs] The attributes wrapping the head of T; [] when
% T is not a tattr node.
func why3.term-attrs term -> list attribute.
why3.term-attrs (tattr Attrs _) Attrs.
why3.term-attrs (ttrigger _ _) [].
why3.term-attrs (tconst _ _) [].
why3.term-attrs (tapp _ _ _) [].
why3.term-attrs (tlet _ _ _) [].
why3.term-attrs (tquant _ _ _) [].
why3.term-attrs (teps _ _) [].
why3.term-attrs ttrue [].
why3.term-attrs tfalse [].
why3.term-attrs (tbinop _ _ _) [].
why3.term-attrs (tif _ _ _) [].
why3.term-attrs (tnot _) [].
why3.term-attrs (tcase _ _) [].

% [why3.attr-value Attrs Key VOpt] Total lookup of a "Key:Value" attribute:
% VOpt is (some Value) for the first attribute of Attrs whose string is
% Key:Value, and none if there is no such attribute.
pred why3.attr-value i:list attribute, i:string, o:option string.
why3.attr-value [] _ none.
why3.attr-value [attr S | As] Key VOpt :-
  rex.split ":" S Parts,
  why3.attr-value-parts Parts As Key VOpt.

pred why3.attr-value-parts i:list string, i:list attribute, i:string, o:option string.
why3.attr-value-parts [] As Key VOpt :- why3.attr-value As Key VOpt.
why3.attr-value-parts [_] As Key VOpt :- why3.attr-value As Key VOpt.
why3.attr-value-parts [K, V] As Key VOpt :-
  why3.string-eq K Key Eq,
  why3.attr-value-hit Eq V As Key VOpt.
why3.attr-value-parts [_, _, _ | _] As Key VOpt :- why3.attr-value As Key VOpt.

pred why3.attr-value-hit i:bool, i:string, i:list attribute, i:string, o:option string.
why3.attr-value-hit tt V _ _ (some V).
why3.attr-value-hit ff _ As Key VOpt :- why3.attr-value As Key VOpt.
|}
  ; LPCode
      {|
% ---- Task prefix surgery ---------------------------------------------------

% [why3.tdecl-defines TD Ref] Relates a task declaration to the global
% references it defines.
pred why3.tdecl-defines i:tdecl, o:gref.
why3.tdecl-defines (decl D) Ref :- why3.decl-defines D Refs, std.mem Refs Ref.

% [why3.remove-defining Ref Decls Out] Out is Decls without a declaration
% defining Ref. The clauses overlap on purpose: which occurrence to remove
% is a relational choice, and the first solution removes the first
% defining declaration. Fails when no declaration defines Ref.
pred why3.remove-defining i:gref, i:list tdecl, o:list tdecl.
why3.remove-defining Ref [TD | Rest] Rest :- why3.tdecl-defines TD Ref.
why3.remove-defining Ref [TD | Rest] [TD | Out] :-
  why3.remove-defining Ref Rest Out.
|}
  ]
