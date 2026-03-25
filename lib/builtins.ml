open Term
open Ty

let in_ctx_for_ty = Ty.in_ctx_for_why_simple_ty
let in_ctx_for_term = Term.in_ctx_for_why_simple_term
let pp_ctx_for_term = Term.pp_ctx_for_term

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