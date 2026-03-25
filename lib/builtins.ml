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
      ( CPred ( "why3.var-type", in_ctx_for_ty,
            CIn  (vsymbol, "V",
            COut (ty, "T",
            CEasy "Get the type of a variable" )),
            fun var _ ~depth:_ _ctx  _-> !: (var.vs_ty)),
        DocAbove );
  MLCode
  ( CPred ( "why3.ls-type", in_ctx_for_ty,
            CIn  (lsymbol, "L",
            COut (ty, "T",
            CEasy "Get the value type of a logic symbol. Fails if the symbol has no value type (i.e. is a proposition)" )),
            fun ls _ ~depth:_ _ctx  _-> ?: (ls.ls_value)),
        DocAbove );
  MLCode
  ( CPred ("why3.pp-term", in_ctx_for_term,
            CIn  (term, "T",
            COut (Elpi.API.BuiltInContextualData.string, "S",
            CEasy "Convert a term to string using Why3's pretty printer" )),
            fun t _ ~depth:_ ctx  _-> !: 
             (Format.asprintf "@[<hov>%a@ |-@ %a@]@\n%!"
      (Elpi.API.RawData.Constants.Map.pp (Elpi.API.ContextualConversion.pp_ctx_entry pp_ctx_for_term)) ctx#ctx_for_term
       term.pp t)),
        DocAbove );
  ]