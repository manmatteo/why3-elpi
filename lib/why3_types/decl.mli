val decl_declaration : Elpi.API.BuiltIn.declaration list ref

val prsymbol :
  (Why3.Decl.prsymbol, 'a, 'b) Elpi.API.ContextualConversion.t

type gref

val gref :
  (gref, 'a, 'b) Elpi.API.ContextualConversion.t

type decl_kind =
  | Decl_prop
  | Decl_type
  | Decl_data
  | Decl_ind
  | Decl_logic
  | Decl_param

val decl_kind :
  (decl_kind, 'a, 'b) Elpi.API.ContextualConversion.t

type decl_body

val decl_body :
  (decl_body, 'a, 'b) Elpi.API.ContextualConversion.t

val decl_defined_grefs : Why3.Decl.decl -> gref list

val decl_body_of_gref : Why3.Decl.decl -> gref -> decl_body option

val decl :
  (Why3.Decl.decl, 'a, 'b) Elpi.API.ContextualConversion.t