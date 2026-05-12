(** Declarations of builtin predicates and types *)
val declaration : Elpi.API.BuiltIn.declaration list
val why3_builtin_declarations : Elpi.API.BuiltIn.declaration list
val document : Elpi.API.BuiltIn.declaration list -> unit

type ctx_for_term
module Ctx_for_why_simple_term = Term.Ctx_for_why_simple_term
val ctx_for_term : (int * ctx_for_term, 'a, 'b) Elpi.API.ContextualConversion.t
val context_made_of_ctx_for_term : (ctx_for_term, Why3.Term.vsymbol, 'a) Elpi_api_compat.context
val in_ctx_for_term : (Term.ctx_for_why_simple_term, Elpi.API.Data.constraints) Elpi_api_compat.ctx_readback
val pp_ctx_for_term : Format.formatter -> ctx_for_term -> unit

type focused_goal
val focused_goal : (focused_goal, 'a, 'b) Elpi.API.ContextualConversion.t
val goal_decl_to_focused_goal : Why3.Decl.decl -> focused_goal option
val focused_goal_to_tdecls : focused_goal -> Why3.Theory.tdecl list

val in_ctx_for_ty : (Ty.ctx_for_why_simple_ty, Elpi.API.Data.constraints) Elpi_api_compat.ctx_readback

(* Embeddings of terms, types and tasks *)
val attribute : (Why3.Ident.attribute, 'a, 'b) Elpi.API.ContextualConversion.t
val term : (Why3.Term.term, 'a, 'b) Elpi.API.ContextualConversion.t
val lsymbol : (Why3.Term.lsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val ty   : (Why3.Ty.ty, 'a, 'b) Elpi.API.ContextualConversion.t
val env  : (Why3.Env.env, 'a, 'b) Elpi.API.ContextualConversion.t
val task : (Why3.Task.task, 'a, 'b) Elpi.API.ContextualConversion.t
val focused_task : (Why3.Task.task, 'a, 'b) Elpi.API.ContextualConversion.t
val decl : (Why3.Decl.decl, 'a, 'b) Elpi.API.ContextualConversion.t
val tdecl : (Why3.Theory.tdecl, 'a, 'b) Elpi.API.ContextualConversion.t
val vsymbol : (Why3.Term.vsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val prsymbol : (Why3.Decl.prsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val split_focused_goal : Why3.Task.task -> (Why3.Theory.tdecl list * focused_goal) option

(** Runtime: ELPI program loading and query execution *)
val register_builtin_declaration : Elpi.API.BuiltIn.declaration -> unit
val declare_external_symbol : name:string -> ty:string -> Elpi.API.RawData.constant
val get_program : file:string -> Elpi.API.Setup.elpi * Elpi.API.Compile.program
val run_query_with :
  Elpi.API.Compile.program ->
  (Elpi.API.Data.state ->
   Elpi.API.Data.state * Elpi.API.Data.term * Elpi.API.Conversion.extra_goals) ->
  ('a, 'b list, Elpi.API.Data.constraints) Elpi.API.ContextualConversion.t ->
  'a list option