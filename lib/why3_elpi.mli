(* Embeddings of Why3 types *)


(** Declarations of builtin predicates and types *)
val declaration : Elpi.API.BuiltIn.declaration list
val why3_builtin_declarations : Elpi.API.BuiltIn.declaration list
val document : Elpi.API.BuiltIn.declaration list -> unit

type ctx_for_term = Term.ctx_for_term
module Ctx_for_why_simple_term = Term.Ctx_for_why_simple_term
(* :
  sig 
    class type t =
      object
        inherit Elpi.API.ContextualConversion.ctx
        inherit Ctx_for_ctx_for_term.t
        method  ctx_for_term :
          ctx_for_term Elpi.API.ContextualConversion.ctx_field
      end
  end *)
val ctx_for_term : (int * ctx_for_term, 'a, 'b) Elpi.API.ContextualConversion.t
val context_made_of_ctx_for_term : (ctx_for_term, Why3.Term.vsymbol, 'a) Elpi_api_compat.context
val in_ctx_for_term : (Term.ctx_for_why_simple_term, Elpi.API.Data.constraints) Elpi_api_compat.ctx_readback
val pp_ctx_for_term : Format.formatter -> ctx_for_term -> unit

type focused_goal = Term.focused_goal
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

(* Other embeddings: constants (ty/l symbols) and variables for types and terms *)
val vsymbol : (Why3.Term.vsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val prsymbol : (Why3.Decl.prsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val split_focused_goal : Why3.Task.task -> (Why3.Theory.tdecl list * focused_goal) option