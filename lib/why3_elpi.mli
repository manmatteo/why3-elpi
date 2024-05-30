(* Embeddings of Why3 types *)


(** Declarations of builtin predicates and types *)
val declaration : Elpi.API.BuiltIn.declaration list
val document : Elpi.API.BuiltIn.declaration list -> unit

type ctx_for_term = Term.ctx_for_term
module Ctx_for_ctx_for_term = Term.Ctx_for_ctx_for_term (* :
  sig 
    class type t = object inherit Elpi.API.ContextualConversion.ctx end
  end *)
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
val context_made_of_ctx_for_term : (ctx_for_term, Why3.Term.vsymbol, #Elpi.API.ContextualConversion.ctx, 'a) Elpi.API.ContextualConversion.context
(* Embeddings of terms, types and tasks *)
val term : (Why3.Term.term, #Ctx_for_why_simple_term.t, 'b) Elpi.API.ContextualConversion.t
(* val ty : Why3.Ty.ty Elpi.API.Conversion.t *)
val env : (Why3.Env.env, 'a, 'b) Elpi.API.ContextualConversion.t

(* Embeddings of Why3 types *)
(* Other embeddings: constants (ty/l symbols) and variables for types and terms *)
val vsymbol : (Why3.Term.vsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val prsymbol : (Why3.Decl.prsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val decl : (Why3.Decl.decl, #Ctx_for_why_simple_term.t, 'b) Elpi.API.ContextualConversion.t

val task : (Why3.Task.task, #Ctx_for_why_simple_term.t, 'b) Elpi.API.ContextualConversion.t