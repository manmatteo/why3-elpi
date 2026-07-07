(** Declarations of builtin predicates and types *)
val declaration : Elpi.API.BuiltIn.declaration list

val why3_builtin_declarations : Elpi.API.BuiltIn.declaration list
val document : Elpi.API.BuiltIn.declaration list -> unit

(* Embeddings of terms, types and tasks *)
val attribute : (Term.attribute, 'a, 'b) Elpi.API.ContextualConversion.t
val term : (Why3.Term.term, 'a, 'b) Elpi.API.ContextualConversion.t
val lsymbol : (Why3.Term.lsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val ty : (Why3.Ty.ty, 'a, 'b) Elpi.API.ContextualConversion.t
val env : (Why3.Env.env, 'a, 'b) Elpi.API.ContextualConversion.t
val task : (Why3.Task.task, 'a, 'b) Elpi.API.ContextualConversion.t
val focused_task : (Why3.Task.task, 'a, 'b) Elpi.API.ContextualConversion.t
val decl : (Why3.Decl.decl, 'a, 'b) Elpi.API.ContextualConversion.t
val tdecl : (Why3.Theory.tdecl, 'a, 'b) Elpi.API.ContextualConversion.t
val vsymbol : (Why3.Term.vsymbol, 'a, 'b) Elpi.API.ContextualConversion.t
val prsymbol : (Why3.Decl.prsymbol, 'a, 'b) Elpi.API.ContextualConversion.t

val register_transform :
     name:string
  -> file:string
  -> arg_type:('a, 'b) Why3.Args_wrapper.trans_typ
  -> desc:Why3.Pp.formatted
  -> unit
