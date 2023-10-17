(** Embeddings of terms, types and tasks *)
val term : Why3.Term.term Elpi.API.Conversion.t
val ty : (Why3.Ty.ty, unit,unit) Elpi.API.ContextualConversion.t (* Ty is downcasted to build a list ty constructors, this forces the unit, unit *)
val task : Why3.Task.task Elpi.API.Conversion.t
val env : Why3.Env.env Elpi.API.Conversion.t

(** Declarations of builtin predicates and types *)
val why3_builtin_declarations : Elpi.API.BuiltIn.declaration list
val document : Elpi.API.BuiltIn.declaration list -> unit

(** Other embeddings: constants (ty/l symbols) and variables for types and terms *)
val tyvsym : Why3.Ty.tvsymbol Elpi.API.Conversion.t
val tysym : Why3.Ty.tysymbol Elpi.API.Conversion.t
val lsym : Why3.Term.lsymbol Elpi.API.Conversion.t
val vsym : Why3.Term.vsymbol Elpi.API.Conversion.t
val prsymbol : Why3.Decl.prsymbol Elpi.API.Conversion.t
val data_decl : Why3.Decl.data_decl Elpi.API.Conversion.t
val logic_decl : Why3.Decl.logic_decl Elpi.API.Conversion.t
val decl : Why3.Decl.decl Elpi.API.Conversion.t
