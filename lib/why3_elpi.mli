(** Declarations of builtin predicates and types *)
val declaration : Elpi.API.BuiltIn.declaration list

val why3_builtin_declarations : Elpi.API.BuiltIn.declaration list
val document : Elpi.API.BuiltIn.declaration list -> unit

type focused_goal

val focused_goal : (focused_goal, 'a, 'b) Elpi.API.ContextualConversion.t
val goal_decl_to_focused_goal : Why3.Decl.decl -> focused_goal option
val focused_goal_to_tdecls : focused_goal -> Why3.Theory.tdecl list

(* Embeddings of terms, types and tasks *)
val attribute : (Why3.Ident.attribute, 'a, 'b) Elpi.API.ContextualConversion.t
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

val split_focused_goal :
  Why3.Task.task -> (Why3.Theory.tdecl list * focused_goal) option

(** Runtime: ELPI program loading and query execution *)
val register_builtin_declaration : Elpi.API.BuiltIn.declaration -> unit

val declare_external_symbol :
  name:string -> ty:string -> Elpi.API.RawData.constant

val get_program : file:string -> Elpi.API.Setup.elpi * Elpi.API.Compile.program

val register_transform :
  name:string -> file:string -> entrypoint:int -> desc:Why3.Pp.formatted -> unit

val build_and_register_transform_with_args :
     name:string
  -> file:string
  -> entrypoint:int
  -> arg_type:('a, 'b) Why3.Args_wrapper.trans_typ
  -> desc:Why3.Pp.formatted
  -> unit
