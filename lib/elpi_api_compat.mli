(** Compatibility shim providing fork-specific Elpi API additions. Replaces the
    Gopiandcode/elpi fork's additions to ContextualConversion,
    BuiltInContextualData, and Builtin.PPX. *)

(** Base class wrapping raw hypothetical context. Drop-in for the fork's
    [Elpi.API.ContextualConversion.ctx]. *)
class ctx : Elpi.API.Data.hyps -> object
  method raw : Elpi.API.Data.hyps
end

type 'a ctx_entry =
  { entry : 'a
  ; depth : int
  }

val pp_ctx_entry :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a ctx_entry -> unit

type 'a ctx_field = 'a ctx_entry Elpi.API.RawData.Constants.Map.t

val pp_ctx_field :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a ctx_field -> unit

(** Fork-compatible ctx_readback type: builds a context value from raw hyps. *)
type ('cls, 'csts) ctx_readback =
     depth:int
  -> Elpi.API.Data.hyps
  -> 'csts
  -> Elpi.API.Data.state
  -> Elpi.API.Data.state * 'cls * 'csts * Elpi.API.Conversion.extra_goals

(** Context descriptor – replaces the fork's
    [Elpi.API.ContextualConversion.context]. *)
type ('a, 'k, 'csts) context =
  { is_entry_for_nominal : Elpi.API.Data.hyp -> Elpi.API.RawData.constant option
  ; to_key : depth:int -> 'a -> 'k
  ; push :
         depth:int
      -> Elpi.API.Data.state
      -> 'k
      -> 'a ctx_entry
      -> Elpi.API.Data.state
  ; pop : depth:int -> Elpi.API.Data.state -> 'k -> Elpi.API.Data.state
  ; conv :
      ( Elpi.API.RawData.constant * 'a
      , unit
      , 'csts )
      Elpi.API.ContextualConversion.t
  ; init : Elpi.API.Data.state -> Elpi.API.Data.state
  ; get : Elpi.API.Data.state -> 'a ctx_field
  }

(** Process hyps into state. Drop-in for the fork's
    [Elpi.API.PPX.readback_context]. *)
val readback_context :
     ('a, 'k, 'csts) context
  -> depth:int
  -> Elpi.API.Data.hyps
  -> 'csts
  -> Elpi.API.Data.state
  -> Elpi.API.Data.state * Elpi.API.Conversion.extra_goals

module BuiltInContextualData : sig
  val int : (int, 'c, 'csts) Elpi.API.ContextualConversion.t
  val bool : (bool, 'c, 'csts) Elpi.API.ContextualConversion.t
  val float : (float, 'c, 'csts) Elpi.API.ContextualConversion.t
  val string : (string, 'c, 'csts) Elpi.API.ContextualConversion.t

  val nominal :
    (Elpi.API.RawData.constant, 'c, 'csts) Elpi.API.ContextualConversion.t

  val list :
       ('a, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('a list, 'c, 'csts) Elpi.API.ContextualConversion.t

  val polyA0 : (Elpi.API.Data.term, 'c, 'csts) Elpi.API.ContextualConversion.t
end

module PPX : sig
  val char : (char, 'c, 'csts) Elpi.API.ContextualConversion.t

  val option :
       ('a, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('a option, 'c, 'csts) Elpi.API.ContextualConversion.t

  val pair :
       ('a, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('b, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('a * 'b, 'c, 'csts) Elpi.API.ContextualConversion.t

  val triple :
       ('a, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('b, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('cc, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('a * 'b * 'cc, 'c, 'csts) Elpi.API.ContextualConversion.t

  val quadruple :
       ('a, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('b, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('cc, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('d, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('a * 'b * 'cc * 'd, 'c, 'csts) Elpi.API.ContextualConversion.t

  val quintuple :
       ('a, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('b, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('cc, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('d, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('e, 'c, 'csts) Elpi.API.ContextualConversion.t
    -> ('a * 'b * 'cc * 'd * 'e, 'c, 'csts) Elpi.API.ContextualConversion.t
end

module Doc : sig
  type prec_level =
    | Arrow
    | AppArg

  val show_ty_ast : ?prec:prec_level -> Elpi.API.Conversion.ty_ast -> string

  val kind :
    Format.formatter -> Elpi.API.Conversion.ty_ast -> doc:string -> unit

  val constructor :
       Format.formatter
    -> name:string
    -> doc:string
    -> ty:Elpi.API.Conversion.ty_ast
    -> args:Elpi.API.Conversion.ty_ast list
    -> unit

  val adt :
       doc:string
    -> ty:Elpi.API.Conversion.ty_ast
    -> args:(string * string * Elpi.API.Conversion.ty_ast list) list
    -> Format.formatter
    -> unit
    -> unit
end
