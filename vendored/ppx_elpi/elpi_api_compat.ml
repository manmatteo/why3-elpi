(** Runtime support library for the vendored ppx_elpi (declared in its
    [ppx_runtime_libraries]). Contains what remains of the Gopiandcode/elpi
    fork's API that upstream Elpi never adopted: the hypothetical-context
    readback machinery and the PPX.Doc documentation helpers, plus contextual
    lifts of a few builtin conversions. Everything here compiles against
    mainline Elpi; nothing re-implements deleted API. *)

open Elpi.API

(** Base class wrapping raw hypothetical context. Provides the same interface as
    the fork's [ContextualConversion.ctx]. *)
class ctx (h : Data.hyps) =
  object
    method raw = h
  end

(** A context entry: a value together with its bind depth. *)
type 'a ctx_entry =
  { entry : 'a
  ; depth : int
  }

let pp_ctx_entry pp fmt { entry; _ } = pp fmt entry

let pp_ctx_field pp fmt field =
  let first = ref true in
  Elpi.API.RawData.Constants.Map.iter
    (fun key entry ->
      if !first then first := false else Format.fprintf fmt ", ";
      Format.fprintf fmt "%s:%a"
        (Elpi.API.RawData.Constants.show key)
        (pp_ctx_entry pp) entry)
    field

(** A context field: a map from De Bruijn constants to context entries. *)
type 'a ctx_field = 'a ctx_entry RawData.Constants.Map.t

(** A context descriptor: everything needed to read back a contextual type from
    the hypothetical context. The [conv] type uses [unit] for the [hyps]
    parameter because the embed/readback functions ignore the context object
    (they rely on state instead). *)
type ('a, 'k, 'csts) context =
  { is_entry_for_nominal : Data.hyp -> RawData.constant option
  ; to_key : depth:int -> 'a -> 'k
  ; push : depth:int -> Data.state -> 'k -> 'a ctx_entry -> Data.state
  ; pop : depth:int -> Data.state -> 'k -> Data.state
  ; conv : (RawData.constant * 'a, unit, 'csts) ContextualConversion.t
  ; init : Data.state -> Data.state
  ; get : Data.state -> 'a ctx_field
  }

(** Process the hypothetical context: for each hyp that corresponds to a context
    entry (as determined by [ctx.is_entry_for_nominal]), read back the entry and
    register it in the state via [ctx.push]. Returns the updated state and
    accumulated extra goals. *)
let readback_context ctx ~depth hyps csts state =
  (* Re-initialise the context state component. *)
  let state = ctx.init state in
  List.fold_left
    (fun (state, gls) hyp ->
      let raw = RawData.of_hyp hyp in
      match ctx.is_entry_for_nominal hyp with
      | None -> (state, gls)
      | Some nominal ->
        let depth_hyp = raw.RawData.hdepth in
        (* Read back the context entry using unit as the "context" (the
           embed/readback for ctx entries never actually use the context
           object—they look things up in state). *)
        let state, (_, entry), entry_gls =
          ctx.conv.ContextualConversion.readback ~depth:depth_hyp () csts state
            raw.RawData.hsrc
        in
        let key = ctx.to_key ~depth:depth_hyp entry in
        let ctx_entry = { entry; depth = depth_hyp } in
        let state = ctx.push ~depth:nominal state key ctx_entry in
        (state, gls @ entry_gls))
    (state, []) hyps

(* Context readbacks are typed with the upstream
   [Elpi.API.ContextualConversion.ctx_readback], instantiated at
   [Data.constraints]; no fork-specific type is needed. *)

(* ------------------------------------------------------------------ *)
(** {2 Contextual conversions for built-in types}

    These are [ContextualConversion.(!>)] of the corresponding builtin
    conversions, spelled out as record literals: [!>] is a function application,
    so a module-level [let int = !> BuiltInData.int] would be weakly polymorphic
    (value restriction) and could not serve two different context types. Record
    literals with projection/lambda fields are nonexpansive, hence fully
    polymorphic. *)

module BuiltInContextualData = struct
  (** Lift a plain [Conversion.t] to work in any contextual context. *)
  let int : (int, 'ctx, 'csts) ContextualConversion.t =
    { ContextualConversion.ty = BuiltInData.int.ty
    ; pp_doc = BuiltInData.int.pp_doc
    ; pp = BuiltInData.int.pp
    ; embed = (fun ~depth _ctx _csts s x -> BuiltInData.int.embed ~depth s x)
    ; readback =
        (fun ~depth _ctx _csts s t -> BuiltInData.int.readback ~depth s t)
    }

  let bool : (bool, 'ctx, 'csts) ContextualConversion.t =
    { ContextualConversion.ty = Elpi.Builtin.bool.ty
    ; pp_doc = Elpi.Builtin.bool.pp_doc
    ; pp = Elpi.Builtin.bool.pp
    ; embed = (fun ~depth _ctx _csts s x -> Elpi.Builtin.bool.embed ~depth s x)
    ; readback =
        (fun ~depth _ctx _csts s t -> Elpi.Builtin.bool.readback ~depth s t)
    }

  let float : (float, 'ctx, 'csts) ContextualConversion.t =
    { ContextualConversion.ty = BuiltInData.float.ty
    ; pp_doc = BuiltInData.float.pp_doc
    ; pp = BuiltInData.float.pp
    ; embed = (fun ~depth _ctx _csts s x -> BuiltInData.float.embed ~depth s x)
    ; readback =
        (fun ~depth _ctx _csts s t -> BuiltInData.float.readback ~depth s t)
    }

  let string : (string, 'ctx, 'csts) ContextualConversion.t =
    { ContextualConversion.ty = BuiltInData.string.ty
    ; pp_doc = BuiltInData.string.pp_doc
    ; pp = BuiltInData.string.pp
    ; embed = (fun ~depth _ctx _csts s x -> BuiltInData.string.embed ~depth s x)
    ; readback =
        (fun ~depth _ctx _csts s t -> BuiltInData.string.readback ~depth s t)
    }

  (** List over a contextual element type. *)
  let list (elem : ('a, 'ctx, 'csts) ContextualConversion.t) :
      ('a list, 'ctx, 'csts) ContextualConversion.t =
    ContextualConversion.( !>> ) BuiltInData.list elem
end

(* ------------------------------------------------------------------ *)
(** {2 Contextual conversions for common types used in the PPX}

    Only [option] and [pair] exist: they delegate to [Elpi.Builtin] so the
    constructors are the ones Elpi's stdlib already knows about. Wider tuples
    would need fresh global constructors (the exact incompatibility this shim
    exists to avoid), so the PPX rejects them; use nested pairs or a record. *)

module PPX = struct
  (** option a *)
  let option (a : ('a, 'h, 'c) ContextualConversion.t) :
      ('a option, 'h, 'c) ContextualConversion.t =
    ContextualConversion.( !>> ) Elpi.Builtin.option a

  (** pair a b *)
  let pair (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t) :
      ('a * 'b, 'h, 'c) ContextualConversion.t =
    ContextualConversion.( !>>> ) Elpi.Builtin.pair a b
end

(* ------------------------------------------------------------------ *)
(** {2 Documentation helpers (drop-in for Elpi.API.PPX.Doc)} *)

module Doc = struct
  type prec_level =
    | Arrow
    | AppArg

  let rec show_ty_ast ?(prec = Arrow) =
    let open Conversion in
    function
    | TyName s -> s
    | TyApp ("->", a, [ b ]) -> (
      let inner =
        Printf.sprintf "%s -> %s"
          (show_ty_ast ~prec:AppArg a)
          (show_ty_ast ~prec:Arrow b)
      in
      match prec with
      | AppArg -> "(" ^ inner ^ ")"
      | Arrow -> inner)
    | TyApp (s, a, []) -> (
      let inner = Printf.sprintf "%s %s" s (show_ty_ast ~prec:AppArg a) in
      match prec with
      | AppArg -> "(" ^ inner ^ ")"
      | Arrow -> inner)
    | TyApp (s, a, rest) -> (
      let args =
        String.concat " " (List.map (show_ty_ast ~prec:AppArg) (a :: rest))
      in
      let inner = Printf.sprintf "%s %s" s args in
      match prec with
      | AppArg -> "(" ^ inner ^ ")"
      | Arrow -> inner)

  let kind fmt ty ~doc =
    Format.fprintf fmt "%% %s@\n" doc;
    Format.fprintf fmt "@[<hov2>kind %s@[<hov> type.@]@]@\n" (show_ty_ast ty)

  let constructor fmt ~name ~doc ~ty ~args =
    let sig_str =
      match args with
      | [] -> show_ty_ast ty
      | _ ->
        String.concat " -> " (List.map (show_ty_ast ~prec:AppArg) args)
        ^ " -> " ^ show_ty_ast ty
    in
    Format.fprintf fmt "@[<hov2>external symbol %s :@[<hov> %s.@]@]@\n%% %s@\n"
      name sig_str doc
end
