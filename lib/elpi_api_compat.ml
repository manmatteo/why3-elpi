(** Compatibility shim providing fork-specific Elpi API additions. Replaces the
    Gopiandcode/elpi fork's additions to ContextualConversion,
    BuiltInContextualData, Builtin.PPX, and PPX.Doc. *)

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

(** A fork-compatible ctx_readback type. The first parameter is the CONSTRUCTED
    context class type (not the raw input hyps type). The function receives raw
    [Data.hyps] and returns the constructed class. *)
type ('cls, 'csts) ctx_readback =
     depth:int
  -> Data.hyps
  -> 'csts
  -> Data.state
  -> Data.state * 'cls * 'csts * Conversion.extra_goals

(* ------------------------------------------------------------------ *)
(** {2 Contextual conversions for built-in types} *)

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

  let any : (Data.term, 'ctx, 'csts) ContextualConversion.t =
    { ContextualConversion.ty = BuiltInData.any.ty
    ; pp_doc = BuiltInData.any.pp_doc
    ; pp = BuiltInData.any.pp
    ; embed = (fun ~depth _ctx _csts s x -> BuiltInData.any.embed ~depth s x)
    ; readback =
        (fun ~depth _ctx _csts s t -> BuiltInData.any.readback ~depth s t)
    }

  (** De Bruijn constants used as "nominals" (bound variables). *)
  let nominal : (RawData.constant, 'ctx, 'csts) ContextualConversion.t =
    let ty = Conversion.TyName "nominal" in
    let embed ~depth:_ _ctx _csts s c = (s, RawData.mkBound c, []) in
    let readback ~depth _ctx _csts s t =
      match RawData.look ~depth t with
      | RawData.Const c when c >= 0 -> (s, c, [])
      | _ ->
        Utils.type_error
          (Format.asprintf "Not a nominal (bound variable): %a"
             (RawPp.term depth) t)
    in
    { ContextualConversion.ty
    ; pp_doc = (fun _ () -> ())
    ; pp = (fun fmt c -> Format.fprintf fmt "#%d" c)
    ; embed
    ; readback
    }

  (** List over a contextual element type. *)
  let list (elem : ('a, 'ctx, 'csts) ContextualConversion.t) :
      ('a list, 'ctx, 'csts) ContextualConversion.t =
    ContextualConversion.( !>> ) BuiltInData.list elem

  (** Placeholder polynomial type parameter (for generated code). *)
  let polyA0 = any
end

(* ------------------------------------------------------------------ *)
(** {2 Contextual conversions for common types used in the PPX} *)

module PPX = struct
  (** Char encoded as a single-character string. *)
  let char : (char, 'ctx, 'csts) ContextualConversion.t =
    let ty = Conversion.TyName "char" in
    let embed ~depth _ctx _csts s c =
      BuiltInData.string.embed ~depth s (String.make 1 c)
    in
    let readback ~depth _ctx _csts s t =
      let s, str, gls = BuiltInData.string.readback ~depth s t in
      if String.length str = 1 then (s, str.[0], gls)
      else Utils.type_error "expected a single-character string for char"
    in
    { ContextualConversion.ty
    ; pp_doc = (fun _ () -> ())
    ; pp = (fun fmt c -> Format.fprintf fmt "'%c'" c)
    ; embed
    ; readback
    }

  (* allocate_constructors declares global symbols and must run before
     Setup.init. We do this once at module load with ParamC placeholders.
     declare_allocated is pure, so we instantiate typed converters lazily
     without any runtime global declarations or identity hacks. *)

  let triple_decl (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t)
      (cc : ('cc, 'h, 'c) ContextualConversion.t) :
      ('a * 'b * 'cc, 'h, 'c) AlgebraicData.declaration =
    let open AlgebraicData in
    Decl
      { ty =
          Conversion.TyApp
            ( "triple"
            , a.ContextualConversion.ty
            , [ b.ContextualConversion.ty; cc.ContextualConversion.ty ] )
      ; doc = "Triples"
      ; pp =
          (fun fmt (x, y, z) ->
            Format.fprintf fmt "trpl(%a,%a,%a)" a.ContextualConversion.pp x
              b.ContextualConversion.pp y cc.ContextualConversion.pp z)
      ; constructors =
          [ K
              ( "trpl"
              , "trpl"
              , CA (a, CA (b, CA (cc, N)))
              , B (fun x y z -> (x, y, z))
              , M
                  (fun ~ok ~ko:_ -> function
                    | x, y, z -> ok x y z) )
          ]
      }

  let quadruple_decl (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t)
      (cc : ('cc, 'h, 'c) ContextualConversion.t)
      (d : ('d, 'h, 'c) ContextualConversion.t) :
      ('a * 'b * 'cc * 'd, 'h, 'c) AlgebraicData.declaration =
    let open AlgebraicData in
    Decl
      { ty =
          Conversion.TyApp
            ( "quadruple"
            , a.ContextualConversion.ty
            , [ b.ContextualConversion.ty
              ; cc.ContextualConversion.ty
              ; d.ContextualConversion.ty
              ] )
      ; doc = "Quadruples"
      ; pp =
          (fun fmt (x, y, z, w) ->
            Format.fprintf fmt "quadr(%a,%a,%a,%a)" a.ContextualConversion.pp x
              b.ContextualConversion.pp y cc.ContextualConversion.pp z
              d.ContextualConversion.pp w)
      ; constructors =
          [ K
              ( "quadr"
              , "quadr"
              , CA (a, CA (b, CA (cc, CA (d, N))))
              , B (fun x y z w -> (x, y, z, w))
              , M
                  (fun ~ok ~ko:_ -> function
                    | x, y, z, w -> ok x y z w) )
          ]
      }

  let quintuple_decl (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t)
      (cc : ('cc, 'h, 'c) ContextualConversion.t)
      (d : ('d, 'h, 'c) ContextualConversion.t)
      (e : ('e, 'h, 'c) ContextualConversion.t) :
      ('a * 'b * 'cc * 'd * 'e, 'h, 'c) AlgebraicData.declaration =
    let open AlgebraicData in
    Decl
      { ty =
          Conversion.TyApp
            ( "quintuple"
            , a.ContextualConversion.ty
            , [ b.ContextualConversion.ty
              ; cc.ContextualConversion.ty
              ; d.ContextualConversion.ty
              ; e.ContextualConversion.ty
              ] )
      ; doc = "Quintuples"
      ; pp =
          (fun fmt (x, y, z, w, v) ->
            Format.fprintf fmt "quint(%a,%a,%a,%a,%a)" a.ContextualConversion.pp
              x b.ContextualConversion.pp y cc.ContextualConversion.pp z
              d.ContextualConversion.pp w e.ContextualConversion.pp v)
      ; constructors =
          [ K
              ( "quint"
              , "quint"
              , CA (a, CA (b, CA (cc, CA (d, CA (e, N)))))
              , B (fun x y z w v -> (x, y, z, w, v))
              , M
                  (fun ~ok ~ko:_ -> function
                    | x, y, z, w, v -> ok x y z w v) )
          ]
      }

  let triple_alloc : AlgebraicData.allocation =
    AlgebraicData.allocate_constructors
      (AlgebraicData.ParamC
         (fun a ->
           AlgebraicData.ParamC
             (fun b -> AlgebraicData.ParamC (fun cc -> triple_decl a b cc))))

  let quadruple_alloc : AlgebraicData.allocation =
    AlgebraicData.allocate_constructors
      (AlgebraicData.ParamC
         (fun a ->
           AlgebraicData.ParamC
             (fun b ->
               AlgebraicData.ParamC
                 (fun cc ->
                   AlgebraicData.ParamC (fun d -> quadruple_decl a b cc d)))))

  let quintuple_alloc : AlgebraicData.allocation =
    AlgebraicData.allocate_constructors
      (AlgebraicData.ParamC
         (fun a ->
           AlgebraicData.ParamC
             (fun b ->
               AlgebraicData.ParamC
                 (fun cc ->
                   AlgebraicData.ParamC
                     (fun d ->
                       AlgebraicData.ParamC (fun e -> quintuple_decl a b cc d e))))))

  (** option a *)
  let option (a : ('a, 'h, 'c) ContextualConversion.t) :
      ('a option, 'h, 'c) ContextualConversion.t =
    ContextualConversion.( !>> ) Elpi.Builtin.option a

  (** pair a b *)
  let pair (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t) :
      ('a * 'b, 'h, 'c) ContextualConversion.t =
    ContextualConversion.( !>>> ) Elpi.Builtin.pair a b

  (** triple a b cc *)
  let triple (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t)
      (cc : ('cc, 'h, 'c) ContextualConversion.t) :
      ('a * 'b * 'cc, 'h, 'c) ContextualConversion.t =
    AlgebraicData.declare_allocated triple_alloc (triple_decl a b cc)

  let quadruple (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t)
      (cc : ('cc, 'h, 'c) ContextualConversion.t)
      (d : ('d, 'h, 'c) ContextualConversion.t) :
      ('a * 'b * 'cc * 'd, 'h, 'c) ContextualConversion.t =
    AlgebraicData.declare_allocated quadruple_alloc (quadruple_decl a b cc d)

  let quintuple (a : ('a, 'h, 'c) ContextualConversion.t)
      (b : ('b, 'h, 'c) ContextualConversion.t)
      (cc : ('cc, 'h, 'c) ContextualConversion.t)
      (d : ('d, 'h, 'c) ContextualConversion.t)
      (e : ('e, 'h, 'c) ContextualConversion.t) :
      ('a * 'b * 'cc * 'd * 'e, 'h, 'c) ContextualConversion.t =
    AlgebraicData.declare_allocated quintuple_alloc (quintuple_decl a b cc d e)
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

  let adt ~doc ~ty ~args fmt () =
    Format.fprintf fmt "%% %s@\n" doc;
    List.iter
      (fun (name, adoc, arg_tys) ->
        let sig_str =
          match arg_tys with
          | [] -> show_ty_ast ty
          | _ ->
            String.concat " -> " (List.map (show_ty_ast ~prec:AppArg) arg_tys)
            ^ " -> " ^ show_ty_ast ty
        in
        Format.fprintf fmt
          "@[<hov2>external symbol %s :@[<hov> %s.@]@]@\n%% %s@\n" name sig_str
          adoc)
      args
end
