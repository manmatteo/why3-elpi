let declaration = ref []
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
let pp_tctx _ _ = ()
type tctx =
  | Entry of ((string)[@elpi.key ]) [@@elpi.index (module String) "term"]
[@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tctx = "tctx"
    let elpi_constant_type_tctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tctx
    let elpi_constant_constructor_tctx_Entry = "entry"
    let elpi_constant_constructor_tctx_Entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tctx_Entry
    module Elpi_tctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tctx_state =
      Elpi.API.State.declare_component ~name:"tctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                           Elpi_tctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tctx
                                                             Elpi_api_compat.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_tctx_to_key ~depth:_  = function | Entry elpi__11 -> elpi__11
    let elpi_is_tctx elpi__h =
      let { Elpi.API.RawData.hdepth = elpi__depth; hsrc = elpi__x } =
        Elpi.API.RawData.of_hyp elpi__h in
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tctx_Entryc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non nominal")
          else None
      | _ -> None
    let elpi_push_tctx ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_tctx ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tctx_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_tctx =
      struct class type t = object inherit Elpi_api_compat.ctx end end
    let rec elpi_embed_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__6, Entry elpi__5) ->
                  let (elpi__state, elpi__9, elpi__7) =
                    Elpi_api_compat.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__6 in
                  let (elpi__state, elpi__10, elpi__8) =
                    (let elpi__embed =
                       Elpi_api_compat.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed in
                     fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi__embed ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__5 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppGlobalL
                       elpi_constant_constructor_tctx_Entryc
                       [elpi__9; elpi__10]),
                    (List.concat [elpi__7; elpi__8]))
    and elpi_readback_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tctx_Entryc ->
                    let (elpi__state, elpi__4, elpi__3) =
                      Elpi_api_compat.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__1::[] ->
                         let (elpi__state, elpi__1, elpi__2) =
                           (let elpi__readback =
                              Elpi_api_compat.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback in
                            fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t -> elpi__readback ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__1 in
                         (elpi__state, (elpi__4, (Entry elpi__1)),
                           (List.concat [elpi__3; elpi__2]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tctx_Entryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c as 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi_api_compat.Doc.kind fmt kind ~doc:"tctx";
               Elpi_api_compat.Doc.constructor fmt
                 ~ty:(Elpi.API.ContextualConversion.TyName "prop")
                 ~name:"entry" ~doc:"Entry"
                 ~args:[Elpi.API.ContextualConversion.TyName "term";
                       Elpi_api_compat.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tctx fmt x);
        embed = elpi_embed_tctx;
        readback = elpi_readback_tctx
      }
    let context_made_of_tctx =
      {
        Elpi_api_compat.is_entry_for_nominal = elpi_is_tctx;
        to_key = elpi_tctx_to_key;
        push = elpi_push_tctx;
        pop = elpi_pop_tctx;
        conv = tctx;
        init =
          (fun state ->
             Elpi.API.State.set elpi_tctx_state state
               ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                         Elpi_tctx_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : tctx
                                                           Elpi_api_compat.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tctx_state state))
      }
    let elpi_tctx = Elpi.API.BuiltIn.MLDataC tctx
    class ctx_for_tctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tctx.t = object (_) inherit  ((Elpi_api_compat.ctx) h) end
    let (in_ctx_for_tctx :
      (Ctx_for_tctx.t, 'csts) Elpi_api_compat.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_tctx) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_tctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var tctx]
  | App of term * term 
  | Lam of string * ((term)[@elpi.binder "term" tctx (fun s -> Entry s)]) 
[@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_term = "term"
    let elpi_constant_type_termc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_term
    let elpi_constant_constructor_term_Var = "var"
    let elpi_constant_constructor_term_Varc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Var
    let elpi_constant_constructor_term_App = "app"
    let elpi_constant_constructor_term_Appc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_App
    let elpi_constant_constructor_term_Lam = "lam"
    let elpi_constant_constructor_term_Lamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Lam
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi_api_compat.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi_api_compat.ctx_field
          end
      end
    let rec elpi_embed_term :
      'c 'csts .
        (term, 'c as 'c, 'csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | Var elpi__22 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_tctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__22 in
                  (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | App (elpi__25, elpi__26) ->
                  let (elpi__state, elpi__29, elpi__27) =
                    (let elpi__embed = elpi_embed_term in
                     fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi__embed ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__25 in
                  let (elpi__state, elpi__30, elpi__28) =
                    (let elpi__embed = elpi_embed_term in
                     fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi__embed ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__26 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppGlobalL
                       elpi_constant_constructor_term_Appc
                       [elpi__29; elpi__30]),
                    (List.concat [elpi__27; elpi__28]))
              | Lam (elpi__31, elpi__32) ->
                  let (elpi__state, elpi__35, elpi__33) =
                    (let elpi__embed =
                       Elpi_api_compat.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed in
                     fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi__embed ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__31 in
                  let elpi__ctx_entry = (fun s -> Entry s) elpi__31 in
                  let elpi__ctx_key =
                    elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                  let elpi__ctx_entry =
                    {
                      Elpi_api_compat.entry = elpi__ctx_entry;
                      depth = elpi__depth
                    } in
                  let elpi__state =
                    elpi_push_tctx ~depth:elpi__depth elpi__state
                      elpi__ctx_key elpi__ctx_entry in
                  let (elpi__state, elpi__37, elpi__34) =
                    (let elpi__embed = elpi_embed_term in
                     fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi__embed ~depth h c s t)
                      ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                      elpi__state elpi__32 in
                  let elpi__36 = Elpi.API.RawData.mkLam elpi__37 in
                  let elpi__state =
                    elpi_pop_tctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppGlobalL
                       elpi_constant_constructor_term_Lamc
                       [elpi__35; elpi__36]),
                    (List.concat [elpi__33; elpi__34]))
    and elpi_readback_term :
      'c 'csts .
        (term, 'c as 'c, 'csts) Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
                    let (_, elpi__dbl2ctx) =
                      Elpi.API.State.get elpi_tctx_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf
                            "Readback of unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi_api_compat.pp_ctx_field pp_tctx)
                            elpi__dbl2ctx);
                     (let { Elpi_api_compat.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (Var
                           (elpi_tctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Appc ->
                    let (elpi__state, elpi__17, elpi__16) =
                      (let elpi__readback = elpi_readback_term in
                       fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi__readback ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__14::[] ->
                         let (elpi__state, elpi__14, elpi__15) =
                           (let elpi__readback = elpi_readback_term in
                            fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t -> elpi__readback ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__14 in
                         (elpi__state, (App (elpi__17, elpi__14)),
                           (List.concat [elpi__16; elpi__15]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Appc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Lamc ->
                    let (elpi__state, elpi__21, elpi__20) =
                      (let elpi__readback =
                         Elpi_api_compat.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback in
                       fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi__readback ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__18::[] ->
                         let elpi__ctx_entry = (fun s -> Entry s) elpi__21 in
                         let elpi__ctx_key =
                           elpi_tctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi_api_compat.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__18, elpi__19) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__18
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               (let elpi__readback = elpi_readback_term in
                                (fun ~depth ->
                                   fun h ->
                                     fun c ->
                                       fun s ->
                                         fun t ->
                                           elpi__readback ~depth h c s t))
                                 ~depth:(elpi__depth + 1) elpi__hyps
                                 elpi__constraints elpi__state elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (Lam (elpi__21, elpi__18)),
                           (List.concat [elpi__20; elpi__19]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Lamc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "term" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and term :
      'c 'csts . (term, 'c as 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "term" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi_api_compat.Doc.kind fmt kind ~doc:"term";
               Elpi_api_compat.Doc.constructor fmt ~ty:kind ~name:"app"
                 ~doc:"App"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_term;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_term];
               Elpi_api_compat.Doc.constructor fmt ~ty:kind ~name:"lam"
                 ~doc:"Lam"
                 ~args:[Elpi_api_compat.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->",
                           (Elpi.API.ContextualConversion.TyName "term"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_term])]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi_api_compat.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi_api_compat.get s
      end
    let (in_ctx_for_term :
      (Ctx_for_term.t, 'csts) Elpi_api_compat.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let (s, gls0) =
                Elpi_api_compat.readback_context context_made_of_tctx ~depth
                  h c s in
              (s, ((new ctx_for_term) h s), c, (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_term])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let builtin =
  let open Elpi.API.BuiltIn in
    Elpi.API.BuiltIn.declare ~file_name:(Sys.argv.(1)) (!declaration)
let main () = Elpi.API.BuiltIn.document_file builtin; exit 0
let () = main ()
