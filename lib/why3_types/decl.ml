open Term
open Ty
open Common
open Why3
open Why3.Decl

include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : prsymbol) -> ()
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_prsymbol = "prsymbol"
    let _ = elpi_constant_type_prsymbol
    let elpi_constant_type_prsymbolc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_prsymbol
    let _ = elpi_constant_type_prsymbolc
    let elpi_opaque_data_decl_prsymbol =
      Elpi.API.OpaqueData.declare
        {
          Elpi.API.OpaqueData.name = "prsymbol";
          doc = "Names for declarations";
          pp = Pretty.print_pr;
          compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    let _ = elpi_opaque_data_decl_prsymbol
    module Ctx_for_prsymbol =
      struct
        class type t = object inherit Elpi_api_compat.ctx end
      end
    let prsymbol :
      'c .
        (prsymbol, 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_prsymbol in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = prsymbol
    let elpi_embed_prsymbol = prsymbol.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_prsymbol
    let elpi_readback_prsymbol =
      prsymbol.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_prsymbol
    let elpi_prsymbol = Elpi.API.BuiltIn.MLDataC prsymbol
    let _ = elpi_prsymbol
    class ctx_for_prsymbol (h : Elpi.API.Data.hyps)
      (s : Elpi.API.Data.state) : Ctx_for_prsymbol.t =
      object (_) inherit  ((Elpi_api_compat.ctx) h) end
    let (in_ctx_for_prsymbol :
      (Ctx_for_prsymbol.t, 'csts) Elpi_api_compat.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_prsymbol) h s), c, (List.concat []))
    let _ = in_ctx_for_prsymbol
    let () = declaration := ((!declaration) @ [elpi_prsymbol])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let logicdeclc = Elpi.API.RawData.Constants.declare_global_symbol "logic"
let embed_logic_decl : (logic_decl, 'a, 'b) Elpi.API.ContextualConversion.embedding = fun ~depth hyps constraints st (ls,def) ->
  let open Elpi.API.RawData in
  let st, ax, eg1 = term.embed ~depth hyps constraints st (Decl.ls_defn_axiom def) in
  let st, ls, eg2 = lsymbol.embed ~depth hyps constraints st ls in
  st, mkApp logicdeclc ls [ax], eg1@eg2
let readback_logic_decl : (logic_decl, 'a,'b) Elpi.API.ContextualConversion.readback = fun ~depth hyps constraints st tm ->
  let unsupported msg =
    Loc.errorm "Readback not supported for logic decl: %s@." msg
  in
  let open Elpi.API.RawData in
  let open Why3.Decl in
  match look ~depth tm with
  | App (c, ls, [ax]) when c = logicdeclc ->
    let st, _ls, eg1 = lsymbol.readback ~depth hyps constraints st ls in (* Lsymbol is not needed for now as it is read back from axiom *)
    let st, ax, eg2 = term.readback ~depth hyps constraints st ax in
    (match (ls_defn_of_axiom ax) with
    | Some ax -> st, ax, eg1@eg2
    | None -> unsupported (Format.asprintf "Couldn't read back logic declaration from axiom %a" Pretty.print_term ax))
  | _ -> unsupported "invalid"
let logic_decl : (logic_decl, 'c, 'csts) Elpi.API.ContextualConversion.t =
  let pp_doc = (fun fmt () -> Format.fprintf fmt "type logic  lsymbol  -> term -> logic_decl.") in
  let pp = Pretty.print_logic_decl in
  { Elpi.API.ContextualConversion.embed = embed_logic_decl; Elpi.API.ContextualConversion.readback = readback_logic_decl; ty = Elpi.API.Conversion.TyName "logic_decl"; pp_doc; pp }

let () = declaration := ((!declaration) @ [Elpi.API.BuiltIn.MLDataC logic_decl])

include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : data_decl) -> ()
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_data_decl = "data-decl"
    let _ = elpi_constant_type_data_decl
    let elpi_constant_type_data_declc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_data_decl
    let _ = elpi_constant_type_data_declc
    let elpi_opaque_data_decl_data_decl =
      Elpi.API.OpaqueData.declare
        {
          name = "data_decl";
          pp =
            (pp_why_data
               (fun fmt ->
                  fun (x, _) -> Format.fprintf fmt "%a" Pretty.print_ts x));
          doc = "";
          compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    let _ = elpi_opaque_data_decl_data_decl
    module Ctx_for_data_decl =
      struct
        class type t = object inherit Elpi_api_compat.ctx end
      end
    let data_decl :
      'c .
        (data_decl, 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_data_decl in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = data_decl
    let elpi_embed_data_decl = data_decl.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_data_decl
    let elpi_readback_data_decl =
      data_decl.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_data_decl
    let elpi_data_decl = Elpi.API.BuiltIn.MLDataC data_decl
    let _ = elpi_data_decl
    class ctx_for_data_decl (h : Elpi.API.Data.hyps)
      (s : Elpi.API.Data.state) : Ctx_for_data_decl.t =
      object (_) inherit  ((Elpi_api_compat.ctx) h) end
    let (in_ctx_for_data_decl :
      (Ctx_for_data_decl.t, 'csts) Elpi_api_compat.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_data_decl) h s), c, (List.concat []))
    let _ = in_ctx_for_data_decl
    let () = declaration := ((!declaration) @ [elpi_data_decl])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let plemmac = Elpi.API.RawData.Constants.declare_global_symbol "lemma"
let paxiomc = Elpi.API.RawData.Constants.declare_global_symbol "axiom"
let pgoalc = Elpi.API.RawData.Constants.declare_global_symbol "goal"
let paramc = Elpi.API.RawData.Constants.declare_global_symbol "const"
let tydeclc = Elpi.API.RawData.Constants.declare_global_symbol "typ" (* Abstract type*)
let datac = Elpi.API.RawData.Constants.declare_global_symbol "data"  (* Data (defined) type*)
let decllc = Elpi.API.RawData.Constants.declare_global_symbol "declls"

let embed_decl : (Decl.decl, 'a, 'b) Elpi.API.ContextualConversion.embedding = fun ~depth h c st decl ->
  let unsupported msg =
  Loc.errorm "Embed not supported for decl :(%s, %a)@." msg Pretty.print_decl decl
  in
  let open Elpi.API.RawData in
  let open Decl in
  let open Elpi.API.ContextualConversion in (* Better casts are available in elpi API but not in this branch *)
  let _dtag = decl.d_tag in     (* TODO *)
  let _dnews = decl.d_news in   (* TODO! Provides set of idents introduced by this declaration *) (*   Format.printf "The idents introduced in decl: %s@." (Ident.Sid.fold (fun id str -> id.id_string ^ "," ^ str) _dnews ""); *)
  match decl.d_node with
  | Decl.Dtype ty -> let st, tsymb, eg = tysymbol.embed ~depth h c st ty in
    st, mkApp tydeclc tsymb [], eg
  | Decl.Ddata ddecls -> (* Algebraic data *)
    let st, ddecls, eg = (Elpi_api_compat.BuiltInContextualData.list data_decl).embed ~depth h c st ddecls
    in st, mkApp datac ddecls [], eg
  | Decl.Dparam p ->
    let st, lsymb, eg = lsymbol.embed ~depth h c st p
    in st, mkApp paramc lsymb [], eg
  | Decl.Dlogic ll -> (* Logic declarations *)
    let st, ll, eg = (Elpi_api_compat.BuiltInContextualData.list logic_decl).embed ~depth h c st ll
    in st, mkApp decllc ll [], eg
  | Decl.Dprop (k,s,t) -> (*let st, prdecl, eg = prop_decl.embed ~depth h c st (k,s,t) in st, *)
    let st, prsym, eg1 = prsymbol.embed ~depth h c st s in
    (* let st, tt, eg2 = term.embed ~depth h c st t in *)
    let st, tt, eg2 = term.embed ~depth h c st t in
    let konst = (match k with | Plemma -> plemmac | Paxiom -> paxiomc | Pgoal  -> pgoalc)
    in st, mkApp konst prsym [tt], eg1@eg2
  | Decl.Dind _ -> unsupported "dind"

let readback_decl : (Decl.decl, 'a, 'b) Elpi.API.ContextualConversion.readback = fun ~depth h c st decl ->
  let open Elpi.API.ContextualConversion in
  let unsupported msg =
  Loc.errorm "Readback not supported for decl: (%s, %a)@." msg (Elpi.API.RawPp.term depth) decl
  in
  let create_prop_decl k symt t =
    let st, prs, eg1 = prsymbol.readback ~depth h c st symt in
    let st, tt, eg2  = term.readback ~depth h c st t in
    st, Decl.create_prop_decl k prs tt, eg1 @ eg2
  in
  let open Elpi.API.RawData in
  match look ~depth decl with
  | Const _ -> unsupported "const"
  | Lam _ -> unsupported "lam"
  | App (c, symt, [t]) when c = plemmac -> create_prop_decl Decl.Plemma symt t
  | App (c, symt, [t]) when c = paxiomc -> create_prop_decl Decl.Paxiom symt t
  | App (c, symt, [t]) when c = pgoalc ->  create_prop_decl Decl.Pgoal  symt t
  | App (c, symt, []) when  c = paramc ->
    let st, ls, eg   = lsymbol.readback ~depth h c st symt in
(*     if Term.ls_equal ls Term.ps_equ then
      st, Decl.create_prop_decl Decl.Paxiom (Decl.create_prsymbol (Ident.id_fresh "a")) Term.t_true, eg
    else *)
    st, Decl.create_param_decl ls, eg
  | App (c, tysymt, []) when c = tydeclc ->
    let st, ts, eg = tysymbol.readback ~depth h c st tysymt in
    st, Decl.create_ty_decl ts, eg
  | App (c, dlist, []) when c = datac -> (* Algebraic data *)
    let st, dlist, eg = (Elpi_api_compat.BuiltInContextualData.list data_decl).readback ~depth h c st dlist in
    st, Decl.create_data_decl dlist, eg
  | App (c, llist, []) when c = decllc -> (* Defined predicate *)
    let st, dlist, eg = (Elpi_api_compat.BuiltInContextualData.list logic_decl).readback ~depth h c st llist in
    st, Decl.create_logic_decl dlist, eg
  | App (_, _, _) -> unsupported "app"
  | Cons (_, _) -> unsupported "cons"
  | Nil -> unsupported "nil"
  | Builtin (_, _) -> unsupported "builtin"
  | CData _ -> unsupported "cdata"
  | UnifVar (_, _) -> unsupported "unifvar"

let decl : (Decl.decl, 'a, 'b) Elpi.API.ContextualConversion.t = {
  ty = TyName "decl";
  pp = Pretty.print_decl;
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind decl type.
type goal   prsymbol -> term -> decl.
type lemma  prsymbol -> term -> decl.
type axiom  prsymbol -> term -> decl.
type typ    tysymbol -> decl. %% Abstract type
type data   list data_decl   -> decl. %% Data (defined) type
type declls list logic_decl  -> decl. %% Defined logic symbol
type const  lsymbol  -> decl.|});
  readback = readback_decl;
  embed = embed_decl;
}

let () = declaration := ((!declaration) @ [Elpi.API.BuiltIn.MLDataC decl])