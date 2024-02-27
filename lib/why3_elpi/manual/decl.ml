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
let logic_decl : 'c .  (logic_decl, #Elpi.API.ContextualConversion.ctx as 'c, 'csts) Elpi.API.ContextualConversion.t =
  let pp_doc = (fun fmt () -> Format.fprintf fmt "type logic  lsymbol  -> term -> logic_decl.") in
  let pp = Pretty.print_logic_decl in
  { Elpi.API.ContextualConversion.embed = embed_logic_decl; Elpi.API.ContextualConversion.readback = readback_logic_decl; ty = Elpi.API.Conversion.TyName "logic_decl"; pp_doc; pp }

let plemmac = Elpi.API.RawData.Constants.declare_global_symbol "lemma"
let paxiomc = Elpi.API.RawData.Constants.declare_global_symbol "axiom"
let pgoalc = Elpi.API.RawData.Constants.declare_global_symbol "goal"
let paramc = Elpi.API.RawData.Constants.declare_global_symbol "const"
let tydeclc = Elpi.API.RawData.Constants.declare_global_symbol "typ" (* Abstract type*)
let datac = Elpi.API.RawData.Constants.declare_global_symbol "data"  (* Data (defined) type*)
let decllc = Elpi.API.RawData.Constants.declare_global_symbol "declls"

let embed_decl : (Decl.decl, 'a, 'b) API.ContextualConversion.embedding = fun ~depth h c st decl ->
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
    let st, ddecls, eg = (API.BuiltInData.list !< data_decl).embed ~depth st ddecls
    in st, mkApp datac ddecls [], eg
  | Decl.Dparam p ->
    let st, lsymb, eg = lsymbol.embed ~depth h c st p
    in st, mkApp paramc lsymb [], eg
  | Decl.Dlogic ll -> (* Logic declarations *)
    let st, ll, eg = (API.BuiltInData.list !< logic_decl).embed ~depth st ll
    in st, mkApp decllc ll [], eg
  | Decl.Dprop (k,s,t) ->
    let st, prsym, eg1 = prsymbol.embed ~depth h c st s in
    let st, tt, eg2 = term.embed ~depth h c st t in
    let konst = (match k with | Plemma -> plemmac | Paxiom -> paxiomc | Pgoal  -> pgoalc)
    in st, mkApp konst prsym [tt], eg1@eg2
  | Decl.Dind _ -> unsupported "dind"

let readback_decl : (Decl.decl, 'a, 'b) API.ContextualConversion.readback = fun ~depth h c st decl ->
  let open API.ContextualConversion in
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
    let st, dlist, eg = (API.BuiltInData.list !< data_decl).readback ~depth st dlist in
    st, Decl.create_data_decl dlist, eg
  | App (c, llist, []) when c = decllc -> (* Defined predicate *)
    let st, dlist, eg = (API.BuiltInData.list !< logic_decl).readback ~depth st llist in
    st, Decl.create_logic_decl dlist, eg
  | App (_, _, _) -> unsupported "app"
  | Cons (_, _) -> unsupported "cons"
  | Nil -> unsupported "nil"
  | Builtin (_, _) -> unsupported "builtin"
  | CData _ -> unsupported "cdata"
  | UnifVar (_, _) -> unsupported "unifvar"

let decl : (Decl.decl, 'a, 'b) API.ContextualConversion.t = {
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