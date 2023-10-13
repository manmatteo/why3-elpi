open Why3
open Elpi
(* Constants for Why3 HOAS *)
let andc = Elpi.API.RawData.Constants.declare_global_symbol "and"
let orc = Elpi.API.RawData.Constants.declare_global_symbol "or"
let impc = Elpi.API.RawData.Constants.declare_global_symbol "imp"
let iffc = Elpi.API.RawData.Constants.declare_global_symbol "iff"
let allc = Elpi.API.RawData.Constants.declare_global_symbol "all"
let existsc = Elpi.API.RawData.Constants.declare_global_symbol "ex"
let applc = Elpi.API.RawData.Constants.declare_global_symbol "appl"
let notc = Elpi.API.RawData.Constants.declare_global_symbol "not"
let lsymbc = Elpi.API.RawData.Constants.declare_global_symbol "lsymb"
let strc = Elpi.API.RawData.Constants.declare_global_symbol "tstr"
let intc = Elpi.API.RawData.Constants.declare_global_symbol "tint"
let falsec = Elpi.API.RawData.Constants.declare_global_symbol "bot"
let truec = Elpi.API.RawData.Constants.declare_global_symbol "top"
let itec = Elpi.API.RawData.Constants.declare_global_symbol "ite"
let tvarc = Elpi.API.RawData.Constants.declare_global_symbol "tvar"
let tsymbc = Elpi.API.RawData.Constants.declare_global_symbol "tsymb"
let tappc = Elpi.API.RawData.Constants.declare_global_symbol "tapp"

let tyvsym : Ty.tvsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "tyvsymbol";
  doc = "Embedding of type variables";
  pp = (fun _ _ -> ());
  compare = Ty.tv_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}
let tysym : Ty.tysymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "tysymbol";
  doc = "Embedding of type symbols";
  pp = (fun fmt a -> Format.fprintf fmt "«%a»" Pretty.print_ts a);
  compare = Ty.ts_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [] (* Are these helpful? [("«ts_int»", Ty.ts_int ); ("«ts_real»", Ty.ts_real ); ("«ts_bool»", Ty.ts_bool ); ("«ts_str»", Ty.ts_str )] *);
}

let rec embed_ty : Why3.Ty.ty API.Conversion.embedding = fun ~depth st ty ->
  let open Elpi.API.RawData in
  match ty.ty_node with
  | Ty.Tyapp (h, []) ->
    let st, ts, eg = tysym.Elpi.API.Conversion.embed ~depth st h in
    st, mkApp tsymbc ts [], eg
  | Ty.Tyapp (h, l) ->
    let st, ts, egs = tysym.Elpi.API.Conversion.embed ~depth st h in
    let st, tl, egs = List.fold_right (fun arg (st, args, egs) ->
      let st, tt, eg = embed_ty ~depth st arg in 
      st, mkCons tt args, eg@egs
    ) l (st,mkNil,egs) in
    st, mkApp tappc ts [tl], egs
  | Ty.Tyvar v ->
    let st, vsymb, eg = tyvsym.embed ~depth st v in
    st, mkApp tvarc vsymb [], eg

(* This readback is defined in mutual recursion with the entire conversion *)
let rec readback_ty : Ty.ty API.Conversion.readback = fun ~depth st tm ->
  let unsupported msg =
  Loc.errorm "Readback not supported for type: (%s, %a)@." msg (Elpi.API.RawPp.term depth) tm
  in
  match (API.RawData.look ~depth tm) with
  | API.RawData.Const _ -> unsupported ""
  | API.RawData.App (c, ts, []) when c = tsymbc -> 
    let st, ts, eg = tysym.readback ~depth st ts in
    st, Ty.ty_app ts [], eg
  | API.RawData.App (c, ts, [tl]) when c = tappc  -> 
    let st, ts, eg1 = tysym.readback ~depth st ts in
    let st, args, eg2 = (API.BuiltInData.list ty).readback ~depth st tl in
    st, Ty.ty_app ts args, eg1@eg2
  | _ -> unsupported ""

(* Embedding of types *)
and ty : Ty.ty API.Conversion.t =
   {
  API.Conversion.ty = API.Conversion.TyName "ty";
  pp = Pretty.print_ty;
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|%% Embedding of types
kind ty type.
type tvar tyvsymbol -> ty.
type tapp tysymbol -> list ty -> ty.
type tsymb tysymbol -> ty.|});
  readback = readback_ty;
  embed = embed_ty;
}

let lsym : Term.lsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "lsymbol";
  doc = "Embedding of predicate symbols";
  pp = Pretty.print_ls;
  compare = Term.ls_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}
let vsym : Term.vsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "vsymbol";
  doc = "Embedding of variable symbols";
  pp = Pretty.print_vs;
  compare = Term.vs_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}


let embed_term : Term.term API.Conversion.embedding = fun ~depth st term ->
  let unsupported msg =
  Loc.errorm "Term not supported:(%s, %a)@." msg Pretty.print_term term
  in
  let open Elpi.API.RawData in
  let open Term in
  let rec aux ~depth st term (map : constant Mvs.t) =
  match term.t_node with
  | Term.Tvar v ->
    (try st, mkBound @@ Mvs.find v map, []
    with Not_found -> unsupported "unbound variable")
  | Term.Tconst c ->
    begin match c with
    (* TODO: We would prefer to use BigInt directly. to_int can raise overflow exceptions *)
    | Constant.ConstInt n -> let st, tm, eg = API.BuiltInData.int.embed ~depth st (BigInt.to_int n.il_int) in st, mkApp intc tm [], eg
    | Constant.ConstReal _ -> unsupported "real"
    | Constant.ConstStr s -> let st, tm, eg = API.BuiltInData.string.embed ~depth st s in st, mkApp strc tm [], eg
    end
  | Term.Tapp (ls, []) -> (* single constant *)
    let st, lsy, extra_goals = lsym.Elpi.API.Conversion.embed st ~depth ls in
    st, mkApp lsymbc lsy [], extra_goals
  | Term.Tapp (ls, args) -> (* constant with arguments *)
    let st, lsy, eg = lsym.Elpi.API.Conversion.embed st ~depth ls in
    let st, argslist, egs = List.fold_right (fun arg (st, args, egs) ->
      let st, tt, eg = aux ~depth st arg map in 
      st, tt::args, eg@egs
    ) args (st,[],eg) in
    let argslist = List.fold_right (fun arg acc ->
      mkCons arg acc) argslist mkNil in
    st, mkApp applc lsy [argslist], egs 
  | Term.Tlet (_, _)
  -> unsupported "let binder"
  | Term.Tcase (_, _)
  -> unsupported "case"
  | Term.Teps _ -> unsupported "epsilon/function"
  | Term.Tquant (q, tq) ->
    let (vlist,trigger,term) = Term.t_open_quant tq in
    begin match trigger with
    | (_::_) -> unsupported "Triggers not supported"
    | [] -> 
      (* Update the variable map (and depth) by adding each variable in the
         order in which it appears in the list of vsymbol (vlist) *)
      let map,depth =
        List.fold_right (fun var (map,depth) ->
          (Mvs.add var depth map, depth + 1) )
          vlist (map, depth) in
      (* The recursive call, with the updated map *)
      let embedded_body = (aux ~depth st term map) in
      (* Close all the newly created binders with the appropriate quantifer constant
         at the according type *)
      let build_binders quant =
        List.fold_right (fun var (st, tm, eg) ->
          let st, ty_term, eg1 = ty.embed ~depth st var.vs_ty in
          st, mkApp quant ty_term [mkLam tm], eg @ eg1)
          vlist embedded_body in
      begin match q with
      | Term.Tforall -> build_binders allc
      | Term.Texists -> build_binders existsc
      end
    end
  | Term.Tif (t1, t2, t3) ->
    let st, t1, eg1 = aux ~depth st t1 map in
    let st, t2, eg2 = aux ~depth st t2 map in
    let st, t3, eg3 = aux ~depth st t3 map in
    st, mkApp itec t1 [t2;t3], eg1@eg2@eg3
  | Term.Ttrue -> st, mkConst truec, []
  | Term.Tfalse -> st, mkConst falsec, []
  | Term.Tnot t ->
    let st, tm, eg = aux ~depth st t map in
    st, (mkApp notc tm []), eg
  | Term.Tbinop (op, t1, t2) ->
    let st, t1, eg1 = aux ~depth st t1 map in
    let st, t2, eg2 = aux ~depth st t2 map in
    let eg = eg1 @ eg2 in
  match op with
  | Term.Tand ->     st, (mkApp andc t1 [t2]), eg
  | Term.Tor ->      st, (mkApp orc  t1 [t2]), eg
  | Term.Timplies -> st, (mkApp impc t1 [t2]), eg
  | Term.Tiff ->     st, (mkApp iffc t1 [t2]), eg
  in aux ~depth st term Term.Mvs.empty

let rec readback_term : Term.term API.Conversion.readback = fun ~depth st tm ->
  let unsupported msg =
  Loc.errorm "Readback not supported for term: (%s, %a)@." msg (Elpi.API.RawPp.term depth) tm
  in
  let open API.RawData in
  (* The correspondence between De Brujin levels and Why3 variables during
     readback is stored in a Wstdlib.Mint map *)
  let open Wstdlib in
  let rec aux ~depth st tm (map : Term.vsymbol Mint.t) =
  (* Instrument a full conversion dependent on a variable map, so that it can be used
     to call a `list term` conversion in a recursive call *)
  let aux_conversion : Term.vsymbol Mint.t -> Term.term API.Conversion.t = fun m -> {
    API.Conversion.ty = API.Conversion.TyName "term";
    pp = Pretty.print_term; pp_doc = (fun _ () -> ()); embed = embed_term;
    readback = (fun ~depth st tm -> aux ~depth st tm m);
  }
  in
  let build_quantified_body ~depth st typ bo map quant_builder =
    let st, typ, eg1 = ty.readback ~depth st typ in
    let var = Term.create_vsymbol (Ident.id_fresh "x") typ in
    let map = Mint.add depth var map in
    let st, bo, eg2 = aux ~depth st bo map in
    (match bo.t_node with
    | Term.Tquant (_, tq) -> let (vlist,_,bo) = Term.t_open_quant tq in
      st, quant_builder (var::vlist) [] bo, eg1 @ eg2
    | _ -> st, quant_builder [var] [] bo, eg1 @ eg2)
  in
(*Mint.iter (fun k v -> Format.printf "%d -> %a@." k Pretty.print_vs v) map;
  Format.printf "term: %a@." (Elpi.API.RawPp.term depth) tm; *)
  match look ~depth tm with
  | Const c when c == truec -> st, Why3.Term.t_true, []
  | Const c when c == falsec -> st, Why3.Term.t_false, []
  | Const c when c == lsymbc -> unsupported "const"
  | Const c when c>=0 ->
    st, Why3.Term.t_var (Mint.find c map), []
  | Const _ -> unsupported "const"
  | Lam t ->
    let st, tt, eg = aux ~depth:(depth+1) st t map in
    st, tt, eg
  | App (c, t1, [t2]) when c = andc -> 
    let st, tt1, eg1 = aux ~depth st t1 map in
    let st, tt2, eg2 = aux ~depth st t2 map in
    st,  Why3.Term.t_and tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2]) when c = orc ->
    let st, tt1, eg1 = aux ~depth st t1 map in
    let st, tt2, eg2 = aux ~depth st t2 map in
    st,  Why3.Term.t_or tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2]) when c = impc ->
    let st, tt1, eg1 = aux ~depth st t1 map in
    let st, tt2, eg2 = aux ~depth st t2 map in
    st,  Why3.Term.t_implies tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2]) when c = iffc ->
    let st, tt1, eg1 = aux ~depth st t1 map in
    let st, tt2, eg2 = aux ~depth st t2 map in
    st,  Why3.Term.t_iff tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2;t3]) when c = itec ->
    let st, tt1, eg1 = aux ~depth st t1 map in
    let st, tt2, eg2 = aux ~depth st t2 map in
    let st, tt3, eg3 = aux ~depth st t3 map in
    st,  Why3.Term.t_if tt1 tt2 tt3, eg1 @ eg2 @ eg3
  | App (c, t1, []) when c = lsymbc -> (* To fix for firstorder? *)
    let st, ls, eg = lsym.readback ~depth st t1 in
    st, Why3.Term.t_app_infer ls [], eg
  | App (c, t1, []) when c = notc ->
    let st, t1, eg = aux ~depth st t1 map in
    st, Why3.Term.t_not t1, eg
  | App (c, t1, [tl]) when c = applc ->
    let st, t1, eg1 = lsym.readback ~depth st t1 in
    let st, tl, eg2 = (API.BuiltInData.list (aux_conversion map)).readback ~depth st tl in
    st, Why3.Term.t_app_infer t1 tl, eg1 @ eg2
  | App (c, typ, [bo]) when c = allc ->
    build_quantified_body ~depth st typ bo map Why3.Term.t_forall_close
  | App (c, typ, [bo]) when c = existsc ->
    build_quantified_body ~depth st typ bo map Why3.Term.t_exists_close
  | App (c, n, []) when c = intc -> (* Native integers *)
    let st, n, eg = API.BuiltInData.int.readback ~depth st n
    in st, Why3.Term.t_nat_const n, eg
  | App (c, _, _) ->
    unsupported (Format.asprintf "app %a" (Elpi.API.RawPp.term depth) (mkConst c))
  | Cons (_, _) -> unsupported "cons"
  | Nil -> unsupported "nil"
  | Builtin (_, _) -> unsupported "builtin"
  | CData _ -> unsupported "cdata"
  | UnifVar (_, _) -> unsupported "unifvar"
  in aux ~depth st tm Mint.empty

and term : Term.term API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "term";
  pp = Pretty.print_term;
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind term type.
type lsymb lsymbol -> term.
type tint int -> term.
type tstr string -> term.
type appl lsymbol -> list term -> term.
type and term -> term -> term.
type or  term -> term -> term.
type imp term -> term -> term.
type iff term -> term -> term.
type all ty -> (term -> term) -> term.
type ex  ty -> (term -> term) -> term.
type ite term -> term -> term -> term.
type not term -> term.
type top term.
type bot term.|});
  readback = readback_term;
  embed = embed_term;
}

let prsymbol : Decl.prsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "prsymbol";
  doc = "Names for declarations";
  pp = Pretty.print_pr;
  compare = compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

let defc = Elpi.API.RawData.Constants.declare_global_symbol "def"
let def2c = Elpi.API.RawData.Constants.declare_global_symbol "def2"

let embed_data_decl : Decl.data_decl API.Conversion.embedding = fun ~depth st ddecls ->
  let open Elpi.API.RawData in
  let (ty, kons) = ddecls in
  let st, tsymb, eg1 = tysym.embed ~depth st ty in
  let st, lkons, eg2 = (* Building a list of constructors for the given type *)
    List.fold_left (fun (st,t,eg) (ls, ll) ->
      let st, projlist, eg1 =
        List.fold_left (fun (st,ll,eg) maybe_ls -> (* Building a list of projection for the given symbol *)
          match maybe_ls with None -> st,ll,eg
          | Some s -> let a, b, c = lsym.embed ~depth st s in a, mkCons b ll, c@eg)
        (st, mkNil, []) ll
      in let st, lsymb, eg2 = lsym.embed ~depth st ls in
      let newdef = mkApp defc lsymb [projlist]
      in st, mkCons newdef t, eg@eg1@eg2)
    (st, mkNil, []) kons
  in let newtype = mkApp def2c tsymb [lkons]
  in st, newtype ,eg1@eg2
let readback_data_decl : Decl.data_decl API.Conversion.readback = fun ~depth st ddecls ->
  let unsupported msg =
  Loc.errorm "Data declaration is not well-formed: (%s, %a)@." msg (Elpi.API.RawPp.term depth) ddecls
  in
  let open Elpi.API.RawData in
  (match look ~depth ddecls with
  | App (h, tsymb, [lkons]) when h=def2c->
    let st, tsymb, eg = tysym.readback ~depth st tsymb in
    let lkons = API.Utils.lp_list_to_list ~depth lkons in
    let st, lkons, eg = List.fold_left (fun (st, cur, egs) kons ->
      match (look ~depth kons) with
      | App (h,lsymb,[projlist]) when h=defc -> 
        let st, lsymb, eg1 = lsym.readback ~depth st lsymb in
        let st, projlist, eg2 = (API.BuiltInData.list lsym).readback ~depth st projlist in
        st, (lsymb, projlist)::cur, eg1@eg2@egs
      | _ -> unsupported "")
    (st, [], eg) lkons
    in
    let lkons = (List.map (fun (ls,lk) -> ls, List.map (fun x -> Some x) lk) lkons) in
    st, (tsymb, lkons), eg
  | _ -> unsupported "")

let data_decl : Decl.data_decl API.Conversion.t = {
  pp = Pretty.print_data_decl;
  ty = API.Conversion.TyName "data_decl";
  pp_doc = (fun fmt () -> Format.fprintf fmt "");
  readback = readback_data_decl;
  embed = embed_data_decl;
}

(** Logic declarations are currently embedded by obtaining and reading back
their defining axiom. This isn't very robust and is subject to change.*)
let logicdeclc = Elpi.API.RawData.Constants.declare_global_symbol "logic"
let embed_logic_decl : Decl.logic_decl API.Conversion.embedding = fun ~depth st (ls,def) ->
  let open API.RawData in
(*   Format.printf "embedding %a in context %s@." Pretty.print_term tm (List.fold_left (fun a v -> a ^ (Format.asprintf "%a " Pretty.print_vs v)) "" vars); *)
  let st, ax, eg1 = embed_term ~depth st (Decl.ls_defn_axiom def) in
  let st, ls, eg2 = lsym.embed ~depth st ls in
  st, mkApp logicdeclc ls [ax], eg1@eg2
let readback_logic_decl : Decl.logic_decl API.Conversion.readback = fun ~depth st term ->
  let unsupported msg =
    Loc.errorm "Readback not supported for logic decl: %s@." msg
  in
  let open Elpi.API.RawData in
  let open Decl in
  match look ~depth term with
  | App (c, ls, [ax]) when c = logicdeclc ->
    let st, _ls, eg1 = lsym.readback ~depth st ls in (* Lsymbol is not needed for now as it is read back from axiom *)
    let st, ax, eg2 = readback_term ~depth st ax in
    (match (ls_defn_of_axiom ax) with
    | Some ax -> st, ax, eg1@eg2
    | None -> unsupported "Couldn't read back logic declaration from axiom")
  | _ -> unsupported "invalid"

let logic_decl : Decl.logic_decl API.Conversion.t = {
  pp = Pretty.print_logic_decl;
  ty = API.Conversion.TyName "logic_decl";
  pp_doc = (fun fmt () -> Format.fprintf fmt "type logic  lsymbol  -> term -> logic_decl.");
  readback = readback_logic_decl;
  embed = embed_logic_decl;
}

let plemmac = Elpi.API.RawData.Constants.declare_global_symbol "lemma"
let paxiomc = Elpi.API.RawData.Constants.declare_global_symbol "axiom"
let pgoalc = Elpi.API.RawData.Constants.declare_global_symbol "goal"
let paramc = Elpi.API.RawData.Constants.declare_global_symbol "param"
let tydeclc = Elpi.API.RawData.Constants.declare_global_symbol "tydecl"
let decllc = Elpi.API.RawData.Constants.declare_global_symbol "declls"
let datac = Elpi.API.RawData.Constants.declare_global_symbol "data"

let embed_decl : Decl.decl API.Conversion.embedding = fun ~depth st decl ->
  let unsupported msg =
  Loc.errorm "Embed not supported for decl :(%s, %a)@." msg Pretty.print_decl decl
  in
  let open Elpi.API.RawData in
  let open Decl in
  let _dtag = decl.d_tag in     (* TODO *)
  let _dnews = decl.d_news in   (* TODO! Important *) (*   Format.printf "The idents introduced in decl: %s@." (Ident.Sid.fold (fun id str -> id.id_string ^ "," ^ str) _dnews ""); *)
  match decl.d_node with
  | Decl.Dtype ty -> let st, tsymb, eg = tysym.embed ~depth st ty in
    st, mkApp tydeclc tsymb [], eg
  | Decl.Ddata ddecls -> (* Algebraic data *)
    let st, ddecls, eg = (API.BuiltInData.list data_decl).embed ~depth st ddecls
    in st, mkApp datac ddecls [], eg
  | Decl.Dparam p -> let st, lsymb, eg = lsym.embed ~depth st p in
    st, mkApp paramc lsymb [], eg
  | Decl.Dlogic ll -> (* Logic declarations *)
    let st, ll, eg = (API.BuiltInData.list logic_decl).embed ~depth st ll
    in st, mkApp decllc ll [], eg
  | Decl.Dprop (k,s,t) ->
    let st, prsym, eg1 = prsymbol.Elpi.API.Conversion.embed ~depth st s in
    let st, tt, eg2 = embed_term ~depth st t in
    let konst = (match k with | Plemma -> plemmac | Paxiom -> paxiomc | Pgoal  -> pgoalc)
    in st, mkApp konst prsym [tt], eg1@eg2
  | Decl.Dind _ -> unsupported "dind"

let readback_decl : Decl.decl API.Conversion.readback = fun ~depth st decl ->
  let unsupported msg =
  Loc.errorm "Readback not supported for decl: (%s, %a)@." msg (Elpi.API.RawPp.term depth) decl
  in
  let create_prop_decl k symt t =
    let st, prs, eg1 = prsymbol.readback ~depth st symt in
    let st, tt, eg2  = readback_term ~depth st t in
    st, Decl.create_prop_decl k prs tt, eg1 @ eg2
  in
  let open Elpi.API.RawData in
  match look ~depth decl with
  | Const _ -> unsupported "const"
  | Lam _ -> unsupported "lam"
  | App (c, symt, [t]) when c = plemmac -> create_prop_decl Decl.Plemma symt t
  | App (c, symt, [t]) when c = paxiomc -> create_prop_decl Decl.Paxiom symt t
  | App (c, symt, [t]) when c = pgoalc ->  create_prop_decl Decl.Pgoal symt t
  | App (c, symt, []) when  c = paramc ->
    let st, ls, eg = lsym.readback ~depth st symt in
    st, Decl.create_param_decl ls, eg
  | App (c, tysymt, []) when c = tydeclc ->
    let st, ts, eg = tysym.readback ~depth st tysymt in
    st, Decl.create_ty_decl ts, eg
  | App (c, dlist, []) when c = datac -> (* Algebraic data *)
    let st, dlist, eg = (API.BuiltInData.list data_decl).readback ~depth st dlist in
    st, Decl.create_data_decl dlist, eg
  | App (c, llist, []) when c = decllc -> (* Defined predicate *)
    let st, dlist, eg = (API.BuiltInData.list logic_decl).readback ~depth st llist in
    st, Decl.create_logic_decl dlist, eg
  | App (_, _, _) -> unsupported "app"
  | Cons (_, _) -> unsupported "cons"
  | Nil -> unsupported "nil"
  | Builtin (_, _) -> unsupported "builtin"
  | CData _ -> unsupported "cdata"
  | UnifVar (_, _) -> unsupported "unifvar"

let decl : Decl.decl API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "decl";
  pp = Pretty.print_decl;
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind decl type.
type goal   prsymbol -> term -> decl.
type lemma  prsymbol -> term -> decl.
type axiom  prsymbol -> term -> decl.
type tydecl tysymbol -> decl.
type data   list X   -> decl.
type declls list X   -> decl.
type param  lsymbol  -> decl.|});
  readback = readback_decl;
  embed = embed_decl;
}

(* Tasks are embedded as lists of declaration (there is more
   useful information but we ignore it for now)*)
let embed_task : Task.task API.Conversion.embedding =
  fun ~depth st task ->
  (API.BuiltInData.list decl).embed ~depth st (Task.task_decls task)

let readback_task : Task.task API.Conversion.readback =
  fun ~depth st term ->
    let st, decl_list, eg = (API.BuiltInData.list decl).readback ~depth st term in
    let task = List.fold_left Task.add_decl None decl_list in
    st, task, eg

let task : Task.task API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "list decl";
  pp = Pretty.print_task;
  pp_doc = (fun _fmt () -> ());
  readback = readback_task;
  embed = embed_task;
}

(* let lpq : Elpi.API.Quotation.quotation = fun ~depth st _loc text ->
  let open Parsing in
  let ast = Parser.Lp.parse_string "xxx" ("type " ^ text ^ ";") in
  match ast |> Stream.next |> fun x -> x.Common.Pos.elt with
  | Syntax.P_query { Common.Pos.elt = Syntax.P_query_infer(t,_); _ } ->
      (*Printf.eprintf "Q %s\n" text;*)
      let t, pats = !scope_ref t in
      let st, t, _ = embed_term ~pats ~depth st t in
      st, t
  | _ -> assert false

let () = Quotation.set_default_quotation lpq *)

let why3_builtin_declarations =
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInData in
  let open Elpi.API.BuiltInPredicate in
  let open Elpi.API.BuiltInPredicate.Notation in
  [
    MLCode
      (Pred ( "why3.term->string",
            In  (term, "T",
            Out (string, "S",
            Easy "Pretty print a term using the native pretty printer" )),
            fun t _ ~depth:_ -> !: (Format.asprintf "%a" Pretty.print_term t )),
        DocAbove );
    MLCode
      (Pred ( "why3.decl->string",
            In  (decl, "D",
            Out (string, "S",
            Easy "Pretty print a declaration using the native pretty printer" )),
            fun d _ ~depth:_ -> !: (Format.asprintf "%a" Pretty.print_decl d )),
        DocAbove );
    MLCode
      ( Pred ( "why3.create-prsymbol",
            In  (string, "S",
            Out (prsymbol, "P",
            Easy "Create a fresh prsymbol from a string" )),
            fun name _ ~depth:_ -> !: (Decl.create_prsymbol (Ident.id_fresh name))),
        DocAbove );
    MLCode
      ( Pred ( "why3.create-prop",
            In  (string,   "N",
            In  (list ty,  "TS",
            Out (lsym,       "N",
            Easy "Axiomatize a propositional symbol with name N and argument types TS" ))),
            fun name ts _ ~depth:_ -> !: (Term.create_lsymbol (Ident.id_fresh name) ts None)),
        DocAbove );
    MLCode
      ( Pred ( "why3.create-lsymb",
            In  (string,   "N",
            In  (list ty,  "TS",
            In  (ty,  "T",
            Out (lsym,       "N",
            Easy "Axiomatize a function symbol with name N, type T and argument types TS" )))),
            fun name ts t _ ~depth:_ -> !: (Term.create_lsymbol (Ident.id_fresh name) ts (Some t))),
        DocAbove );
    MLCode
      ( Pred ( "why3.var-type",
            In  (vsym, "V",
            Out (ty, "T",
            Easy "Get the type of a variable" )),
            fun var _ ~depth:_ -> !: (var.vs_ty)),
        DocAbove );
    MLCode
      ( Pred ( "why3.lsymb-type",
            In  (lsym, "L",
            Out (ty, "T",
            Easy "Get the type of a predicate symbol" )),
            fun s _ ~depth:_ -> !: (match s.ls_value with None -> Loc.errorm "No type for predicate symbol" | Some t -> t)),
        DocAbove );
    MLCode
      ( Pred ( "why3.lsymb-args-type",
            In  (lsym, "L",
            Out (list ty, "T",
            Easy "Get the list of the argument types of a predicate symbol" )),
            fun s _ ~depth:_ -> !: (s.ls_args)),
        DocAbove );
    MLCode
      ( Pred ( "why3.search-lsymb",
            In  (string, "S",
            In  (string, "T",
            Out (lsym, "L",
            Easy "Look up for theory T and for symbol S in T" ))),
            fun s t _ ~depth:_ -> !: (
              let config : Whyconf.config = Whyconf.init_config None in
              let main : Whyconf.main = Whyconf.get_main config in
              let env : Env.env = Env.create_env (Whyconf.loadpath main) in
              let theory = Env.read_theory env [] t in
              Theory.ns_find_ls theory.Theory.th_export [s])),
        DocAbove );
        
    MLData lsym;
    MLData vsym;
    MLData term;
    MLData ty;
    MLData tysym;
    MLData tyvsym;
    MLData prsymbol;
    MLData decl;
    LPCode {|type transform string -> list decl -> list decl -> prop.|}
    ]
 

let document () =
  let w3lp_builtins = API.BuiltIn.declare ~file_name:"w3lp.elpi" why3_builtin_declarations
  in let header = "%% API for manipulating Why3 terms and declaration via λProlog\n%% This file is automatically generated."
  in API.BuiltIn.document_file ~header w3lp_builtins