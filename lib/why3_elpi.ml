open Why3
open Elpi

(* A state component linking Why3 variable symbols and ELPI bound variables *)
let descriptor = Elpi.API.State.new_state_descriptor ()
let varmap : (int Term.Mvs.t) API.State.component =
  API.State.declare_component ~descriptor
    ~name:"varmap"
    ~init:(fun _ -> Term.Mvs.empty)
    ~pp:(fun fmt m -> Term.Mvs.iter (fun k e -> Format.fprintf fmt "(%a,%d);" Pretty.print_vs k e) m)
    ~start:(fun x -> x) ()
let mapvar : (Term.vsymbol API.RawData.Constants.Map.t) API.State.component =
  API.State.declare_component ~descriptor
    ~name:"mapvar"
    ~init:(fun _ -> API.RawData.Constants.Map.empty)
    ~pp:(fun fmt m -> API.RawData.Constants.Map.iter (fun k e -> Format.fprintf fmt "(%d,%a);" k Pretty.print_vs e) m)
    ~start:(fun x -> x) ()

(* Constants for Why3 HOAS *)
let epsc = Elpi.API.RawData.Constants.declare_global_symbol "eps"
let letc = Elpi.API.RawData.Constants.declare_global_symbol "let"
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
let matchc = Elpi.API.RawData.Constants.declare_global_symbol "match"
let branchc = Elpi.API.RawData.Constants.declare_global_symbol "branch"

(* Printer for Ident-like Why3 builtins: ident, variables...
   These are mostly a layer over Ident, and can be seen as names *)
let pp_why_ident p = fun fmt x -> Format.fprintf fmt "`%a`" p x 
(* Printer for Why3 names that include more content: logic symbols, data
   types...  This content (typing for lsymbols, constructors for data types...)
   is accessed via builtin predicates  *)
let pp_why_data p = fun fmt x -> Format.fprintf fmt "«%a»" p x 

let ident : Ident.ident Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  name = "ident";
  doc = "Why3 identifiers. Can be inspected or built via builtin predicates, for example for accessing their attributes.";
  pp = pp_why_ident (fun fmt x -> Format.fprintf fmt "%s" x.Ident.id_string);
  compare = Ident.id_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}
(* Unused for now *)
(*
let attribute : Ident.attribute Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  name = "ident";
  doc = "Attributes of Why3 identifiers. Can be created with builtin predicates. Only manually exported attributes are known to the API.";
  pp = (fun fmt x -> Format.fprintf fmt "`%s`" x.Ident.attr_string);
  compare = Ident.attr_compare;
  hash = Ident.attr_hash;
  hconsed = false;
  constants = [];
} *)

let env : Env.env Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  name = "env";
  doc = "The current environment can be retrieved, for example during a transformation with why3.get-env";
  pp = (fun fmt _ -> Format.fprintf fmt "env");
  compare = (fun _ _ -> 0); (* envs are all the same! *)
  hash = (fun e -> Weakhtbl.tag_hash (Env.env_tag e));
  hconsed = false;
  constants = [];
}
let tyvsym : Ty.tvsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  name = "tv";
  doc = "Variables in polymorphic types.";
  pp = pp_why_ident Pretty.print_tv;
  compare = Ty.tv_compare;
  hash = Ty.tv_hash;
  hconsed = false;
  constants = [];
}
let tysym : Ty.tysymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  name = "tysymbol";
  doc = "Embedding of type symbols. Internal information (Ident, arguments) is not exposed.";
  pp = pp_why_data Pretty.print_ts;
  compare = Ty.ts_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [] (* Are these helpful? [("arr", Ty.ts_func); ("«ts_int»", Ty.ts_int ); ("«ts_real»", Ty.ts_real ); ("«ts_bool»", Ty.ts_bool ); ("«ts_str»", Ty.ts_str )] *);
}

let ty : (Ty.ty, 'a, 'b) API.ContextualConversion.t =
  let open API.BuiltInData in
  let open API.ContextualConversion in
  API.AlgebraicData.declare {
  ty = TyName "ty";
  doc = "Embedding of types";
  pp = Pretty.print_ty;
  constructors = [
   K("tvar","Type variable",
     A (tyvsym,N),
     B Ty.ty_var,
     M (fun ~ok ~ko ty ->
       (match ty.ty_node with | Ty.Tyvar v -> ok v | _ -> ko ())));
   K("tapp","",
     A (tysym,C((fun x -> (!>) (list (!< x))) , N)),
     B Ty.ty_app,
     M (fun ~ok ~ko ty ->
       (match ty.ty_node with | Ty.Tyapp (t, u) -> ok t u | _ -> ko ())));
  ]
}

(** Embedding of lsymbols. Note: we are using OpaqueData, so argument and value
    types are not exposed to the API. They can be inspected or manipulated by
    using navite predicates. *)
let lsym : Term.lsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "lsymbol";
  doc = "Embedding of predicate symbols. Name, argument and value type can be accessed via native predicates.";
  pp = pp_why_data Pretty.print_ls;
  compare = Term.ls_compare;
  hash = Term.ls_hash;
  hconsed = false;
  constants = [];
}

(** As before, we embed variable symbols as an OpaqueData so their type can only
    be inspected or manipulated via native predicates. *)
let vsym : Term.vsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "var"; doc = "Embedding of variable symbols"; pp = pp_why_ident Pretty.print_vs;
  compare = Term.vs_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

let pwildc = Elpi.API.RawData.Constants.declare_global_symbol "pwild"
let pappc = Elpi.API.RawData.Constants.declare_global_symbol "papp"
let pasc = Elpi.API.RawData.Constants.declare_global_symbol "pas"
let pvarc = Elpi.API.RawData.Constants.declare_global_symbol "pvar"
let porc = Elpi.API.RawData.Constants.declare_global_symbol "por"
let pabsc = Elpi.API.RawData.Constants.declare_global_symbol "pabs"
let rec embed_pattern = fun ~depth st pat ->
  (* let unsupported msg = Loc.errorm "Pattern not supported: (%s)@." msg in *)
  let open Elpi.API.RawData in
  let open Term in
  match pat.pat_node with
  | Term.Pvar vr ->
    API.State.update varmap st (Mvs.add vr depth), (* state *)
    mkApp pvarc (mkBound depth) [], (* term *)
    [] (* extra goals *)
  | Term.Pwild ->
    let st, typ, eg = ty.embed () () ~depth st pat.pat_ty in
    st, mkApp pwildc typ [], eg
  | Term.Papp (ls, pl) ->
    let st, lsy, eg1 = lsym.Elpi.API.Conversion.embed st ~depth ls in
    let st, typ, eg2 = ty.embed () () ~depth st pat.pat_ty in
    let st, pl, egs, _nbindings =
      List.fold_right (fun pat (st, pl, egs,n) ->
      (* let curmap = API.State.get varmap st in *)
      (* Format.printf "depth is now %d, maxvalue is %d, numvalue is %d@." depth (List.fold_left max 0 (Mvs.values curmap)) (Mvs.cardinal curmap); *)
      (* (Term.Mvs.iter (fun vs bind -> Format.printf "%a bound to %d@." Pretty.print_vs vs bind) curmap); *)
      (* let depth = max depth (1 + List.fold_left max 0 (Mvs.values (API.State.get varmap st))) in *)
      (* Format.printf "depth is now %d, maxvalue is %d, numvalue is %d@." depth (List.fold_left max 0 (Mvs.values curmap)) (Mvs.cardinal curmap); *)
      let st, tt, eg = embed_pattern ~depth:(depth+n) st pat in
      st, mkCons tt pl, eg@egs,n+1
    ) pl (st,mkNil,[],0) in
    st, mkApp pappc lsy [pl;typ], eg1@eg2@egs
  | Term.Pas (pat, vs) ->
    let st = API.State.update varmap st (Mvs.add vs depth) in
    let st, vs, eg2 = vsym.Elpi.API.Conversion.embed ~depth st vs in
    let st, pat, eg1 = embed_pattern ~depth:(depth+1) st pat in
    st, mkApp pasc pat [vs], eg1@eg2
  | Term.Por (pat1, pat2) ->
    let st, pat1, eg1 = embed_pattern ~depth st pat1 in
    let st, pat2, eg2 = embed_pattern ~depth st pat2 in
    st, mkApp porc pat1 [pat2], eg1@eg2

and readback_pattern = fun ~depth st pat ->
  let unsupported msg =
  Loc.errorm "Readback not supported for pattern: (%s, %a)@." msg (Elpi.API.RawPp.term depth) pat
  in
  let open Elpi.API.RawData in
  let open Term in
  match look ~depth pat with
  | App (c, typ, [])   when c = pwildc ->
    let st, typ, eg = ty.readback ~depth () () st typ in
    st, pat_wild typ, eg
  | App (c, ls, [pl;typ]) when c = pappc  ->
    let st, ls, eg1 = lsym.readback ~depth st ls in
    let st, pl, eg2 = (API.BuiltInData.list pattern).readback ~depth st pl in
    let st, typ, eg3 = ty.readback ~depth () () st typ in
    st, pat_app ls pl typ, eg1@eg2@eg3
  | App (c, pat, [vs]) when c = pasc ->
    let st, pat, eg1 = readback_pattern ~depth st pat in
    let st, vs, eg2 = vsym.readback ~depth st vs in
    st, pat_as pat vs, eg1@eg2
  | App (c, vs, []) when c = pvarc ->
    let vname = (match (look ~depth vs) with | Const v -> v | _ -> unsupported "") in
    let vs =
      try API.RawData.Constants.Map.find vname (API.State.get mapvar st)
    with Not_found -> unsupported "Can;t find corresponding vsymbol"
    in
    st, pat_var vs, []
  | App (c, pat1, [pat2]) when c = porc ->
    let st, pat1, eg1 = readback_pattern ~depth st pat1 in
    let st, pat2, eg2 = readback_pattern ~depth st pat2 in
    st, pat_or pat1 pat2, eg1@eg2
  | _ -> unsupported ""

and pattern : Term.pattern API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "pattern";
  pp = (fun _ _ -> ());
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind pattern type.
type pwild ty -> pattern.
type papp lsymbol -> list pattern -> ty -> pattern. 
type pas pattern -> var -> pattern.
type pvar term -> pattern.
type por pattern -> pattern -> pattern.
type pabs var -> (term -> term_branch) -> term_branch.
|});
  readback = readback_pattern;
  embed = embed_pattern;
}

let rec embed_term : Term.term API.Conversion.embedding = fun ~depth st term ->
  let unsupported msg =
  Loc.errorm "Term embedding not supported:@.(%s,@. %a)@." msg Pretty.print_term term in
  let open Elpi.API.RawData in
  let open Term in
  let build_binders depth binder vlist embedded_body =
    List.fold_right (fun var (st, tm, eg) ->
      let st, ty_term, eg1 = ty.embed () () ~depth st var.vs_ty in
      let st, vname, eg2 = vsym.embed ~depth st var in
      st, mkApp binder vname [ty_term; mkLam tm], eg @ eg1 @ eg2)
      vlist embedded_body
  in
  match term.t_node with
  | Term.Tvar v ->
    (try API.State.get varmap st |> Mvs.find v |> fun i -> st, mkBound i, []
    with Not_found -> unsupported (Format.asprintf "unbound variable %a" Pretty.print_vs v))
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
      let st, tt, eg = embed_term ~depth st arg in
      st, mkCons tt args, eg@egs
    ) args (st,mkNil,eg) in
    st, mkApp applc lsy [argslist], egs 
  | Term.Tlet (t, tbound) -> 
    let st, t, eg1 = embed_term ~depth st t in (* the term we are naming *)
    let var, topen = Term.t_open_bound tbound in (* the bound variable and the term where it is bound *)
    let st, ty_term, eg2 = ty.embed () () ~depth st var.vs_ty in (* embed vname and its type *)
    let st, vname, eg3 = vsym.embed ~depth st var in
    let st = API.State.update varmap st (Mvs.add var depth) in
    let st, topen, eg4 = embed_term ~depth:(depth + 1) st topen in
    st, mkApp letc vname [ty_term; t; mkLam topen], eg1 @ eg2 @ eg3 @ eg4
  | Term.Tcase (t, branches) ->
    (* let open API.ContextualConversion in *)
    let st, term, eg = embed_term ~depth st t in
    let st, branches, eg1 = (API.BuiltInData.list term_branch).embed ~depth st branches in
    st, mkApp matchc term [branches], eg@eg1
    (* List.fold_left (fun (st,terms,eg) b ->
      let pat, tm = Term.t_open_branch b in
      let st, pat, eg1, branch_map = embed_pattern ~depth st pat in
      (Mvs.iter (fun v value -> Format.printf "%a -> %d@." Pretty.print_vs v value) map);
      (Format.printf "pattern: %a@." (Elpi.API.RawPp.term depth) pat);
      let map = Mvs.set_union map branch_map in
      let depth = depth + (Mvs.cardinal branch_map) in
      let st, term, eg2 = aux ~depth st tm map in
      let st, term , egs = build_binders pabsc (Mvs.keys branch_map) (st, mkApp branchc pat [term], eg@eg1@eg2)
      in
      st, (mkCons term terms), egs
      (* st, mkCons pat pats, mkCons term terms, eg@eg1@eg2 *)
    ) (st,mkNil,[]) branches
    in *)
    
  | Term.Teps t ->
    let var, term = Term.t_open_bound t in
    let st = API.State.update varmap st (Mvs.add var depth) in
    let depth = depth+1 in
    let t = embed_term ~depth st term in
    build_binders depth epsc [var] t
  | Term.Tquant (q, tq) ->
    let (vlist,trigger,term) = Term.t_open_quant tq in
    begin match trigger with
    | (_::_) -> unsupported "Triggers not supported"
    | [] -> 
      (* Update the variable map (and depth) by adding each variable in the
         order in which it appears in the list of vsymbol (vlist) *)
      let st,depth =
        List.fold_left (fun (st,depth) var ->
          (API.State.update varmap st (Mvs.add var depth), depth + 1) )
          (st, depth) vlist in
      (* The recursive call, with the updated map *)
      let embedded_body = embed_term ~depth st term in
      (* Close binders with the appropriate quantifer constant at the according type *)
      begin match q with
      | Term.Tforall -> build_binders depth allc vlist embedded_body
      | Term.Texists -> build_binders depth existsc vlist embedded_body
      end
    end
  | Term.Tif (t1, t2, t3) ->
    let st, t1, eg1 = embed_term ~depth st t1 in
    let st, t2, eg2 = embed_term ~depth st t2 in
    let st, t3, eg3 = embed_term ~depth st t3 in
    st, mkApp itec t1 [t2;t3], eg1@eg2@eg3
  | Term.Ttrue -> st, mkConst truec, []
  | Term.Tfalse -> st, mkConst falsec, []
  | Term.Tnot t ->
    let st, tm, eg = embed_term ~depth st t in
    st, (mkApp notc tm []), eg
  | Term.Tbinop (op, t1, t2) ->
    let st, t1, eg1 = embed_term ~depth st t1 in
    let st, t2, eg2 = embed_term ~depth st t2 in
    let op = match op with
    | Term.Tand -> andc | Term.Tor ->  orc  
    | Term.Timplies -> impc | Term.Tiff -> iffc
    in st, mkApp op t1 [t2], eg1 @ eg2

and readback_term : Term.term API.Conversion.readback = fun ~depth st tm ->
  (* Format.printf "readback term in state %a@." API.Pp.state st; *)
  let unsupported msg =
  Loc.errorm "Readback not supported for term:@ (%s@, %a)@." msg (Elpi.API.RawPp.term depth) tm
  in
  let open API.RawData in
  let build_quantified_body ~depth st _typ vname bo quant =
    (* note that reading back the type is not necessary, since it is already in the embedded vsymb,
       as long as vsymb is CData *)
    let st, var, eg2 = vsym.readback ~depth st vname in
    let st = API.State.update mapvar st (Constants.Map.add depth var) in
    let st, bo, eg3 = readback_term ~depth st bo in
    (match bo.t_node with
    | Term.Tquant (quant, tq) -> let (vlist,_,bo) = Term.t_open_quant tq in
      st, Term.t_quant_close quant (var::vlist) [] bo, eg2 @ eg3
    | _ -> st, Term.t_quant_close quant [var] [] bo, eg2 @ eg3)
  in
(*Mint.iter (fun k v -> Format.printf "%d -> %a@." k Pretty.print_vs v) map;
  Format.printf "term: %a@." (Elpi.API.RawPp.term depth) tm; *)
  match look ~depth tm with
  | Const c when c == truec -> st, Why3.Term.t_true, []
  | Const c when c == falsec -> st, Why3.Term.t_false, []
  | Const c when c == lsymbc -> unsupported "const"
  | Const c when c>=0 ->
    let var = Constants.Map.find c (API.State.get mapvar st) in
    st, Why3.Term.t_var var, []
  | Const _ -> unsupported "const"
  | Lam t -> readback_term ~depth:(depth+1) st t
  | App (c, t1, [t2]) when c = andc -> 
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_and tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2]) when c = orc ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_or tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2]) when c = impc ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_implies tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2]) when c = iffc ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_iff tt1 tt2, eg1 @ eg2
  | App (c, t1, [t2;t3]) when c = itec ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    let st, tt3, eg3 = readback_term ~depth st t3 in
    st,  Why3.Term.t_if tt1 tt2 tt3, eg1 @ eg2 @ eg3
  | App (c, t1, []) when c = notc ->
    let st, t1, eg = readback_term ~depth st t1 in
    st, Why3.Term.t_not t1, eg
  | App (c, t1, []) when c = lsymbc -> (* Predicate with no arguments *)
    let st, ls, eg = lsym.readback ~depth st t1 in
    st, Why3.Term.t_app_infer ls [], eg
  | App (c, t1, [tl]) when c = applc ->(* Predicate with arguments *)
    let st, t1, eg1 = lsym.readback ~depth st t1 in
    let st, tl, eg2 = (API.BuiltInData.list term).readback ~depth st tl in
    st, Why3.Term.t_app_infer t1 tl, eg1 @ eg2
  | App (c, vname, [typ; bo]) when c = allc ->
    build_quantified_body ~depth st typ vname bo Why3.Term.Tforall
  | App (c, vname, [typ; bo]) when c = existsc ->
    build_quantified_body ~depth st typ vname bo Why3.Term.Texists
  | App (c, vname, [_typ; bo]) when c = epsc -> (* type is in vsymb as cdata *)
    let st, var, eg2 = vsym.readback ~depth st vname in
    let st = API.State.update mapvar st (Constants.Map.add depth var) in
    let st, bo, eg3 = readback_term ~depth st bo in
    st, Term.t_eps_close var bo, eg2 @ eg3
  | App (c, vname, [_typ; t; tbound]) when c = letc -> (* type is in vsymb as cdata *)
    let st, var, eg2 = vsym.readback ~depth st vname in
    let st = API.State.update mapvar st (Constants.Map.add depth var) in
    let st, t, eg3 = readback_term ~depth st t in
    let st, tbound, eg4 = readback_term ~depth st tbound in
    st, Term.t_let_close var t tbound, eg2 @ eg3 @ eg4
  | App (c, n, []) when c = intc -> (* Native integers *)
    let st, n, eg = API.BuiltInData.int.readback ~depth st n
    in st, Why3.Term.t_nat_const n, eg
  | App (c, tm, [branches]) when c = matchc ->
    let st, tm, eg1 = readback_term ~depth st tm in
    let st, branches, eg2 = (API.BuiltInData.list term_branch).readback ~depth st branches in
    st,Term.t_case tm branches,eg1@eg2
  | App (c, _, _) ->
    unsupported (Format.asprintf "app %a" (Elpi.API.RawPp.term depth) (mkConst c))
  | Cons (_, _) -> unsupported "cons"
  | Nil -> unsupported "nil"
  | Builtin (_, _) -> unsupported "builtin"
  | CData _ -> unsupported "cdata"
  | UnifVar (_, _) -> unsupported "unifvar"

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
type all var  -> ty   -> (term -> term) -> term.
type ex  var  -> ty   -> (term -> term) -> term.
type ite term -> term -> term -> term.
type not term -> term.
type top term.
type bot term.
type eps var -> ty -> (term -> term) -> term.
type match term -> list term_branch -> term.
type branch pattern -> term -> term_branch.|});
  readback = readback_term;
  embed = embed_term;
}

and embed_term_branch = fun ~depth st tb ->
  let (pat, tm) = Term.t_open_branch tb in
  let open Elpi.API.RawData in
  let oldmap = API.State.get varmap st in
  let st, pat, eg1 = embed_pattern ~depth st pat in
  let newmap = API.State.get varmap st in
  let map_diff = Term.Mvs.set_diff newmap oldmap in
  (* (Term.Mvs.iter (fun vs bind -> Format.printf "%a bound to %d@." Pretty.print_vs vs bind) map_diff); *)
  let st, tm, eg2 = term.embed ~depth:(depth + Term.Mvs.cardinal map_diff) st tm in
  Term.Mvs.fold (fun vs _vn (st, tm, egs) ->
    let st, vs, eg = vsym.embed ~depth st vs in
    st, mkApp pabsc vs [mkLam tm], egs@eg)
    map_diff (st,mkApp branchc pat [tm],eg1@eg2)

and readback_term_branch = fun ~depth st tb ->
  let unsupported msg =
  Loc.errorm "Readback not supported for term branch: (%s, %a)@." msg (Elpi.API.RawPp.term depth) tb
  in
  let open Elpi.API.RawData in
  match look ~depth tb with
  | App (c, vname,[tbranch]) when c = pabsc ->
    let st, var, eg = vsym.readback ~depth st vname in
    let st = API.State.update mapvar st (Constants.Map.add depth var) in
    (match look ~depth tbranch with
    | Lam t -> let st,tm, eg1 = term_branch.readback ~depth:(depth+1) st t in st, tm, eg@eg1
    | _ -> unsupported "")
  | App (c, pat, [tm]) when c = branchc ->
    let st, pat, eg1 = readback_pattern ~depth st pat in
    let st, tm, eg2 = term.readback ~depth st tm in
    st, Term.t_close_branch pat tm, eg1@eg2
  | _ -> unsupported ""

and term_branch : Term.term_branch API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "term_branch";
  pp = (fun _ _ -> ());
  pp_doc = (fun fmt () -> Format.fprintf fmt "kind term_branch type.");
  readback = readback_term_branch;
  embed = embed_term_branch;
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


(* The current implementation is partial, so for the moment we fallback to an
opaque embedding of data decl*)

(* 
let defc = Elpi.API.RawData.Constants.declare_global_symbol "def"
let def2c = Elpi.API.RawData.Constants.declare_global_symbol "def2"

let embed_data_decl : Decl.data_decl API.Conversion.embedding = fun ~depth st (ddecls : Decl.data_decl) ->
  let open Elpi.API.RawData in
  let (ty, kons) = ddecls in
  let st, tsymb, eg1 = tysym.embed ~depth st ty in
  let st, lkons, eg2 = (* Building a list of constructors for the given type *)
    List.fold_left (fun (st,t,eg) (ls, ll) ->
      let st, projlist, eg1 =
        List.fold_left (fun (st,ll,eg) maybe_ls -> (* Building a list of projection for the given symbol *)
          match maybe_ls with None -> st,ll,eg (** TODO: Important! Store a placeholder for the None case, and update readback accordingly *)
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
    let st, lkons, eg = List.fold_right (fun kons (st, cur, egs) ->
      match (look ~depth kons) with
      | App (h,lsymb,[projlist]) when h=defc ->
        let st, lsymb, eg1 = lsym.readback ~depth st lsymb in
        let st, projlist, eg2 = (API.BuiltInData.list lsym).readback ~depth st projlist in
        st, (lsymb, projlist)::cur, eg1@eg2@egs
      | _ -> unsupported "")
    lkons (st, [], eg)
    in
    let lkons = (List.map (fun (ls,lk) -> ls, List.map (fun x -> Some x) lk) lkons) in
    st, (tsymb, lkons), eg
  | _ -> unsupported "") *)

let data_decl : Decl.data_decl API.Conversion.t = Elpi.API.OpaqueData.declare {
  name = "data_decl";
  pp = pp_why_data (fun fmt (x, _) -> Format.fprintf fmt "%a" Pretty.print_ts x);
  doc = "";
  compare = compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

(** Logic declarations are currently embedded by obtaining and reading back
their defining axiom. This isn't very robust and is subject to change.*)
let logicdeclc = Elpi.API.RawData.Constants.declare_global_symbol "logic"
let embed_logic_decl : Decl.logic_decl API.Conversion.embedding = fun ~depth st (ls,def) ->
  let open API.RawData in
  let st, ax, eg1 = term.embed ~depth st (Decl.ls_defn_axiom def) in
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
    | None -> unsupported (Format.asprintf "Couldn't read back logic declaration from axiom %a" Pretty.print_term ax))
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
let paramc = Elpi.API.RawData.Constants.declare_global_symbol "const"
let tydeclc = Elpi.API.RawData.Constants.declare_global_symbol "typ" (* Abstract type*)
let datac = Elpi.API.RawData.Constants.declare_global_symbol "data"  (* Data (defined) type*)
let decllc = Elpi.API.RawData.Constants.declare_global_symbol "declls"

let embed_decl : Decl.decl API.Conversion.embedding = fun ~depth st decl ->
  let unsupported msg =
  Loc.errorm "Embed not supported for decl :(%s, %a)@." msg Pretty.print_decl decl
  in
  let open Elpi.API.RawData in
  let open Decl in
  let _dtag = decl.d_tag in     (* TODO *)
  let _dnews = decl.d_news in   (* TODO! Useful for bound symbols *) (*   Format.printf "The idents introduced in decl: %s@." (Ident.Sid.fold (fun id str -> id.id_string ^ "," ^ str) _dnews ""); *)
  match decl.d_node with
  | Decl.Dtype ty -> let st, tsymb, eg = tysym.embed ~depth st ty in
    st, mkApp tydeclc tsymb [], eg
  | Decl.Ddata ddecls -> (* Algebraic data *)
    let st, ddecls, eg = (API.BuiltInData.list data_decl).embed ~depth st ddecls
    in st, mkApp datac ddecls [], eg
  | Decl.Dparam p ->
    let st, lsymb, eg = lsym.embed ~depth st p
    in st, mkApp paramc lsymb [], eg
  | Decl.Dlogic ll -> (* Logic declarations *)
    let st, ll, eg = (API.BuiltInData.list logic_decl).embed ~depth st ll
    in st, mkApp decllc ll [], eg
  | Decl.Dprop (k,s,t) ->
    let st, prsym, eg1 = prsymbol.Elpi.API.Conversion.embed ~depth st s in
    let st, tt, eg2 = term.embed ~depth st t in
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
  | App (c, symt, [t]) when c = pgoalc ->  create_prop_decl Decl.Pgoal  symt t
  | App (c, symt, []) when  c = paramc ->
    let st, ls, eg   = lsym.readback ~depth st symt in
(*     if Term.ls_equal ls Term.ps_equ then
      st, Decl.create_prop_decl Decl.Paxiom (Decl.create_prsymbol (Ident.id_fresh "a")) Term.t_true, eg
    else *)
    st, Decl.create_param_decl ls, eg
  | App (c, tysymt, []) when c = tydeclc ->
    let st, ts, eg = tysym.readback ~depth st tysymt in
    st, Decl.create_ty_decl ts, eg
  | App (c, dlist, []) when c = datac -> (* Algebraic data *)
    let st, dlist, eg = (API.BuiltInData.list data_decl).readback ~depth st dlist in
    (* List.iter (Format.printf "obtained %a @." Pretty.print_data_decl) dlist; *)
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
type typ    tysymbol -> decl. %% Abstract type
type data   list data_decl   -> decl. %% Data (defined) type
type declls list logic_decl  -> decl. %% Defined logic symbol
type const  lsymbol  -> decl.|});
  readback = readback_decl;
  embed = embed_decl;
}

let theory : Theory.theory Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "theory";
  doc = "Symbol for theory (currently cannot be inspected)";
  pp = (fun fmt t -> Format.fprintf fmt "%s" t.Theory.th_name.id_string);
  compare = (fun x y -> Stdlib.compare x.th_name y.th_name);
  hash = (fun x -> Hashtbl.hash x.th_name);
  hconsed = false;
  constants = [];
}
let meta : Theory.meta Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "meta";
  doc = "Symbol for meta (currently cannot be inspected)";
  pp = (fun fmt m -> Format.fprintf fmt "%s" m.Theory.meta_name);
  compare = (fun x y -> Stdlib.compare x.meta_tag y.meta_tag);
  hash = (fun x -> Hashtbl.hash x.meta_tag);
  hconsed = false;
  constants = [];
}
let meta_arg : Theory.meta_arg Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "meta-arg";
  doc = "Symbol for meta args (currently cannot be inspected)";
  pp = (fun fmt m -> Format.fprintf fmt "%a" Pretty.print_meta_arg m);
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

(* Hide clones *)
let opaque_tdecl : Theory.tdecl Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "meta-arg";
  doc = "Symbol for arguments of a clone (currently cannot be inspected)";
  pp = (fun fmt t -> Format.fprintf fmt "%s"
        (match t.Theory.td_node with | Theory.Clone (t, _) -> t.th_name.Ident.id_string
        | _ -> "Wrong embedder used!"));
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

let tdecl_declaration : (Theory.tdecl,'a,'b) API.AlgebraicData.declaration = 
  let open API.BuiltInData in {
  ty = TyName "tdecl";
  doc = "Theory declarations";
  pp = Pretty.print_tdecl;
  constructors = [
   K("decl","Local or imported declaration",
     A (decl,N),
     B (fun x -> Theory.create_decl x),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Decl d -> ok d | _ -> ko ())));
   K("use","Use of theory",
     A (theory,N),
     B (fun x -> Theory.create_use x),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Use t -> ok t | _ -> ko ())));
   K("meta","Map of metas",
     A (meta,A(list meta_arg,N)),
     B (fun m args -> Theory.create_meta m args),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Meta (a,args) -> ok a args | _ -> ko ())));
   K("clone","Clone of theory",
     A (opaque_tdecl, N),
     B (fun t -> t),
     M (fun ~ok ~ko td ->
       (match td.td_node with | Theory.Clone (_,_) -> ok td | _ -> ko ())));
  ]
}

let tdecl = API.AlgebraicData.declare tdecl_declaration

(* Tasks are just lists of theory declarations *)
let embed_task : Task.task API.Conversion.embedding =
  let open API.ContextualConversion in
  fun ~depth st task ->
  (API.BuiltInData.list !< tdecl).embed ~depth st (Task.task_tdecls task)

let readback_task : Task.task API.Conversion.readback =
  let open API.ContextualConversion in
  fun ~depth st term ->
    let st, tdecl_list, eg =
      (API.BuiltInData.list !< tdecl).readback ~depth st term in
    let task = List.fold_left Task.add_tdecl None tdecl_list in
    st, task, eg

let task : Task.task API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "list tdecl";
  pp = Pretty.print_task;
  pp_doc = (fun _fmt () -> ());
  readback = readback_task;
  embed = embed_task;
}

let why3_builtin_declarations =
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInData in
  let open Elpi.API.BuiltInPredicate in
  let open Elpi.API.ContextualConversion in
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
        MLCode (Pred ("why3.create-ident",
            In (string, "S",
            Out (ident, "I",
            Easy "Create and register a fresh ident from a string" )),
            fun name _ ~depth:_ -> !: (Ident.id_register (Ident.id_fresh name))),
            DocAbove);
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
            In  (list @@ (!<) ty,  "TS",
            Out (lsym,       "N",
            Easy "Axiomatize a propositional symbol with name N and argument types TS" ))),
            fun name ts _ ~depth:_ -> !: (Term.create_lsymbol (Ident.id_fresh name) ts None)),
        DocAbove );
    MLCode
      ( Pred ( "why3.create-lsymb",
            In  (string,   "N",
            In  (list @@ (!<) ty,  "TS",
            CIn (ty,  "T",
            Out (lsym,       "N",
            Easy "Axiomatize a function symbol with name N, type T and argument types TS" )))),
            fun name ts t _ ~depth:_ -> !: (Term.create_lsymbol (Ident.id_fresh name) ts (Some t))),
        DocAbove );
    MLCode
      ( Pred ( "why3.var-type",
            In  (vsym, "V",
            COut (ty, "T",
            Easy "Get the type of a variable" )),
            fun var _ ~depth:_ -> !: (var.vs_ty)),
        DocAbove );
    MLCode
      (Pred ("why3.lsymb-name",
            In (lsym, "L",
            Out (ident, "S",
            Easy "Get the Ident of a predicate symbol")),
            fun s _ ~depth:_ -> !: (s.ls_name)),
            DocAbove);
    MLCode
      ( Pred ( "why3.lsymb-type",
            In  (lsym, "L",
            COut (ty, "T",
            Easy "Get the type of a predicate symbol" )),
            fun s _ ~depth:_ -> !: (match s.ls_value with None -> Loc.errorm "No type for predicate symbol" | Some t -> t)),
        DocAbove );
    MLCode
      ( Pred ( "why3.lsymb-args-type",
            In  (lsym, "L",
            Out (list @@ (!<) ty, "T",
            Easy "Get the list of the argument types of a predicate symbol" )),
            fun s _ ~depth:_ -> !: (s.ls_args)),
        DocAbove );
    MLCode
      ( Pred ( "why3.search-lsymb",
            In  (env, "E",
            In  (string, "T",
            In  (list string, "N",
            In  (string, "S",
            Out (lsym, "L",
            Easy "\nLook for a symbol in the environment. The theory T and\
            namespace N where the symbol should be looked for need to be\
            provided." ))))),
            fun e t n s _ ~depth:_ -> !: (
              let theory = Env.read_theory e n t in
              Theory.ns_find_ls theory.Theory.th_export [s])),
        DocAbove );
    MLCode (Pred ("why3.data-ty", In (data_decl, "D", Out (tysym, "T", Easy "Get the defined type symbol of a datatype declaration.")),
    fun (ty,_k) _ ~depth:_ -> !: (ty)), DocAbove);
    MLCode
      (Pred ("why3.var-name",
            In (vsym, "V",
            Out (ident, "S",
            Easy "Get the Ident of a variable symbol")),
            fun s _ ~depth:_ -> !: (s.vs_name)),
            DocAbove);
    MLCode
      (Pred ("why3.pr-name",
            In (prsymbol, "V",
            Out (ident, "S",
            Easy "Get the Ident of a proposition declaration symbol")),
            fun s _ ~depth:_ -> !: (s.pr_name)),
            DocAbove);
    MLCode
      (Pred ("why3.ty-name",
            In (tysym, "T",
            Out (ident, "S",
            Easy "Get the Ident of a type symbol")),
            fun t _ ~depth:_ -> !: (t.ts_name)),
            DocAbove);
    MLCode
      ( Pred ( "why3.get-attrs",
            In  (ident, "I",
            Out (list string, "L",
            Easy "\nObtain a list of strings corresponding to the attributes of an\
            identifier. Useful for filtering based on an attribute name,\
            although the underlying attributes are currently not exposed through\
            the API." )),
            fun i _ ~depth:_ -> !: (List.map (fun attr -> attr.Ident.attr_string) (Ident.Sattr.elements i.id_attrs) )),
        DocAbove );
        
    MLData env;
    MLData meta;
    MLData meta_arg;
    MLData theory;
    MLData ident;
    MLData pattern;
    MLData term_branch;
    MLData lsym;
    MLData vsym;
    MLData term;
    MLDataC ty;
    MLData tysym;
    MLData tyvsym;
    MLData prsymbol;
    MLDataC tdecl;
    MLData logic_decl;
    MLData data_decl;
    MLData decl;
    LPCode ""
    ]

let document builtins =
  let w3lp_builtins = API.BuiltIn.declare ~file_name:"w3lp.elpi" builtins
  in let header = "%% API for manipulating Why3 terms and declaration via λProlog\n%% This file is automatically generated."
  in API.BuiltIn.document_file ~header w3lp_builtins