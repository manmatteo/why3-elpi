open Why3
open Elpi

(* Constants for Why3 HOAS *)
let andc = Elpi.API.RawData.Constants.declare_global_symbol "and"
let orc = Elpi.API.RawData.Constants.declare_global_symbol "or"
let impc = Elpi.API.RawData.Constants.declare_global_symbol "imp"
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
  pp = Pretty.print_ts;
  compare = Ty.ts_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [("ts_int", Ty.ts_int ); ("ts_real", Ty.ts_real ); ("ts_bool", Ty.ts_bool ); ("ts_str", Ty.ts_str )];
}

let rec embed_ty : Why3.Ty.ty API.Conversion.embedding = fun ~depth st ty ->
  let open Elpi.API.RawData in
  match ty.ty_node with
  | Ty.Tyapp (h, []) ->
    let st, ts, eg = tysym.Elpi.API.Conversion.embed ~depth st h in
    st, mkApp tsymbc ts [], eg
  | Ty.Tyapp (h, l) ->
    let st, ts, eg = tysym.Elpi.API.Conversion.embed ~depth st h in
    let st, tl, egs = List.fold_right (fun arg (st, args, egs) ->
      let st, tt, eg = embed_ty ~depth st arg in 
      st, mkCons tt args, eg@egs
    ) l (st,mkNil,[]) in
    st, mkApp tappc ts [tl], eg
  | Ty.Tyvar v ->
    let st, vsymb, eg = tyvsym.embed ~depth st v in
    st, mkApp tvarc vsymb [], eg

(* This readback is defined in mutual recursion with the entire conversion *)
let rec readback_ty : Ty.ty API.Conversion.readback = fun ~depth st tm ->
  let unsupported msg =
  Loc.errorm "Readback not supported for type: (%s, %a)@." msg (Elpi.API.RawPp.term depth) tm
  in
  match (API.RawData.look ~depth tm) with
  | API.RawData.Const c -> unsupported ""
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

let int : Number.int_constant API.Conversion.t = 
let open Elpi.API.Conversion in {
ty = TyName "int";
pp = (fun _ _ -> ());
pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind int type.|});
readback = (fun ~depth st tm -> assert false);
embed = (fun ~depth st tm -> assert false);
}

let embed_term : Term.term API.Conversion.embedding = fun ~depth st term ->
  let unsupported msg =
  Loc.errorm "Term not supported:(%s, %a)@." msg Pretty.print_term term
  in
  let open Elpi.API.RawData in
  let open Term in
  let rec aux ~depth st term (map : constant Mvs.t) =
  match term.t_node with
  | Term.Tvar v -> st, mkBound @@ Mvs.find v map, []
  | Term.Tconst c ->
    begin match c with
    | Constant.ConstInt n -> let st, tm, eg = API.BuiltInData.int.embed ~depth st (BigInt.to_int n.il_int) in st, mkApp intc tm [], eg
    | Constant.ConstReal r -> unsupported "real"
    | Constant.ConstStr s -> let st, tm, eg = API.BuiltInData.string.embed ~depth st s in st, mkApp strc tm [], eg
    end
  | Term.Tapp (ls, []) -> (* single constant *)
    let st, lsy, extra_goals = lsym.Elpi.API.Conversion.embed st ~depth ls in
    st, mkApp lsymbc lsy [], extra_goals
  | Term.Tapp (ls, args) -> (* constant with arguments *)
    let st, lsy, extra_goals = lsym.Elpi.API.Conversion.embed st ~depth ls in
    let st, argslist, egs = List.fold_right (fun arg (st, args, egs) ->
      let st, tt, eg = aux ~depth st arg map in 
      st, tt::args, eg@egs
    ) args (st,[],[]) in
    let argslist = List.fold_right (fun arg acc ->
      mkCons arg acc
      ) argslist mkNil in
    st, mkApp applc lsy [argslist], extra_goals
  | Term.Tlet (_, _)
  -> unsupported "let binder"
  | Term.Tcase (_, _)
  -> unsupported "case"
  | Term.Teps _ -> unsupported "epsilon/function"
  | Term.Tquant (q, tq) ->
    let (vlist,trigger,term) = Term.t_open_quant tq in
    begin match trigger with
    | (a::_) -> unsupported "Triggers not supported"
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
  | Term.Tiff ->     st, (mkApp andc (mkApp impc t1 [t2]) [mkApp impc t2 [t1]]), eg
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
  let aux_conversion : Term.vsymbol Mint.t -> Term.term API.Conversion.t = fun m -> {
    API.Conversion.ty = API.Conversion.TyName "term";
    pp = Pretty.print_term;
    pp_doc = (fun fmt () -> ());
    readback = (fun ~depth st tm -> aux ~depth st tm m);
    embed = embed_term;
  }
  in
(*   Mint.iter (fun k v -> Format.printf "%d -> %a@." k Pretty.print_vs v) map;
  Format.printf "term: %a@." (Elpi.API.RawPp.term depth) tm; *)
  match look ~depth tm with
  | Const c when c == truec -> st, Why3.Term.t_true, []
  | Const c when c == falsec -> st, Why3.Term.t_false, []
  | Const c when c == lsymbc -> unsupported "const"
  | Const c when c>=0 ->
    st, Why3.Term.t_var (Mint.find c map), []
  | Const c -> unsupported "const"
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
    let st, typ, eg1 = ty.readback ~depth st typ in
    let var = Term.create_vsymbol (Ident.id_fresh "x") typ in
    let map = Mint.add depth var map in
    let st, bo, eg2 = aux ~depth st bo map in
    st, Why3.Term.t_forall_close [var] [] bo, eg1 @ eg2
  | App (c, typ, [bo]) when c = existsc ->
    let st, typ, eg1 = ty.readback ~depth st typ in
    let var = Term.create_vsymbol (Ident.id_fresh "x") typ in
    let map = Mint.add depth var map in
    let st, bo, eg2 = aux ~depth st bo map in
    st, Why3.Term.t_exists_close [var] [] bo, eg1 @ eg2
  | App (c, t1, tl) ->
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
let plemmac = Elpi.API.RawData.Constants.declare_global_symbol "lemma"
let paxiomc = Elpi.API.RawData.Constants.declare_global_symbol "axiom"
let pgoalc = Elpi.API.RawData.Constants.declare_global_symbol "goal"
let paramc = Elpi.API.RawData.Constants.declare_global_symbol "param"

let rec embed_decl : Decl.decl API.Conversion.embedding = fun ~depth st decl ->
  let unsupported msg =
  Loc.errorm "Embed not supported for decl :(%s, %a)@." msg Pretty.print_decl decl
  in
  let open Elpi.API.RawData in
  let _dtag = decl.d_tag in     (* TODO *)
  let _dnews = decl.d_news in   (* TODO *)
  match decl.d_node with
  | Decl.Dtype _ -> unsupported "dtype"
  | Decl.Ddata _ -> unsupported "ddata"
  | Decl.Dparam p -> let st, lsymb, eg = lsym.embed ~depth st p in
    st, mkApp paramc lsymb [], eg
  | Decl.Dlogic _ -> unsupported "dlogic"
  | Decl.Dind _ -> unsupported "dind"
  | Decl.Dprop p ->
    let (k, s, t) = p in
    let st, prsym, eg = prsymbol.Elpi.API.Conversion.embed ~depth st s in
    let st, tt, eg = embed_term ~depth st t in
    match k with
    | Decl.Plemma ->
        st, mkApp plemmac prsym [tt], []
    | Decl.Paxiom ->
        st, mkApp paxiomc prsym [tt], []
    | Decl.Pgoal ->
        st, mkApp pgoalc  prsym [tt], []

let rec readback_decl : Decl.decl API.Conversion.readback = fun ~depth st decl ->
  let unsupported msg =
  Loc.errorm "Readback not supported for decl: (%s, %a)@." msg (Elpi.API.RawPp.term depth) decl
  in
  let create_decl k symt t =
    let st, prs, eg1 = prsymbol.readback ~depth st symt in
    let st, tt, eg2  = readback_term ~depth st t in
    st, Decl.create_prop_decl k prs tt, eg1 @ eg2
  in
  let open Elpi.API.RawData in
  match look ~depth decl with
  | Const _ -> unsupported "const"
  | Lam _ -> unsupported "lam"
  | App (c, symt, [t]) when c = plemmac -> create_decl Decl.Plemma symt t
  | App (c, symt, [t]) when c = paxiomc -> create_decl Decl.Paxiom symt t
  | App (c, symt, [t]) when c = pgoalc ->  create_decl Decl.Pgoal symt t
  | App (c, symt, []) when c = paramc ->
    let st, ls, eg = lsym.readback ~depth st symt in
    st, Decl.create_param_decl ls, eg
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
type goal  prsymbol -> term -> decl.
type lemma prsymbol -> term -> decl.
type axiom prsymbol -> term -> decl.
type param lsymbol -> decl.|});
  readback = readback_decl;
  embed = embed_decl;
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
    LPCode {|type transform string -> decl -> list decl -> prop.|}
    ]
 
let w3lp_builtins =
  API.BuiltIn.declare ~file_name:"w3lp.elpi" why3_builtin_declarations

let document () =
  let header = "%% API for manipulating Why3 terms and declaration via λProlog\n%% This file is automatically generated."
  in
  API.BuiltIn.document_file ~header w3lp_builtins

let query (arg: string) (g : Decl.prsymbol) (t : Term.term) =
  document ();
  let goal_decl = Decl.create_prop_decl Pgoal g t in
  let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi"
  (why3_builtin_declarations @ Elpi.Builtin.std_declarations)] in
  let elpi = (API.Setup.init ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
  let loc = Elpi.API.Ast.Loc.initial "(elpi)" in
  let ast = Elpi.API.Parse.program ~elpi ~files:["test.elpi"] in
  let prog =
    let flags = Elpi.API.Compile.default_flags in
    ast |>
    Elpi.API.Compile.unit ~flags ~elpi |>
    (fun u -> Elpi.API.Compile.assemble ~elpi ~flags [u]) in
  let main_query = API.Query.compile prog loc (API.Query.Query {predicate = "transform"; arguments = (D(API.BuiltInData.string, arg, D(decl,goal_decl,Q(Elpi.API.BuiltInData.list decl,"Output",N))))}) in
  if not (Elpi.API.Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) main_query)
    then Loc.errorm "elpi: type error in file"
  else
  let out_decl_list =
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize main_query) with
  | Elpi.API.Execute.Success {
      Elpi.API.Data.state = st; pp_ctx; constraints; output = (tm, ()); _
    } -> Format.printf "elpi: success\n%!" ; tm
  | Failure -> Loc.errorm "elpi: failure"
  | NoMoreSteps -> assert false
  in
  List.iter (Format.printf "decl: %a@." Pretty.print_decl) out_decl_list;
  out_decl_list

let elpi_trans : Trans.trans_with_args = 
  fun argl _env _namtab _name  ->
    match argl with
    | [arg] -> (Trans.goal (query arg))
    | _ -> Loc.errorm "elpi: wrong number of arguments"

(* let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command" *)
let () = Trans.register_transform_with_args "lp" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"