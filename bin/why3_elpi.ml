open Why3
open Elpi

let types = ref [||]

let handle_out _f (out : unit Elpi.API.Execute.outcome) =
  match out with
  | Elpi.API.Execute.Success(data) ->
    (* Elpi returns answers as a map from query variable names to terms *)
    (* We transform it into a map from names to strings *)
    let resp =
      let open Elpi.API.Data in
      StrMap.map (fun term ->
          Elpi.API.Pp.term (data.pp_ctx) (Format.str_formatter) term;
          Format.flush_str_formatter ())
        data.assignments
    in
    Elpi.API.Data.StrMap.iter (fun var bind -> Format.printf "%s: %s" var bind) resp;
  | _ -> ()


let andc = Elpi.API.RawData.Constants.declare_global_symbol "and"
let orc = Elpi.API.RawData.Constants.declare_global_symbol "or"
let impc = Elpi.API.RawData.Constants.declare_global_symbol "imp"
let applc = Elpi.API.RawData.Constants.declare_global_symbol "appl"
let notc = Elpi.API.RawData.Constants.declare_global_symbol "not"
let lsymbc = Elpi.API.RawData.Constants.declare_global_symbol "lsymb"
let appc = Elpi.API.RawData.Constants.declare_global_symbol "app"
let falsec = Elpi.API.RawData.Constants.declare_global_symbol "ff"
let truec = Elpi.API.RawData.Constants.declare_global_symbol "tt"
let itec = Elpi.API.RawData.Constants.declare_global_symbol "ite"

let lsym : Term.lsymbol Elpi.API.Conversion.t = Elpi.API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "symbol";
  doc = "lsymbol";
  pp = Pretty.print_ls;
  compare = Term.ls_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

let rec embed_term : Term.term API.Conversion.embedding = fun ~depth st term ->
  let unsupported msg =
  Loc.errorm "Term not supported:(%s, %a)@." msg Pretty.print_term term
  in
  let open Elpi.API.RawData in
  match term.t_node with
  | Term.Tvar _ -> unsupported "var"
  | Term.Tconst _ -> unsupported "const"
  | Term.Tapp (ls, []) -> (* single constant *)
    let st, lsy, extra_goals = lsym.Elpi.API.Conversion.embed st ~depth ls in
    st, mkApp lsymbc lsy [], extra_goals
  | Term.Tapp (ls, args) -> (* constant with arguments *)
    let st, lsy, extra_goals = lsym.Elpi.API.Conversion.embed st ~depth ls in
    let st, argslist, egs = List.fold_right (fun arg (st, args, egs) ->
      let st, tt, eg = embed_term ~depth st arg in 
      st, tt::args, eg@egs
    ) args (st,[],[]) in
    let argslist = List.fold_right (fun arg acc ->
      mkCons arg acc
      ) (mkApp lsymbc lsy []::argslist) mkNil in
    st, mkApp appc argslist [], extra_goals
  | Term.Tlet (_, _)
  -> unsupported "let binder"
  | Term.Tcase (_, _)
  -> unsupported "case"
  | Term.Teps _ -> unsupported "epsilon/function"
  | Term.Tquant (q, t) ->
    begin match q with
    | Term.Tforall -> unsupported "forall"
    | Term.Texists -> unsupported "forall"
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
    let eg = eg1 @ eg2 in
  match op with
  | Term.Tand ->     st, (mkApp andc t1 [t2]), eg
  | Term.Tor ->      st, (mkApp orc  t1 [t2]), eg
  | Term.Timplies -> st, (mkApp impc t1 [t2]), eg
  | Term.Tiff ->     st, (mkApp andc (mkApp impc t1 [t2]) [mkApp impc t2 [t1]]), eg

let rec readback_term : Term.term API.Conversion.readback = fun ~depth st tm ->
  let unsupported msg =
  Loc.errorm "Readback not supported for term: (%s, %a)@." msg (Elpi.API.RawPp.term depth) tm
  in
  match API.RawData.look ~depth tm with
  | API.RawData.Const c when c == truec -> st, Why3.Term.t_true, []
  | API.RawData.Const c when c == falsec -> st, Why3.Term.t_false, []
  | API.RawData.Const c when c == lsymbc -> unsupported "const"
  | API.RawData.Const c -> unsupported "const"
  | API.RawData.Lam _ -> unsupported "lam"
  | API.RawData.App (c, t1, [t2]) when c = andc -> 
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_and tt1 tt2, eg1 @ eg2
  | API.RawData.App (c, t1, [t2]) when c = orc ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_or tt1 tt2, eg1 @ eg2
  | API.RawData.App (c, t1, [t2]) when c = impc ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    st,  Why3.Term.t_implies tt1 tt2, eg1 @ eg2
  | API.RawData.App (c, t1, [t2;t3]) when c = itec ->
    let st, tt1, eg1 = readback_term ~depth st t1 in
    let st, tt2, eg2 = readback_term ~depth st t2 in
    let st, tt3, eg3 = readback_term ~depth st t3 in
    st,  Why3.Term.t_if tt1 tt2 tt3, eg1 @ eg2 @ eg3
  | API.RawData.App (c, t1, []) when c = lsymbc -> (* To fix for firstorder? *)
    let st, ls, eg = lsym.readback ~depth st t1 in
    st, Why3.Term.t_app_infer ls [], eg
  | API.RawData.App (c, t1, []) when c = notc ->
    let st, t1, eg = readback_term ~depth st t1 in
    st, Why3.Term.t_not t1, eg
  | API.RawData.App (c, t1, tl) when c = applc -> unsupported "applc"
  | API.RawData.App (c, t1, tl) -> unsupported "app"
  | API.RawData.Cons (_, _) -> unsupported "cons"
  | API.RawData.Nil -> unsupported "nil"
  | API.RawData.Builtin (_, _) -> unsupported "builtin"
  | API.RawData.CData _ -> unsupported "cdata"
  | API.RawData.UnifVar (_, _) -> unsupported "unifvar"

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
  | Decl.Dparam _ -> unsupported "dparam"
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
  | App (_, _, _) -> unsupported "app"
  | Cons (_, _) -> unsupported "cons"
  | Nil -> unsupported "nil"
  | Builtin (_, _) -> unsupported "builtin"
  | CData _ -> unsupported "cdata"
  | UnifVar (_, _) -> unsupported "unifvar"

let term : Term.term API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "term";
  pp = Pretty.print_term;
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind term type.
type lsymb symbol -> term.
type app list term -> term.
type and term -> term -> term.
type or  term -> term -> term.
type imp term -> term -> term.
type ite term -> term -> term -> term.
type not term -> term.
type tt term.
type tf term.|});
  readback = readback_term;
  embed = embed_term;
}

let decl : Decl.decl API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "decl";
  pp = Pretty.print_decl;
  pp_doc = (fun fmt () -> Format.fprintf fmt
{|kind decl type.
type goal  prsymbol -> term -> decl.
type lemma prsymbol -> term -> decl.
type axiom prsymbol -> term -> decl.|});
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
      ( Pred ( "why3.create-prsymbol",
            In  (string, "S",
            Out (prsymbol, "P",
            Easy "Create a fresh prsymbol from a string." )),
            fun name _ ~depth:_ -> !: (Decl.create_prsymbol (Ident.id_fresh name))),
        DocAbove );
    MLCode
      (Pred ( "why3.term->string",
            In  (term, "T",
            Out (string, "S",
            Easy "Pretty print a term using the native pretty printer." )),
            fun t _ ~depth:_ -> !: (Format.asprintf "%a" Pretty.print_term t )),
        DocAbove );
        
    MLData lsym;
    MLData term;
    MLData prsymbol;
    MLData decl;
    LPCode {|type transform decl -> list decl -> prop.|}
    ]
 
let w3lp_builtins =
  API.BuiltIn.declare ~file_name:"w3lp.elpi" why3_builtin_declarations

let document () =
  let header = "%% API for manipulating Why3 terms and declaration via λProlog\n%% This file is automatically generated."
  in
  API.BuiltIn.document_file ~header w3lp_builtins

let query (g : Decl.prsymbol) (t : Term.term) =
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
  let main_query = API.Query.compile prog loc (API.Query.Query {predicate = "transform"; arguments = (D(decl,goal_decl,Q(Elpi.API.BuiltInData.list decl,"Output",N)))}) in
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
  out_decl_list

let elpi_trans = Trans.goal query

let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"