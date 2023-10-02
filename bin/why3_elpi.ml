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
let falsec = Elpi.API.RawData.Constants.declare_global_symbol "ff"
let truec = Elpi.API.RawData.Constants.declare_global_symbol "tt"

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
  let unsupported msg t =
  Loc.errorm "Term not supported:(%s, %a)@." msg Pretty.print_term t
  in
  let open Elpi.API.RawData in
  match term.t_node with
  | Term.Tvar _ -> unsupported "var" term
  | Term.Tconst _ -> unsupported "const" term
  | Term.Tapp (ls, args) ->
    let new_state, s, extra_goals = lsym.Elpi.API.Conversion.embed st ~depth ls in
    new_state, mkApp lsymbc s [], extra_goals
  | Term.Tif (_, _, _)
  | Term.Tlet (_, _)
  | Term.Tcase (_, _)
  | Term.Teps _
  | Term.Tquant (_, _)
  -> unsupported "term" term
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
  | Term.Tiff ->     unsupported "iff" term

let rec readback_term : Term.term API.Conversion.readback = fun ~depth st tm ->
  let unsupported msg =
  Loc.errorm "Readback not supported:(%s, %a)@." msg (Elpi.API.RawPp.term depth) tm
  in
  match API.RawData.look ~depth tm with
  | API.RawData.Const c when c == truec -> st, Why3.Term.t_true, []
  | API.RawData.Const c when c == falsec -> st, Why3.Term.t_false, []
  | API.RawData.Const c when c == lsymbc -> unsupported "const"
  | API.RawData.Const c -> unsupported "const %d"
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
  | API.RawData.App (c, t1, []) when c = lsymbc -> (* To fix for firstorder? *)
    let st, ls, eg = lsym.readback ~depth st t1 in
    st, Why3.Term.t_app_infer ls [], eg
  | API.RawData.App (c, t1, tl) when c = applc -> unsupported "applc"
  | API.RawData.App (c, t1, tl) -> unsupported "app"
  | API.RawData.Cons (_, _) -> unsupported "cons"
  | API.RawData.Nil -> unsupported "nil"
  | API.RawData.Builtin (_, _) -> unsupported "builtin"
  | API.RawData.CData _ -> unsupported "cdata"
  | API.RawData.UnifVar (_, _) -> unsupported "unifvar"

let term : Term.term API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "term";
  pp = Pretty.print_term;
  pp_doc = (fun fmt () -> Format.fprintf fmt {|
kind term type.
type lsymb symbol -> term.
type and term -> term -> term.
type or  term -> term -> term.
type imp term -> term -> term.
type not term -> term.
type tt term.
type tf term.
  |});
  readback = readback_term;
  embed = embed_term;
}

(* let embed_decl (decl : Decl.decl) =
  match decl.d_node with
  | Decl.Dtype _ -> ()
  | Decl.Ddata _ -> ()
  | Decl.Dparam _ -> ()
  | Decl.Dlogic _ -> ()
  | Decl.Dind _ -> ()
  | Decl.Dprop (kind, sym, term) ->
    match kind with
    | Decl.Plemma -> Format.printf "I have a lemma"
    | Decl.Paxiom -> Format.printf "I have an axiom"
    | Decl.Pgoal -> Format.printf "I have a goal" *)
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
  [
    MLCode
      ( Pred ( "why_foo",
            Easy "Let's see if this works",
            fun ~depth:_ -> Format.printf "hello" ),
        DocAbove );
    MLCode
      ( Pred ( "why_print",
            In ( string, "P",
                In ( string, "M",
                    Easy "Print message M with prefix P." )
                   ),
            fun p m ~depth:_ -> Format.printf "%s : %s" m p ),
        DocAbove );
    MLData lsym;
    MLData term;
    LPCode {|type transform term -> term -> prop.|}
    ]
 
let w3lp_builtins =
  API.BuiltIn.declare ~file_name:"w3lp.elpi" why3_builtin_declarations

let document () =
  API.BuiltIn.document_file ~header:"% automatically generated" w3lp_builtins

let query (g : Decl.prsymbol) (t : Term.term) =
  document ();
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
  let main_query = API.Query.compile prog loc (API.Query.Query {predicate = "transform"; arguments = (D(term,t,Q(term,"Output",N)))}) in
  if not (Elpi.API.Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) main_query)
    then Loc.errorm "elpi: type error in file"
  else
  let out_tm =
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize main_query) with
  | Elpi.API.Execute.Success {
      Elpi.API.Data.state; pp_ctx; constraints; output = (tm, ()); _
    } -> Format.printf "elpi: success\n%!"; tm
  | Failure -> Loc.errorm "elpi: failure"
  | NoMoreSteps -> assert false
  in
  [Decl.create_prop_decl Pgoal g out_tm]


let elpi_trans = Trans.goal query

let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"