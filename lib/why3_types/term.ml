(* Custom types running through the PPX *)
open Ty
open Common
module WIdent = Why3.Ident
module WPretty = Why3.Pretty
module WTy = Why3.Ty
let declaration = ref []

module WTerm  =
struct
include Why3.Term
    type vsymbol = Why3.Term.vsymbol
    [@@elpi.opaque {
      Elpi.API.OpaqueData.name = "var";
      doc = "Embedding of variable symbols";
      pp = (pp_why_ident Why3.Pretty.print_vs);
      compare = vs_compare;
      hash = Hashtbl.hash;
      hconsed = false;
      constants = [];
    }]
    [@@deriving elpi {declaration}]

    type lsymbol = Why3.Term.lsymbol
    [@@elpi.opaque {
      Elpi.API.OpaqueData.name = "lsymbol";
      doc =
        "Embedding of predicate symbols. Name, argument and value type can be accessed via native predicates.";
      pp = (pp_why_data Why3.Pretty.print_ls);
      compare = ls_compare;
      hash = ls_hash;
      hconsed = false;
      constants = [("infix_at", fs_func_app)];
    }]
    [@@deriving elpi {declaration}]

    type quant = Why3.Term.quant =
      | Tforall
      | Texists
    [@@deriving elpi {declaration}]
    [@@elpi.type_code "quant"]
    [@@elpi.pp fun fmt -> function
      | Tforall -> Format.fprintf fmt "\226\136\128"
      | Texists -> Format.fprintf fmt "\226\136\131"]

    type binop = Why3.Term.binop =
      | Tand
      | Tor
      | Timplies
      | Tiff
    [@@deriving elpi {declaration}]
    [@@elpi.type_code "binop"]
    [@@elpi.pp fun fmt -> function
      | Tand -> Format.fprintf fmt "/\\"
      | Tor -> Format.fprintf fmt "\\/"
      | Timplies -> Format.fprintf fmt "=>"
      | Tiff -> Format.fprintf fmt "<=>"]
end

module Vsym_tags = struct
  open Why3.Term
  type t = vsymbol
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let pp = fun fmt x -> Format.fprintf fmt "`%s`" x.vs_name.id_string
  let show = fun x -> x.vs_name.id_string
end

type ctx_for_term =
| Dctx_vs of (WTerm.vsymbol[@elpi.key]) [@elpi.code "ctx_vs" "term -> var -> prop"]
[@@elpi.index (module Vsym_tags)]
[@@deriving elpi {declaration}]
[@@elpi.pp fun fmt v -> match v with Dctx_vs v -> Format.fprintf fmt "%a" WPretty.print_vs v]
let pp_ctx_for_term = fun fmt c -> ctx_for_term.pp fmt (0,c)

let ctx_entry_to_var (c:ctx_for_term) : WTerm.vsymbol =
  match c with
  | Dctx_vs v -> v

type why_simple_pattern =
  | Pwild of why_simple_ty
  | Pvar of WTerm.vsymbol
  | Papp of WTerm.lsymbol * why_simple_pattern list * why_simple_ty
  | Por of why_simple_pattern * why_simple_pattern
  | Pas of why_simple_pattern * WTerm.vsymbol
[@@deriving elpi {declaration}]
[@@elpi.type_code "pattern"]
[@@elpi.type_doc "Pattern constructors for pattern-matching terms."]
[@@elpi.pp fun fmt -> let rec pp fmt p = match p with
  | Pwild _ -> Format.fprintf fmt "_"
  | Pvar v -> Format.fprintf fmt "%a" WPretty.print_vs v
  | Papp (ls, args, _) -> Format.fprintf fmt "%a(%a)" WPretty.print_ls ls (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp) args
  | Por (p1, p2) -> Format.fprintf fmt "%a | %a" pp p1 pp p2
  | Pas (p, v) -> Format.fprintf fmt "%a as %a" pp p WPretty.print_vs v
  in pp fmt]

let rec pattern_to_simple_pattern (p : WTerm.pattern) : why_simple_pattern =
  match p.pat_node with
  | Pwild -> Pwild (ty_to_why_simple_ty p.pat_ty)
  | Pvar v -> Pvar v
  | Papp (ls, args) -> Papp (ls, List.map pattern_to_simple_pattern args, ty_to_why_simple_ty p.pat_ty)
  | Por (p1, p2) -> Por (pattern_to_simple_pattern p1, pattern_to_simple_pattern p2)
  | Pas (p, v) -> Pas (pattern_to_simple_pattern p, v)

let rec simple_pattern_to_pattern p =
  match p with
  | Pwild ty -> WTerm.pat_wild (why_simple_ty_to_ty ty)
  | Pvar v -> WTerm.pat_var v
  | Papp (ls, args, ty) ->
    WTerm.pat_app ls (List.map simple_pattern_to_pattern args) (why_simple_ty_to_ty ty)
  | Por (p1, p2) -> WTerm.pat_or (simple_pattern_to_pattern p1) (simple_pattern_to_pattern p2)
  | Pas (p, v) -> WTerm.pat_as (simple_pattern_to_pattern p) v

type why_simple_term =
  | Tvar of WTerm.vsymbol [@elpi.var ctx_for_term]
  | Tint of int
  | Tapp of WTerm.lsymbol * why_simple_term list
  | Tquant of WTerm.quant * WTerm.vsymbol  * (why_simple_term [@elpi.binder "term" ctx_for_term (fun _q v -> Dctx_vs v)])
  | Teps of WTerm.vsymbol * (why_simple_term [@elpi.binder "term" ctx_for_term (fun v -> Dctx_vs v)])
  | Ttrue | Tfalse
  | Tbinop of WTerm.binop * why_simple_term * why_simple_term
  | Tif of why_simple_term * why_simple_term * why_simple_term
  | Tnot of why_simple_term
  | Tcase of why_simple_term * why_simple_ty * (why_simple_pattern * why_simple_term) list
  (* Explicit binders in pattern matching *)
  | Pabs of WTerm.vsymbol * (why_simple_term [@elpi.binder "term" ctx_for_term (fun v -> Dctx_vs v)])
[@@deriving elpi {declaration; context=[ctx_for_term];}]
[@@elpi.type_code "term"]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<term>"]
let rec pp_simple_term = 
  fun fmt t -> match t with
  | Tvar v -> Format.fprintf fmt "(%a:%a)" WPretty.print_vs v WPretty.print_ty v.vs_ty
  | Tint n -> Format.fprintf fmt "%d" n
  | Tapp (ls, args) -> Format.fprintf fmt "%a(%a)" WPretty.print_ls ls (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_simple_term) args
  | Tquant (q, v, t) -> Format.fprintf fmt "%a %a. %a" (WPretty.print_quant) q WPretty.print_vs v pp_simple_term t
  | Teps (v, t) -> Format.fprintf fmt "eps %a. %a" WPretty.print_vs v pp_simple_term t
  | Ttrue -> Format.fprintf fmt "true"
  | Tfalse -> Format.fprintf fmt "false"
  | Tbinop (op, t1, t2) -> Format.fprintf fmt "(%a %a %a)" pp_simple_term t1 (WPretty.print_binop ~asym:false) op pp_simple_term t2
  | Tif (t1, t2, t3) -> Format.fprintf fmt "if %a then %a else %a" pp_simple_term t1 pp_simple_term t2 pp_simple_term t3
  | Tnot t -> Format.fprintf fmt "not %a" pp_simple_term t
  | Tcase (t, ty, branches) -> Format.fprintf fmt "case %a : %a of %a" pp_simple_term t why_simple_ty.pp ty (Format.pp_print_list ~pp_sep:Why3.Pp.comma (Why3.Pp.print_pair why_simple_pattern.pp pp_simple_term)) branches
  | Pabs (v, t) -> Format.fprintf fmt "(%a => %a)" WPretty.print_vs v pp_simple_term t
let rec term_to_simple_term (t : WTerm.term) : why_simple_term =
  match t.t_node with
  | Tvar v -> Tvar v
  | Tconst c -> (
    match c with
    | ConstInt n -> Tint (Why3.BigInt.to_int n.il_int)
    | ConstReal _ -> assert false
    | ConstStr _ -> assert false
  )
  | Tapp (ls, args) -> Tapp (ls, List.map term_to_simple_term args)
  | Tif (t1, t2, t3) -> Tif (term_to_simple_term t1, term_to_simple_term t2, term_to_simple_term t3)
  | Tlet (_, _) -> assert false
  | Tcase (t, branches) ->
    let first_pattern_type =
      match branches with
      | [] -> assert false
      | b::_ -> let (p,_) = (WTerm.t_open_branch b) in ty_to_why_simple_ty p.pat_ty in
    let branches = List.map term_branch_to_simple_term branches in
    Tcase (term_to_simple_term t, first_pattern_type, branches)
  | Teps t -> let (v, t) =  WTerm.t_open_bound t in Teps (v, term_to_simple_term t)
  | Tquant (q, t) ->
    (match WTerm.t_open_quant t with
    | [v], _trig, t -> Tquant (q, v, term_to_simple_term t)
    | v::vs, _trig,t -> Tquant (q, v, term_to_simple_term (WTerm.t_quant_close q vs [] t))
    | _ -> assert false)
  | Tbinop (op, t1, t2) -> Tbinop (op, term_to_simple_term t1, term_to_simple_term t2)
  | Tnot t -> Tnot (term_to_simple_term t)
  | Ttrue -> Ttrue
  | Tfalse -> Tfalse
and term_branch_to_simple_term (t : WTerm.term_branch) : (why_simple_pattern * why_simple_term) =
  let (pattern, term) = WTerm.t_open_branch t in
  let tm =  WTerm.Svs.fold (fun v acc -> Pabs (v, acc)) pattern.pat_vars (term_to_simple_term term)
  in (pattern_to_simple_pattern pattern, tm)

let rec simple_term_to_term (st : why_simple_term) : WTerm.term =
  let rec consume_quant q t =
    match t with
    | Tquant (q1, v, t) when q1 = q -> let vs, t  = consume_quant q t in v::vs, t
    | t -> [],t
  in
  match st with
  | Tvar v -> WTerm.t_var v
  | Tint n -> WTerm.t_const (Why3.Constant.int_const_of_int n) WTy.ty_int
  | Tapp (ls, args) ->
      let targs = List.map simple_term_to_term args in
      WTerm.t_app_infer ls targs (* Using t_app without inference might be more efficient, but I had troubles with typing @ applied to typed args*)
  | Tquant (q, v, t) -> let vs, t = consume_quant q t in WTerm.t_quant_close q (v::vs) [] (simple_term_to_term t)
  | Teps (v, t) -> WTerm.t_eps_close v (simple_term_to_term t)
  | Ttrue -> WTerm.t_true
  | Tfalse -> WTerm.t_false
  | Tbinop (op, t1, t2) -> WTerm.t_binary op (simple_term_to_term t1) (simple_term_to_term t2)
  | Tif (t1, t2, t3) -> WTerm.t_if (simple_term_to_term t1) (simple_term_to_term t2) (simple_term_to_term t3)
  | Tnot t -> WTerm.t_not (simple_term_to_term t)
  | Tcase (t, ty, branches) ->
    let rec strip_branch_binders = function
      | Pabs (_, t) -> strip_branch_binders t
      | t -> t
    in
    let simple_term_to_term_branch (p, t) =
      let t = strip_branch_binders t in
      let p = simple_pattern_to_pattern p in
      let t = simple_term_to_term t in
      WTerm.t_close_branch p t
    in
    WTerm.t_case (simple_term_to_term t) (List.map simple_term_to_term_branch branches)
  | Pabs (_, _) -> assert false (* Should only appear in branches and be consumed by the branch reconstructor *)

let term : 'c 'csts .  (WTerm.term, 'c, 'csts) Elpi.API.ContextualConversion.t =
let open Elpi.API.ContextualConversion in
  let kind = TyName "term" in
  {ty = kind;
   pp_doc = why_simple_term.pp_doc;
   pp = WPretty.print_term;
   embed = (fun ~depth h c s t -> elpi_embed_why_simple_term ~depth h c s (term_to_simple_term t));
   readback = (fun ~depth h c s t -> let (a,b,c) = elpi_readback_why_simple_term ~depth h c s t in (a, simple_term_to_term b, c))
  }
let lsymbol = WTerm.lsymbol
let vsymbol = WTerm.vsymbol