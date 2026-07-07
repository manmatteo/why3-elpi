(* Custom types running through the PPX *)
open Ty
open Common
module WIdent = Why3.Ident
module WPretty = Why3.Pretty
module WTy = Why3.Ty

let declaration = ref []

module WTerm = struct
  include Why3.Term

  type vsymbol = Why3.Term.vsymbol
  [@@elpi.opaque
    { Elpi.API.OpaqueData.name = "var"
    ; doc = "Embedding of variable symbols"
    ; pp = pp_why_ident Why3.Pretty.print_vs
    ; compare = vs_compare
    ; hash = Hashtbl.hash
    ; hconsed = false
    ; constants = []
    }]
  [@@deriving elpi { declaration }]

  type lsymbol = Why3.Term.lsymbol
  [@@elpi.opaque
    { Elpi.API.OpaqueData.name = "lsymbol"
    ; doc =
        "Embedding of predicate symbols. Name, argument and value type can be \
         accessed via native predicates."
    ; pp = pp_why_data Why3.Pretty.print_ls
    ; compare = ls_compare
    ; hash = ls_hash
    ; hconsed = false
    ; constants = [ ("infix_at", fs_func_app) ]
    }]
  [@@deriving elpi { declaration }]

  let lsymbol_generated = lsymbol

  let lsymbol : 'c 'csts. (lsymbol, 'c, 'csts) Elpi.API.ContextualConversion.t =
    let pp_doc fmt () =
      Format.fprintf fmt
        "%% Embedding of predicate symbols. Name, argument and value type can \
         be@\n";
      Format.fprintf fmt "%% accessed via native predicates.@\n";
      Format.fprintf fmt "kind lsymbol type.@\n@\n";
      Format.fprintf fmt "external symbol infix_at : lsymbol.@\n"
    in
    { lsymbol_generated with pp_doc }

  type prsymbol = Why3.Decl.prsymbol
  [@@elpi.opaque
    { Elpi.API.OpaqueData.name = "prsymbol"
    ; doc = "Names for declarations"
    ; pp = Why3.Pretty.print_pr
    ; compare
    ; hash = Hashtbl.hash
    ; hconsed = false
    ; constants = []
    }]
  [@@deriving elpi { declaration }]

  type constant = Why3.Constant.constant
  [@@elpi.opaque
    { Elpi.API.OpaqueData.name = "constant"
    ; doc = "Embedding of Why3 constants"
    ; pp =
        pp_why_data (fun fmt c ->
            match c with
            | Why3.Constant.ConstInt n ->
              Format.fprintf fmt "%s" (Why3.BigInt.to_string n.il_int)
            | Why3.Constant.ConstReal _ -> Format.fprintf fmt "<real>"
            | Why3.Constant.ConstStr s -> Format.fprintf fmt "\"%s\"" s)
    ; compare
    ; hash = Hashtbl.hash
    ; hconsed = false
    ; constants = []
    }]
  [@@deriving elpi { declaration }]

  type quant = Why3.Term.quant =
    | Tforall
    | Texists
  [@@deriving elpi { declaration }]
  [@@elpi.type_code "quant"]
  [@@elpi.pp
    fun fmt -> function
     | Tforall -> Format.fprintf fmt "\226\136\128"
     | Texists -> Format.fprintf fmt "\226\136\131"]

  type binop = Why3.Term.binop =
    | Tand
    | Tor
    | Timplies
    | Tiff
  [@@deriving elpi { declaration }]
  [@@elpi.type_code "binop"]
  [@@elpi.pp
    fun fmt -> function
     | Tand -> Format.fprintf fmt "/\\"
     | Tor -> Format.fprintf fmt "\\/"
     | Timplies -> Format.fprintf fmt "=>"
     | Tiff -> Format.fprintf fmt "<=>"]
end

(* Attributes are embedded structurally by their string: Why3 attributes are
   hashconsed by Ident.create_attribute, so reading an (attr S) back yields the
   identical Why3 attribute and no identity is lost at the boundary. *)
type attribute = Attr of string
[@@deriving elpi { declaration }]
[@@elpi.type_code "attribute"]
[@@elpi.type_doc
  "Why3 attributes, embedded structurally: (attr S) is the attribute with \
   string representation S."]
[@@elpi.pp fun fmt (Attr s) -> Format.fprintf fmt "%s" s]

module Vsym_tags = struct
  open Why3.Term

  type t = vsymbol

  let compare = compare
  let hash = Hashtbl.hash
  let equal = ( = )
  let pp = fun fmt x -> Format.fprintf fmt "`%s`" x.vs_name.id_string
  let show = fun x -> x.vs_name.id_string
end

module Lsym_tags = struct
  open Why3.Term

  type t = lsymbol

  let compare = ls_compare
  let hash = ls_hash
  let equal x y = ls_compare x y = 0
  let pp = fun fmt x -> Format.fprintf fmt "`%s`" x.ls_name.id_string
  let show = fun x -> x.ls_name.id_string
end

type ctx_for_term = Ctx_vs of (WTerm.vsymbol[@elpi.key])
(* Now the PPX can generate this [@elpi.code "ctx-vs" "term -> var -> prop"] *)
[@@elpi.index (module Vsym_tags) "term"]
[@@deriving elpi { declaration }]
[@@elpi.pp
  fun fmt v ->
    match v with
    | Ctx_vs v -> Format.fprintf fmt "%a" WPretty.print_vs v]

let pp_ctx_for_term = fun fmt c -> ctx_for_term.pp fmt (0, c)

type ctx_for_lsymbol = Ctx_ls of (WTerm.lsymbol[@elpi.key])
[@@elpi.index (module Lsym_tags) "term"]
[@@deriving elpi { declaration }]
[@@elpi.pp
  fun fmt v ->
    match v with
    | Ctx_ls ls -> Format.fprintf fmt "%a" WPretty.print_ls ls]

let pp_ctx_for_lsymbol = fun fmt c -> ctx_for_lsymbol.pp fmt (0, c)

type why_simple_pattern =
  | Pwild
  | Pvar of WTerm.vsymbol
  | Papp of WTerm.lsymbol * why_simple_pattern list
  | Por of why_simple_pattern * why_simple_pattern
  | Pas of why_simple_pattern * WTerm.vsymbol
[@@elpi.type_code "pattern"]
[@@elpi.type_doc
  "Pattern constructors for pattern-matching terms. Use pvar to name \
   pattern-bound variables and babs to bind their body occurrences."]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<pattern>"]

and why_simple_branch =
  | Branch of why_simple_pattern * why_simple_term
  | Babs of
      WTerm.vsymbol
      * (why_simple_branch
        [@elpi.binder "term" ctx_for_term (fun v -> Ctx_vs v)])
[@@elpi.type_code "branch"]
[@@elpi.type_doc
  "Case branches. Use babs to bind pattern variables, then branch to pair the \
   pattern with its body."]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<branch>"]

and why_simple_term =
  | Tvar of WTerm.vsymbol [@elpi.var ctx_for_term]
  | Tattr of attribute list * why_simple_term
  | Tconst of WTerm.constant * why_simple_ty
  | Tapp of WTerm.lsymbol * why_simple_term list * why_simple_ty option
  | Tlet of
      why_simple_term
      * WTerm.vsymbol
      * (why_simple_term
        [@elpi.binder "term" ctx_for_term (fun _t v -> Ctx_vs v)])
  | Ttrigger of why_simple_term list list * why_simple_term
  | Tquant of
      WTerm.quant
      * WTerm.vsymbol
      * (why_simple_term
        [@elpi.binder "term" ctx_for_term (fun _q v -> Ctx_vs v)])
  | Teps of
      WTerm.vsymbol
      * (why_simple_term[@elpi.binder "term" ctx_for_term (fun v -> Ctx_vs v)])
  | Ttrue
  | Tfalse
  | Tbinop of WTerm.binop * why_simple_term * why_simple_term
  | Tif of why_simple_term * why_simple_term * why_simple_term
  | Tnot of why_simple_term
  | Tcase of why_simple_term * why_simple_branch list
[@@deriving elpi { declaration; context = [ ctx_for_term; ctx_for_lsymbol ] }]
[@@elpi.type_code "term"]
[@@elpi.type_doc
  "Why3 terms. Use tattr to attach attributes to a subterm. Pattern-matching \
   uses branch/babs HOAS branches, applications have optional type \
   annotations, and quantifier triggers use an explicit ttrigger carrier \
   directly under the quantifier body."]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<term>"]

type decl_body =
  | Dterm of why_simple_term
  | Dabs of
      WTerm.vsymbol
      * (decl_body[@elpi.binder "term" ctx_for_term (fun v -> Ctx_vs v)])
[@@deriving elpi { declaration; context = [ ctx_for_term; ctx_for_lsymbol ] }]
[@@elpi.type_code "decl_body"]
[@@elpi.type_doc
  "Opened declaration bodies. Use dabs for definition parameters and dterm for \
   the final body term."]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<decl-body>"]

let pp_attribute fmt (Attr s) = Format.fprintf fmt "%s" s

let pp_attrs fmt attrs =
  match attrs with
  | [] -> ()
  | _ ->
    Format.fprintf fmt "[@%a] "
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         pp_attribute)
      attrs

let rec pp_simple_pattern fmt p =
  match p with
  | Pwild -> Format.fprintf fmt "_"
  | Pvar v -> Format.fprintf fmt "%a" WPretty.print_vs v
  | Papp (ls, args) ->
    Format.fprintf fmt "%a(%a)" WPretty.print_ls ls
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         pp_simple_pattern)
      args
  | Por (p1, p2) ->
    Format.fprintf fmt "%a | %a" pp_simple_pattern p1 pp_simple_pattern p2
  | Pas (p, v) ->
    Format.fprintf fmt "%a as %a" pp_simple_pattern p WPretty.print_vs v

and pp_simple_branch fmt branch =
  match branch with
  | Branch (pattern, body) ->
    Format.fprintf fmt "%a => %a" pp_simple_pattern pattern pp_simple_term body
  | Babs (v, branch) ->
    Format.fprintf fmt "(%a => %a)" WPretty.print_vs v pp_simple_branch branch

and pp_simple_term =
 fun fmt t ->
  match t with
  | Tvar v ->
    Format.fprintf fmt "(%a:%a)" WPretty.print_vs v WPretty.print_ty v.vs_ty
  | Tattr (attrs, t) ->
    pp_attrs fmt attrs;
    pp_simple_term fmt t
  | Tconst (c, _) -> (
    match c with
    | ConstInt n -> Format.fprintf fmt "%s" (Why3.BigInt.to_string n.il_int)
    | ConstReal _ -> Format.fprintf fmt "<real>"
    | ConstStr _ -> Format.fprintf fmt "<str>")
  | Tapp (ls, args, _ty) ->
    Format.fprintf fmt "%a(%a)" WPretty.print_ls ls
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         pp_simple_term)
      args
  | Tlet (t1, v, t2) ->
    Format.fprintf fmt "let %a = %a in %a" WPretty.print_vs v pp_simple_term t1
      pp_simple_term t2
  | Ttrigger (tr, t) ->
    let pp_one fmt terms =
      Format.fprintf fmt "[%a]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           pp_simple_term)
        terms
    in
    Format.fprintf fmt "trigger {%a} in %a"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         pp_one)
      tr pp_simple_term t
  | Tquant (q, v, t) ->
    Format.fprintf fmt "%a %a. %a" WPretty.print_quant q WPretty.print_vs v
      pp_simple_term t
  | Teps (v, t) ->
    Format.fprintf fmt "eps %a. %a" WPretty.print_vs v pp_simple_term t
  | Ttrue -> Format.fprintf fmt "true"
  | Tfalse -> Format.fprintf fmt "false"
  | Tbinop (op, t1, t2) ->
    Format.fprintf fmt "(%a %a %a)" pp_simple_term t1
      (WPretty.print_binop ~asym:false)
      op pp_simple_term t2
  | Tif (t1, t2, t3) ->
    Format.fprintf fmt "if %a then %a else %a" pp_simple_term t1 pp_simple_term
      t2 pp_simple_term t3
  | Tnot t -> Format.fprintf fmt "not %a" pp_simple_term t
  | Tcase (t, branches) ->
    Format.fprintf fmt "case %a of %a" pp_simple_term t
      (Format.pp_print_list ~pp_sep:Why3.Pp.comma pp_simple_branch)
      branches

let rec pp_decl_body fmt = function
  | Dterm t -> pp_simple_term fmt t
  | Dabs (v, body) ->
    Format.fprintf fmt "%a => %a" WPretty.print_vs v pp_decl_body body

let attrs_of_sattr attrs =
  List.map
    (fun a -> Attr a.Why3.Ident.attr_string)
    (Why3.Ident.Sattr.elements attrs)

let sattr_of_attrs attrs =
  List.fold_left
    (fun sattr (Attr s) ->
      Why3.Ident.Sattr.add (Why3.Ident.create_attribute s) sattr)
    Why3.Ident.Sattr.empty attrs

let term_attrs (t : WTerm.term) = attrs_of_sattr t.t_attrs

let wrap_attrs attrs st =
  match attrs with
  | [] -> st
  | _ -> Tattr (attrs, st)

let wrap_term_attrs t st = wrap_attrs (term_attrs t) st
let same_vsymbol v1 v2 = WTerm.vs_compare v1 v2 = 0

let rec same_vsymbol_list xs ys =
  match (xs, ys) with
  | [], [] -> true
  | x :: xs, y :: ys -> same_vsymbol x y && same_vsymbol_list xs ys
  | _ -> false

let pattern_type_error fmt =
  Format.kasprintf (fun msg -> Elpi.API.Utils.type_error msg) fmt

let ensure_pattern_type what actual expected =
  if not (WTy.ty_equal actual expected) then
    pattern_type_error "%s has type %a but the surrounding pattern expects %a"
      what WPretty.print_ty actual WPretty.print_ty expected

let rec pattern_to_simple_pattern (p : WTerm.pattern) : why_simple_pattern =
  match p.pat_node with
  | Pwild -> Pwild
  | Pvar v -> Pvar v
  | Papp (ls, args) -> Papp (ls, List.map pattern_to_simple_pattern args)
  | Por (p1, p2) ->
    Por (pattern_to_simple_pattern p1, pattern_to_simple_pattern p2)
  | Pas (p, v) -> Pas (pattern_to_simple_pattern p, v)

let rec pattern_bound_vars_in_order (p : WTerm.pattern) : WTerm.vsymbol list =
  match p.pat_node with
  | Pwild -> []
  | Pvar v -> [ v ]
  | Papp (_, args) -> List.concat_map pattern_bound_vars_in_order args
  | Por (p1, p2) ->
    let vars1 = pattern_bound_vars_in_order p1 in
    let vars2 = pattern_bound_vars_in_order p2 in
    if same_vsymbol_list vars1 vars2 then vars1 else assert false
  | Pas (p, v) -> pattern_bound_vars_in_order p @ [ v ]

let rec simple_pattern_bound_vars_in_order (p : why_simple_pattern) :
    WTerm.vsymbol list =
  match p with
  | Pwild -> []
  | Pvar v -> [ v ]
  | Papp (_, args) -> List.concat_map simple_pattern_bound_vars_in_order args
  | Por (p1, p2) ->
    let vars1 = simple_pattern_bound_vars_in_order p1 in
    let vars2 = simple_pattern_bound_vars_in_order p2 in
    if same_vsymbol_list vars1 vars2 then vars1
    else
      pattern_type_error
        "or-pattern branches must bind the same variables in the same order"
  | Pas (p, v) -> simple_pattern_bound_vars_in_order p @ [ v ]

let rec simple_pattern_to_pattern expected_ty (p : why_simple_pattern) :
    WTerm.pattern =
  match p with
  | Pwild -> WTerm.pat_wild expected_ty
  | Pvar v ->
    ensure_pattern_type "pattern variable" v.vs_ty expected_ty;
    WTerm.pat_var v
  | Papp (ls, args) ->
    let result_ty =
      match ls.Why3.Term.ls_value with
      | Some ty -> ty
      | None ->
        pattern_type_error "pattern constructor %a has no result type"
          WPretty.print_ls ls
    in
    let subst =
      try WTy.ty_match WTy.Mtv.empty result_ty expected_ty
      with _ ->
        pattern_type_error
          "pattern constructor %a returns %a but is used at type %a"
          WPretty.print_ls ls WPretty.print_ty result_ty WPretty.print_ty
          expected_ty
    in
    let arg_tys = List.map (WTy.ty_inst subst) ls.Why3.Term.ls_args in
    if List.length args <> List.length arg_tys then
      pattern_type_error
        "pattern constructor %a expects %d arguments but got %d"
        WPretty.print_ls ls (List.length arg_tys) (List.length args);
    let args = List.map2 simple_pattern_to_pattern arg_tys args in
    WTerm.pat_app ls args expected_ty
  | Por (p1, p2) ->
    WTerm.pat_or
      (simple_pattern_to_pattern expected_ty p1)
      (simple_pattern_to_pattern expected_ty p2)
  | Pas (p, v) ->
    ensure_pattern_type "as-pattern alias" v.vs_ty expected_ty;
    WTerm.pat_as (simple_pattern_to_pattern expected_ty p) v

let rec term_to_simple_term (tm : WTerm.term) : why_simple_term =
  match tm.t_node with
  | Tvar v -> wrap_term_attrs tm (Tvar v)
  | Tconst c -> (
    let ty =
      match tm.t_ty with
      | Some ty -> ty_to_why_simple_ty ty
      | None -> assert false
    in
    match c with
    | ConstInt _ -> wrap_term_attrs tm (Tconst (c, ty))
    | ConstReal _ -> assert false
    | ConstStr _ -> assert false)
  | Tapp (ls, args) ->
    let ty_opt =
      match tm.t_ty with
      | None -> None
      | Some ty ->
        (* let has_free_tvs = not (Why3.Ty.Stv.is_empty (Why3.Ty.ty_freevars
           Why3.Ty.Stv.empty ty)) in if has_free_tvs then None else *)
        Some (ty_to_why_simple_ty ty)
    in
    wrap_term_attrs tm (Tapp (ls, List.map term_to_simple_term args, ty_opt))
  | Tif (t1, t2, t3) ->
    wrap_term_attrs tm
      (Tif
         (term_to_simple_term t1, term_to_simple_term t2, term_to_simple_term t3))
  | Tlet (t1, tb) ->
    let v, t2 = WTerm.t_open_bound tb in
    wrap_term_attrs tm
      (Tlet (term_to_simple_term t1, v, term_to_simple_term t2))
  | Tcase (scrutinee, branches) ->
    let branches = List.map term_branch_to_simple_term branches in
    wrap_term_attrs tm (Tcase (term_to_simple_term scrutinee, branches))
  | Teps tb ->
    let v, t1 = WTerm.t_open_bound tb in
    wrap_term_attrs tm (Teps (v, term_to_simple_term t1))
  | Tquant (q, qb) ->
    let vs, trig, body = WTerm.t_open_quant qb in
    let tr = List.map (List.map term_to_simple_term) trig in
    let body =
      let body = term_to_simple_term body in
      match tr with
      | [] -> body
      | _ -> Ttrigger (tr, body)
    in
    let rec mk_chain = function
      | [] -> body
      | w :: ws -> Tquant (q, w, mk_chain ws)
    in
    wrap_term_attrs tm (mk_chain vs)
  | Tbinop (op, t1, t2) ->
    wrap_term_attrs tm
      (Tbinop (op, term_to_simple_term t1, term_to_simple_term t2))
  | Tnot t1 -> wrap_term_attrs tm (Tnot (term_to_simple_term t1))
  | Ttrue -> wrap_term_attrs tm Ttrue
  | Tfalse -> wrap_term_attrs tm Tfalse

and term_branch_to_simple_term (branch : WTerm.term_branch) : why_simple_branch
    =
  let pattern, term = WTerm.t_open_branch branch in
  let branch =
    Branch (pattern_to_simple_pattern pattern, term_to_simple_term term)
  in
  List.fold_right
    (fun v acc -> Babs (v, acc))
    (pattern_bound_vars_in_order pattern)
    branch

let apply_attrs attrs term =
  match attrs with
  | [] -> term
  | _ -> WTerm.t_attr_set (sattr_of_attrs attrs) term

let rec simple_term_to_term (st : why_simple_term) : WTerm.term =
  let simple_trigger_to_trigger (tr : why_simple_term list list) : WTerm.trigger
      =
    List.map (List.map simple_term_to_term) tr
  in
  let split_trigger_carrier = function
    | Ttrigger (tr, body) -> (tr, body)
    | body -> ([], body)
  in
  let rec consume_quant_cont q = function
    | Tquant (q1, v, t) when q1 = q ->
      let vs, body = consume_quant_cont q t in
      (v :: vs, body)
    | t -> ([], t)
  in
  match st with
  | Tvar v -> WTerm.t_var v
  | Tattr (attrs, st) -> apply_attrs attrs (simple_term_to_term st)
  | Tconst (c, ty) -> WTerm.t_const c (why_simple_ty_to_ty ty)
  | Tapp (ls, args, ty_opt) -> (
    let targs = List.map simple_term_to_term args in
    match ty_opt with
    | None -> WTerm.t_app_infer ls targs
    | Some ty -> (
      try WTerm.t_app ls targs (Some (why_simple_ty_to_ty ty))
      with _ -> WTerm.t_app_infer ls targs))
  | Tlet (t1, v, t2) ->
    WTerm.t_let_close v (simple_term_to_term t1) (simple_term_to_term t2)
  | Ttrigger _ ->
    pattern_type_error "ttrigger must appear directly under a quantifier binder"
  | Tquant (q, v, t) ->
    let tail_vs, body = consume_quant_cont q t in
    let trig, body = split_trigger_carrier body in
    let qbound =
      WTerm.t_close_quant (v :: tail_vs)
        (simple_trigger_to_trigger trig)
        (simple_term_to_term body)
    in
    WTerm.t_quant q qbound
  | Teps (v, t) -> WTerm.t_eps_close v (simple_term_to_term t)
  | Ttrue -> WTerm.t_true
  | Tfalse -> WTerm.t_false
  | Tbinop (op, t1, t2) ->
    WTerm.t_binary op (simple_term_to_term t1) (simple_term_to_term t2)
  | Tif (t1, t2, t3) ->
    WTerm.t_if (simple_term_to_term t1) (simple_term_to_term t2)
      (simple_term_to_term t3)
  | Tnot t -> WTerm.t_not (simple_term_to_term t)
  | Tcase (t, branches) ->
    let t = simple_term_to_term t in
    let scrutinee_ty =
      match t.t_ty with
      | Some ty -> ty
      | None -> pattern_type_error "case scrutinee has no type"
    in
    let rec open_simple_branch binders = function
      | Babs (v, branch) -> open_simple_branch (v :: binders) branch
      | Branch (pattern, body) -> (List.rev binders, pattern, body)
    in
    let simple_branch_to_term_branch branch =
      let binders, pattern, body = open_simple_branch [] branch in
      let pattern_vars = simple_pattern_bound_vars_in_order pattern in
      if not (same_vsymbol_list binders pattern_vars) then
        pattern_type_error
          "branch binders must match the pattern variables in left-to-right \
           order";
      let pattern = simple_pattern_to_pattern scrutinee_ty pattern in
      let body = simple_term_to_term body in
      WTerm.t_close_branch pattern body
    in
    WTerm.t_case t (List.map simple_branch_to_term_branch branches)

let rec decl_body_of_open_term vars body =
  match vars with
  | [] -> Dterm (term_to_simple_term body)
  | v :: vs -> Dabs (v, decl_body_of_open_term vs body)

let rec decl_body_to_open_term = function
  | Dterm t -> ([], simple_term_to_term t)
  | Dabs (v, body) ->
    let vars, term = decl_body_to_open_term body in
    (v :: vars, term)

let simple_term :
    'c 'csts. (why_simple_term, 'c, 'csts) Elpi.API.ContextualConversion.t =
  let open Elpi.API.ContextualConversion in
  { ty = TyName "term"
  ; pp_doc = why_simple_term.pp_doc
  ; pp = pp_simple_term
  ; embed = elpi_embed_why_simple_term
  ; readback = elpi_readback_why_simple_term
  }

let term : 'c 'csts. (WTerm.term, 'c, 'csts) Elpi.API.ContextualConversion.t =
  let open Elpi.API.ContextualConversion in
  let kind = TyName "term" in
  { ty = kind
  ; pp_doc = why_simple_term.pp_doc
  ; pp = WPretty.print_term
  ; embed =
      (fun ~depth h c s t ->
        elpi_embed_why_simple_term ~depth h c s (term_to_simple_term t))
  ; readback =
      (fun ~depth h c s t ->
        let a, b, c =
          try elpi_readback_why_simple_term ~depth h c s t
          with exn ->
            Format.eprintf "why3-elpi raw->simple term readback failed: %s\n%!"
              (Printexc.to_string exn);
            Format.eprintf "why3-elpi term raw: %a\n%!"
              (Elpi.API.RawPp.term depth)
              t;
            raise exn
        in
        try (a, simple_term_to_term b, c)
        with exn ->
          Format.eprintf "why3-elpi simple->why3 term conversion failed: %s\n%!"
            (Printexc.to_string exn);
          Format.eprintf "why3-elpi simple term: %a\n%!" pp_simple_term b;
          raise exn)
  }

type why_term = WTerm.term

let why_term = term

type local_symbol_decl =
  | Symbol_param
  | Symbol_logic of decl_body
[@@deriving elpi { declaration; context = [ ctx_for_term; ctx_for_lsymbol ] }]
[@@elpi.type_code "local-symbol-decl"]
[@@elpi.type_doc
  "Local symbol declarations. Use symbol-param for an uninterpreted local \
   symbol and symbol-logic for a defined local body."]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<local-symbol-decl>"]

type focused_goal =
  | Goal_formula of WTerm.prsymbol * why_simple_term
  | Local_symbol of
      WTerm.lsymbol
      * (local_symbol_decl
        [@elpi.binder "term" ctx_for_lsymbol (fun ls -> Ctx_ls ls)])
      * (focused_goal
        [@elpi.binder "term" ctx_for_lsymbol (fun ls _decl -> Ctx_ls ls)])
  | Local_prop of string * why_simple_term * focused_goal
  | Local_type of tysymbol * focused_goal
[@@deriving elpi { declaration; context = [ ctx_for_term; ctx_for_lsymbol ] }]
[@@elpi.type_code "focused-goal"]
[@@elpi.type_doc
  "Focused Why3 goal: a goal formula together with its original goal symbol, \
   plus optional local symbol declarations, local proposition declarations, \
   and local type declarations to reify as declarations during readback."]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<focused-goal>"]

let goal_decl_to_focused_goal (decl : Why3.Decl.decl) : focused_goal option =
  match decl.Why3.Decl.d_node with
  | Why3.Decl.Dprop (Why3.Decl.Pgoal, pr, term) ->
    Some (Goal_formula (pr, term_to_simple_term term))
  | _ -> None

let decl_body_to_term (body : decl_body) : WTerm.term =
  let vars, term = decl_body_to_open_term body in
  match vars with
  | [] -> term
  | _ -> WTerm.t_lambda vars [] term

let rec focused_goal_to_tdecls (goal : focused_goal) : Why3.Theory.tdecl list =
  match goal with
  | Goal_formula (pr, concl) ->
    [ Why3.Theory.create_decl
        (Why3.Decl.create_prop_decl Why3.Decl.Pgoal pr
           (simple_term_to_term concl))
    ]
  | Local_symbol (ls, decl, body) ->
    let local_decl =
      match decl with
      | Symbol_param -> Why3.Decl.create_param_decl ls
      | Symbol_logic def ->
        let term = decl_body_to_term def in
        let logic_decl = Why3.Decl.make_ls_defn ls [] term in
        Why3.Decl.create_logic_decl [ logic_decl ]
    in
    Why3.Theory.create_decl local_decl :: focused_goal_to_tdecls body
  | Local_prop (name, premise, body) ->
    let pr = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name) in
    Why3.Theory.create_decl
      (Why3.Decl.create_prop_decl Why3.Decl.Paxiom pr
         (simple_term_to_term premise))
    :: focused_goal_to_tdecls body
  | Local_type (ts, body) ->
    Why3.Theory.create_decl (Why3.Decl.create_ty_decl ts)
    :: focused_goal_to_tdecls body

let lsymbol = WTerm.lsymbol
let vsymbol = WTerm.vsymbol
let prsymbol = WTerm.prsymbol
