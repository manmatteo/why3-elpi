(* Custom types running through the PPX *)
open Ty
open Common
module WIdent = Why3.Ident
module WPretty = Why3.Pretty
module WTy = Why3.Ty
let declaration = Ty.declaration

module WTerm  =
struct
include Why3.Term
    let elpi_constant_type_vsymbol = "vsymbol"
    let elpi_constant_type_vsymbolc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_vsymbol
    let elpi_opaque_data_decl_vsymbol = Elpi.API.OpaqueData.declare
        { Elpi.API.OpaqueData.name = "var";
          doc = "Embedding of variable symbols";
          pp = (pp_why_ident Why3.Pretty.print_vs);
          compare = vs_compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = [] }
    module Ctx_for_vsymbol =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let vsymbol : 'c .  (vsymbol, #Elpi.API.ContextualConversion.ctx as 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_vsymbol in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = vsymbol
    let elpi_embed_vsymbol = vsymbol.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_vsymbol
    let elpi_readback_vsymbol =
      vsymbol.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_vsymbol
    let elpi_vsymbol = Elpi.API.BuiltIn.MLDataC vsymbol
    let _ = elpi_vsymbol
    class ctx_for_vsymbol (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_vsymbol.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_vsymbol :
      (Ctx_for_vsymbol.t, 'csts) Elpi.API.ContextualConversion.ctx_readback)
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_vsymbol) h s), c, (List.concat []))
    let _ = in_ctx_for_vsymbol
    let () = declaration := ((!declaration) @ [elpi_vsymbol])

    let elpi_constant_type_lsymbol = "lsymbol"
    let _ = elpi_constant_type_lsymbol
    let elpi_constant_type_lsymbolc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_lsymbol
    let _ = elpi_constant_type_lsymbolc
    let elpi_opaque_data_decl_lsymbol =
      Elpi.API.OpaqueData.declare
        {
          Elpi.API.OpaqueData.name = "lsymbol";
          doc =
            "Embedding of predicate symbols. Name, argument and value type can be accessed via native predicates.";
          pp = (pp_why_data Why3.Pretty.print_ls);
          compare = ls_compare;
          hash = ls_hash;
          hconsed = false;
          constants = [("infix_at", fs_func_app)]
        }
    let _ = elpi_opaque_data_decl_lsymbol
    module Ctx_for_lsymbol =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let lsymbol :
      'c .
        (lsymbol, #Elpi.API.ContextualConversion.ctx as 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_lsymbol in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = lsymbol
    let elpi_embed_lsymbol = lsymbol.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_lsymbol
    let elpi_readback_lsymbol =
      lsymbol.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_lsymbol
    let elpi_lsymbol = Elpi.API.BuiltIn.MLDataC lsymbol
    let _ = elpi_lsymbol
    class ctx_for_lsymbol (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_lsymbol.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_lsymbol :
      (Ctx_for_lsymbol.t, 'csts) Elpi.API.ContextualConversion.ctx_readback)
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_lsymbol) h s), c, (List.concat []))
    let _ = in_ctx_for_lsymbol
    let () = declaration := ((!declaration) @ [elpi_lsymbol])

    let elpi_constant_type_quant = "quant"
    let elpi_constant_type_quantc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_quant
    let elpi_constant_constructor_quant_Tforall = "tforall"
    let elpi_constant_constructor_quant_Tforallc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_quant_Tforall
    let elpi_constant_constructor_quant_Texists = "texists"
    let elpi_constant_constructor_quant_Texistsc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_quant_Texists
    module Ctx_for_quant =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_quant : 'c 'csts .  (quant, #Ctx_for_quant.t as 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth -> fun elpi__hyps -> fun elpi__constraints -> fun elpi__state ->
              function
              | Tforall -> (elpi__state, (Elpi.API.RawData.mkAppL elpi_constant_constructor_quant_Tforallc []), (List.concat []))
              | Texists -> (elpi__state, (Elpi.API.RawData.mkAppL elpi_constant_constructor_quant_Texistsc []), (List.concat []))
    and elpi_readback_quant : 'c 'csts .  (quant, #Ctx_for_quant.t as 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth -> fun elpi__hyps -> fun elpi__constraints -> fun elpi__state -> fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when elpi__hd == elpi_constant_constructor_quant_Tforallc -> (elpi__state, Tforall, [])
                | Elpi.API.RawData.Const elpi__hd when elpi__hd == elpi_constant_constructor_quant_Texistsc -> (elpi__state, Texists, [])
                | _ -> Elpi.API.Utils.type_error (Format.asprintf "Not a constructor of type %s: %a" "quant" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and quant : 'c 'csts .  (quant, #Ctx_for_quant.t as 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "quant" in {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc = (fun fmt -> fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"quant";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tforall" ~doc:"Tforall" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"texists" ~doc:"Texists" ~args:[]);
        pp = (fun fmt ->
             function
             | Tforall -> Format.fprintf fmt "\226\136\128"
             | Texists -> Format.fprintf fmt "\226\136\131");
        embed = elpi_embed_quant;
        readback = elpi_readback_quant
      }
    let elpi_quant = Elpi.API.BuiltIn.MLDataC quant
    class ctx_for_quant (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state) : Ctx_for_quant.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_quant : (Ctx_for_quant.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth -> fun h -> fun c -> fun s -> (s, ((new ctx_for_quant) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_quant])

    let elpi_constant_type_binop = "binop"
    let elpi_constant_type_binopc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_binop
    let elpi_constant_constructor_binop_Tand = "tand"
    let elpi_constant_constructor_binop_Tandc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_binop_Tand
    let elpi_constant_constructor_binop_Tor = "tor"
    let elpi_constant_constructor_binop_Torc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_binop_Tor let elpi_constant_constructor_binop_Timplies = "timplies"
    let elpi_constant_constructor_binop_Timpliesc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_binop_Timplies
    let elpi_constant_constructor_binop_Tiff = "tiff"
    let elpi_constant_constructor_binop_Tiffc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_binop_Tiff
    module Ctx_for_binop =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_binop : 'c 'csts .  (binop, #Ctx_for_binop.t as 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state ->
              function
              | Tand -> (elpi__state, (Elpi.API.RawData.mkAppL elpi_constant_constructor_binop_Tandc []), (List.concat []))
              | Tor -> (elpi__state, (Elpi.API.RawData.mkAppL elpi_constant_constructor_binop_Torc []), (List.concat []))
              | Timplies -> (elpi__state, (Elpi.API.RawData.mkAppL elpi_constant_constructor_binop_Timpliesc []), (List.concat []))
              | Tiff -> (elpi__state, (Elpi.API.RawData.mkAppL elpi_constant_constructor_binop_Tiffc []), (List.concat []))
    and elpi_readback_binop : 'c 'csts .  (binop, #Ctx_for_binop.t as 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when elpi__hd == elpi_constant_constructor_binop_Tandc -> (elpi__state, Tand, [])
                | Elpi.API.RawData.Const elpi__hd when elpi__hd == elpi_constant_constructor_binop_Torc -> (elpi__state, Tor, [])
                | Elpi.API.RawData.Const elpi__hd when elpi__hd == elpi_constant_constructor_binop_Timpliesc -> (elpi__state, Timplies, [])
                | Elpi.API.RawData.Const elpi__hd when elpi__hd == elpi_constant_constructor_binop_Tiffc -> (elpi__state, Tiff, [])
                | _ -> Elpi.API.Utils.type_error (Format.asprintf "Not a constructor of type %s: %a" "binop" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and binop : 'c 'csts .  (binop, #Ctx_for_binop.t as 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "binop" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"binop";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tand" ~doc:"Tand" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tor" ~doc:"Tor" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"timplies" ~doc:"Timplies" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tiff" ~doc:"Tiff" ~args:[]);
        pp = (fun fmt -> function | Tand -> Format.fprintf fmt "/\\" | Tor -> Format.fprintf fmt "\\/" | Timplies -> Format.fprintf fmt "=>" | Tiff -> Format.fprintf fmt "<=>");
        embed = elpi_embed_binop;
        readback = elpi_readback_binop
      }
    let elpi_binop = Elpi.API.BuiltIn.MLDataC binop
    class ctx_for_binop (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state) : Ctx_for_binop.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_binop : (Ctx_for_binop.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth h c s -> (s, ((new ctx_for_binop) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_binop])
end

module Ident_tags = struct
  open Why3.Ident
  type t = ident
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let pp = fun fmt x -> Format.fprintf fmt "`%s`" x.id_string
  let show = fun x -> x.id_string
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

(* type ctx_for_term =
  | Dctx_ts of (ident[@elpi.key]) * tysymbol
  | Dctx_ls of (ident[@elpi.key]) * lsymbol
[@@elpi.index (module Ident_tags)] *)

type ctx_for_term =
| Dctx_vs of (WTerm.vsymbol[@elpi.key]) * WTerm.lsymbol
[@@elpi.index (module Vsym_tags)]
[@@deriving elpi {declaration}]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<term_context>"]
let pp_ctx_for_term = fun fmt c -> ctx_for_term.pp fmt (0,c)

(* let var_to_ctx_entry (v:vsymbol) : ctx_for_term =
  let id = v.vs_name in
  let ls = create_lsymbol (id_clone id) [] (Some v.vs_ty) in
  Dctx_ls (id, ls) *)

let ctx_entry_to_var (c:ctx_for_term) : WTerm.vsymbol =
  match c with
  | Dctx_vs (v, _ls) -> v
    (* (match ls.ls_value with
    | Some t -> create_vsymbol (id_clone id) t
    |_ -> assert false) *)

type why_simple_pattern =
  | Pwild
  | Pvar of WTerm.vsymbol
  | Papp of WTerm.lsymbol * why_simple_pattern list
  | Por of why_simple_pattern * why_simple_pattern
  | Pas of why_simple_pattern * WTerm.vsymbol
[@@deriving elpi {declaration}]
[@@elpi.type_code "pattern"]
[@@elpi.type_doc "Pattern constructors for pattern-matching terms."]
[@@elpi.pp fun fmt -> let rec pp fmt p = match p with
  | Pwild -> Format.fprintf fmt "_"
  | Pvar v -> Format.fprintf fmt "%a" WPretty.print_vs v
  | Papp (ls, args) -> Format.fprintf fmt "%a(%a)" WPretty.print_ls ls (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp) args
  | Por (p1, p2) -> Format.fprintf fmt "%a | %a" pp p1 pp p2
  | Pas (p, v) -> Format.fprintf fmt "%a as %a" pp p WPretty.print_vs v
  in pp fmt]

let rec pattern_to_simple_pattern (p : WTerm.pattern) : why_simple_pattern =
  match p.pat_node with
  | Pwild -> Pwild
  | Pvar v -> Pvar v
  | Papp (ls, args) -> Papp (ls, List.map pattern_to_simple_pattern args)
  | Por (p1, p2) -> Por (pattern_to_simple_pattern p1, pattern_to_simple_pattern p2)
  | Pas (p, v) -> Pas (pattern_to_simple_pattern p, v)

let rec simple_pattern_to_pattern p ty =
  let why_ty = why_simple_ty_to_ty ty in
  match p with
  | Pwild -> WTerm.pat_wild why_ty
  | Pvar v -> WTerm.pat_var v
  | Papp (ls, args) -> WTerm.pat_app ls (List.map (fun x -> simple_pattern_to_pattern x ty) args) why_ty
  | Por (p1, p2) -> WTerm.pat_or (simple_pattern_to_pattern p1 ty) (simple_pattern_to_pattern p2 ty)
  | Pas (p, v) -> WTerm.pat_as (simple_pattern_to_pattern p ty) v


type why_simple_term =
  | Tvar of WTerm.vsymbol [@elpi.var ctx_for_term]
  | Tint of int
  | Tapp of WTerm.lsymbol * why_simple_term list
  | Tquant of WTerm.quant * WTerm.vsymbol  * (why_simple_term [@elpi.binder "term" ctx_for_term (fun _q v -> Dctx_vs (v, WTerm.create_lsymbol (WIdent.id_clone v.vs_name) [] (Some v.vs_ty)))])
  | Teps of WTerm.vsymbol * (why_simple_term [@elpi.binder "term" ctx_for_term (fun v -> Dctx_vs (v, WTerm.create_lsymbol (WIdent.id_clone v.vs_name) [] (Some v.vs_ty)))])
  | Ttrue | Tfalse
  | Tbinop of WTerm.binop * why_simple_term * why_simple_term
  | Tnot of why_simple_term
  | Tcase of why_simple_term * why_simple_ty * (why_simple_pattern * why_simple_term) list
  (* Explicit binders in pattern matching *)
  | Pabs of WTerm.vsymbol * (why_simple_term [@elpi.binder "term" ctx_for_term (fun v -> Dctx_vs (v, WTerm.create_lsymbol (WIdent.id_clone v.vs_name) [] (Some v.vs_ty)))])
[@@deriving elpi {declaration}]
[@@elpi.type_code "term"]
[@@elpi.pp fun fmt _ -> Format.fprintf fmt "<term>"]

let rec pp_simple_term = 
  fun fmt t -> match t with
  | Tvar v -> Format.fprintf fmt "%a" WPretty.print_vs v
  | Tint n -> Format.fprintf fmt "%d" n
  | Tapp (ls, args) -> Format.fprintf fmt "%a(%a)" WPretty.print_ls ls (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_simple_term) args
  | Tquant (q, v, t) -> Format.fprintf fmt "%a %a. %a" (WPretty.print_quant) q WPretty.print_vs v pp_simple_term t
  | Teps (v, t) -> Format.fprintf fmt "eps %a. %a" WPretty.print_vs v pp_simple_term t
  | Ttrue -> Format.fprintf fmt "true"
  | Tfalse -> Format.fprintf fmt "false"
  | Tbinop (op, t1, t2) -> Format.fprintf fmt "(%a %a %a)" pp_simple_term t1 (WPretty.print_binop ~asym:false) op pp_simple_term t2
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
  | Tif (_, _, _) -> assert false
  | Tlet (_, _) -> assert false
  | Tcase (t, branches) ->
    let first_pattern_type =
      match branches with
      | [] -> assert false
      | b::_ -> let (p,_) = (WTerm.t_open_branch b) in ty_to_why_simple_ty p.pat_ty in
    let branches = List.map (fun t -> term_branch_to_simple_term t) branches in Tcase (term_to_simple_term t, first_pattern_type, branches)
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
  | Tapp (ls, args) -> WTerm.t_app_infer ls (List.map simple_term_to_term args) (* Using t_app without inference might be more efficient, but I had troubles with typing @ applied to typed args*)
  | Tquant (q, v, t) -> let vs, t = consume_quant q t in WTerm.t_quant_close q (v::vs) [] (simple_term_to_term t)
  | Teps (v, t) -> WTerm.t_eps_close v (simple_term_to_term t)
  | Ttrue -> WTerm.t_true
  | Tfalse -> WTerm.t_false
  | Tbinop (op, t1, t2) -> WTerm.t_binary op (simple_term_to_term t1) (simple_term_to_term t2)
  | Tnot t -> WTerm.t_not (simple_term_to_term t)
  | Tcase (t, ty, branches) ->
    let rec strip_branch_binders = function
      | Pabs (_, t) -> strip_branch_binders t
      | t -> t
    in
    let simple_term_to_term_branch (p, t) =
      let t = strip_branch_binders t in
      let p = simple_pattern_to_pattern p ty in
      let t = simple_term_to_term t in
      WTerm.t_close_branch p t
    in
    WTerm.t_case (simple_term_to_term t) (List.map simple_term_to_term_branch branches)
  | Pabs (_, _) -> assert false (* Should only appear in branches and be consumed by the branch reconstructor *)

let term : 'c 'csts .  (WTerm.term, #Ctx_for_why_simple_term.t as 'c, 'csts) Elpi.API.ContextualConversion.t =
let open Elpi.API.ContextualConversion in
  let kind = TyName "why-simple-term" in
  {ty = kind;
   pp_doc = why_simple_term.pp_doc;
   pp = (fun fmt t -> why_simple_term.pp fmt (term_to_simple_term t));
   embed = (fun ~depth h c s t -> elpi_embed_why_simple_term ~depth h c s (term_to_simple_term t));
   readback = (fun ~depth h c s t -> let (a,b,c) = elpi_readback_why_simple_term ~depth h c s t in (a, simple_term_to_term b, c))
  }

let lsymbol = WTerm.lsymbol
let vsymbol = WTerm.vsymbol