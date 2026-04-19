open Term
module Term_conv = Term
module WTerm = Why3.Term
open Common
open Ty
open Why3
open Why3.Decl

let decl_declaration = ref []
let declaration = decl_declaration
type prsymbol = Why3.Decl.prsymbol
type lsymbol = Why3.Term.lsymbol
type tysymbol = Why3.Ty.tysymbol
type vsymbol = Why3.Term.vsymbol
let prsymbol : (prsymbol, 'a, 'b) Elpi.API.ContextualConversion.t = Term_conv.prsymbol

type logic_decl = Why3.Decl.logic_decl

type gref =
  | Gpr of prsymbol
  | Gls of lsymbol
  | Gty of tysymbol
[@@deriving elpi {declaration}]
[@@elpi.type_code "gref"]
[@@elpi.type_doc "References to Why3 global symbols defined by declarations."]
[@@elpi.pp fun fmt -> function
  | Gpr pr -> Format.fprintf fmt "pr:%a" Pretty.print_pr pr
  | Gls ls -> Format.fprintf fmt "ls:%a" Pretty.print_ls ls
  | Gty ts -> Format.fprintf fmt "ty:%a" Pretty.print_ts ts]

type decl_kind =
  | Decl_prop
  | Decl_type
  | Decl_data
  | Decl_ind
  | Decl_logic
  | Decl_param
[@@deriving elpi {declaration}]
[@@elpi.type_code "decl-kind"]
[@@elpi.type_doc "Classification of Why3 declarations returned by why3.decl-kind."]
[@@elpi.pp fun fmt -> function
  | Decl_prop -> Format.fprintf fmt "prop"
  | Decl_type -> Format.fprintf fmt "type"
  | Decl_data -> Format.fprintf fmt "data"
  | Decl_ind -> Format.fprintf fmt "ind"
  | Decl_logic -> Format.fprintf fmt "logic"
  | Decl_param -> Format.fprintf fmt "param"]

type decl_body = Term_conv.decl_body =
  | Dterm of why_simple_term
  | Dabs of vsymbol * decl_body

let decl_body = Term_conv.decl_body

type decl = Why3.Decl.decl
[@@elpi.opaque {
  name = "decl";
  pp = (pp_why_data Pretty.print_decl);
  doc = "Opaque Why3 declaration. Inspect it with why3.decl-kind, why3.decl-defines, and why3.decl-body.";
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}]
[@@deriving elpi {declaration}]

let logic_decl_lsymbol ((ls, _) : logic_decl) =
  ls

let decl_body_of_logic_decl ((_, def) : logic_decl) =
  let vars, body = Decl.open_ls_defn def in
  Term_conv.decl_body_of_open_term vars body

let decl_defined_grefs (decl : Decl.decl) =
  match decl.d_node with
  | Decl.Dprop (_, pr, _) -> [Gpr pr]
  | Decl.Dtype ts -> [Gty ts]
  | Decl.Ddata ddecls ->
      List.concat_map
        (fun (ts, ctors) -> Gty ts :: List.map (fun (ls, _) -> Gls ls) ctors)
        ddecls
  | Decl.Dind (_, idecls) -> List.map (fun (ls, _) -> Gls ls) idecls
  | Decl.Dparam ls -> [Gls ls]
  | Decl.Dlogic ldecls -> List.map (fun ld -> Gls (logic_decl_lsymbol ld)) ldecls

let decl_body_of_gref (decl : Decl.decl) (ref : gref) =
  match decl.d_node, ref with
  | Decl.Dprop (_, pr, tm), Gpr pr' when Why3.Decl.pr_equal pr pr' ->
      Some (Dterm (term_to_simple_term tm))
  | Decl.Dlogic ldecls, Gls ls ->
      List.find_map
        (fun ld ->
          if WTerm.ls_compare (logic_decl_lsymbol ld) ls = 0 then
            Some (decl_body_of_logic_decl ld)
          else
            None)
        ldecls
  | _ -> None