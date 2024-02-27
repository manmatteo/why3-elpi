open Why3
open Why3.Term
open Why3.Ident
open Why3.Ty
open Why3.Env
open Why3.Decl
open Why3.Task
open Elpi
(* Printer for Why3 terms *)
(* Printer for Ident-like Why3 builtins: ident, variables...
   These are mostly a layer over Ident, and can be seen as names *)
let pp_why_ident p = fun fmt x -> Format.fprintf fmt "`%a`" p x 
(* Printer for Why3 names that include more content: logic symbols, data
   types...  This content (typing for lsymbols, constructors for data types...)
   is accessed via builtin predicates  *)
let pp_why_data p = fun fmt x -> Format.fprintf fmt "«%a»" p x 
