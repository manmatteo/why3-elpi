(* Printer for Ident-like Why3 builtins: ident, variables... These are mostly a
   layer over Ident, and can be seen as names *)
let pp_why_ident p = fun fmt x -> Format.fprintf fmt "`%a`" p x

(* Printer for Why3 names that include more content: logic symbols, data
   types... This content (typing for lsymbols, constructors for data types...)
   is accessed via builtin predicates *)
let pp_why_data p = fun fmt x -> Format.fprintf fmt "«%a»" p x
