let declaration = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

let pp_tctx _ _ = ()
type tctx = Entry of (string[@elpi.key])
  [@@elpi.index (module String) "term"]
[@@deriving elpi { declaration }]

let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var tctx]
  | App of term * term
  | Lam of string * (term[@elpi.binder "term" tctx (fun s -> Entry s)])
[@@deriving elpi { declaration }]

let builtin =
  let open Elpi.API.BuiltIn in
  Elpi.API.BuiltIn.declare ~file_name:(Sys.argv.(1)) !declaration

let main () =
  Elpi.API.BuiltIn.document_file builtin;
  exit 0

let () = main ()
