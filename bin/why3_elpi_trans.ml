open Why3
open Elpi
open Why3_elpi

(* let why3_transform_declarations =  fun (e : Env.env) ->
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInPredicate in
  let open Elpi.API.BuiltInPredicate.Notation in
    [ LPDoc {|Predicates for building Why3 transformations|};
      MLCode
      ( CPred ( "why3.get-env",
            Out  (env, "E",
            Easy "Get the environment in which the transformation is called" ),
            fun _ ~depth:_ -> !: (e)),
        DocAbove );
  LPCode {|type transform string -> list tdecl -> list (list tdecl) -> prop.|}] *)

let debug_no_typecheck = Debug.register_flag ~desc:"Disable typechecking for Elpi transformations" "no_elpi_tc"

class ctx_for_why_simple_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state) : Ctx_for_why_simple_term.t =
  object (_)
  inherit  ((Elpi.API.ContextualConversion.ctx) h)
  method ctx_for_term = context_made_of_ctx_for_term.get s
  end

let query (arg: string) (e: Env.env) quotations (t : Task.task) =
  let transform_builtins = declaration @ Why3_elpi_builtins.Builtins.why3_builtin_declarations in
  document transform_builtins;
  let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi" (transform_builtins @ Elpi.Builtin.std_declarations)] in
  let elpi = (API.Setup.init ~quotations ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
  let loc = Elpi.API.Ast.Loc.initial "(elpi)" in
  let ast = Elpi.API.Parse.program ~elpi ~files:["transform.elpi"] in
  let prog =
    let flags = Elpi.API.Compile.default_flags in
    ast |> Elpi.API.Compile.unit ~flags ~elpi |>
    (fun u -> Elpi.API.Compile.assemble ~elpi ~flags [u]) in
  let main_query = API.Query.CQuery ("transform", (DC(API.BuiltInContextualData.string, arg, DC(task,t,QC(Elpi.API.BuiltInContextualData.list task,"Output",NC)))), (fun s-> new ctx_for_why_simple_term [] s), ()) in
  let compiled_query = API.Query.compile prog loc main_query in
  if not (Debug.test_flag debug_no_typecheck) && not (Elpi.API.Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) compiled_query)
    then Loc.errorm "elpi: type error in file"
  else
  let out_task =
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize compiled_query) with
  | Elpi.API.Execute.Success { output = (tm, ()); _ } ->
    Format.printf "elpi: success\n%!" ; tm
  | Failure -> Loc.errorm "elpi: failure"
  | NoMoreSteps -> assert false
  in
  out_task

exception Arg_parse_type_error of Loc.position * string * exn

let why3_quot_from_naming (naming_table: Trans.naming_table)  : Elpi.API.Quotation.quotation = 
  fun ~depth st _loc text ->
   let ns = naming_table.namespace in
   let km = naming_table.known_map in
   let c = naming_table.coercion in
   (* let open Parsing in *)
   let tm = 
     try
       let lb = Lexing.from_string text in
       let t = Lexer.parse_term lb in
       Typing.type_term_in_namespace ns km c t
     with Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, text, e))
    in
   let st,ctx,csts,_eg = Why3_elpi.in_ctx_for_term ~depth [] Elpi.API.RawData.no_constraints st
   in let st, t, _ = term.embed ~depth ctx csts st tm
   in st, t

let elpi_trans : Trans.trans_with_args_l = 
  fun argl env naming_table _name  ->
  let quot = API.Quotation.new_quotations_descriptor () in
  let why3_quot = why3_quot_from_naming naming_table in
  let () = API.Quotation.set_default_quotation why3_quot ~descriptor:quot in
  let () = API.Quotation.register_named_quotation ~name:"why3" why3_quot ~descriptor:quot in
  match argl with
  | [arg] -> (Trans.store (query arg env quot))
  | _ -> Loc.errorm "elpi: wrong number of arguments"

(* let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command" *)
let () = Trans.register_transform_with_args_l "lp" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"
