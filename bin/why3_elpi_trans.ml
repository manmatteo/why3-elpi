open Why3
open Elpi
open Why3_elpi

let why3_transform_declarations =  fun (e : Env.env) ->
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInPredicate in
  let open Elpi.API.BuiltInPredicate.Notation in
    [ LPDoc {|Predicates for building Why3 transformations|};
      MLCode
      ( Pred ( "why3.get-env",
            Out  (env, "E",
            Easy "Get the environment in which the transformation is called" ),
            fun _ ~depth:_ -> !: (e)),
        DocAbove );
  LPCode {|type transform string -> list tdecl -> list (list tdecl) -> prop.|}]

let debug_no_typecheck = Debug.register_flag ~desc:"Disable typechecking for Elpi transformations" "no_elpi_tc"

let query (arg: string) (e: Env.env) (t : Task.task) =
  let transform_builtins = why3_builtin_declarations @ why3_transform_declarations e in
  document transform_builtins;
  let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi" (transform_builtins @ Elpi.Builtin.std_declarations)] in
  let elpi = (API.Setup.init ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
  let loc = Elpi.API.Ast.Loc.initial "(elpi)" in
  let ast = Elpi.API.Parse.program ~elpi ~files:["transform.elpi"] in
  let prog =
    let flags = Elpi.API.Compile.default_flags in
    ast |>
    Elpi.API.Compile.unit ~flags ~elpi |>
    (fun u -> Elpi.API.Compile.assemble ~elpi ~flags [u]) in
  let main_query = API.Query.compile prog loc (API.Query.Query {predicate = "transform"; arguments = (D(API.BuiltInData.string, arg, D(task,t,Q(Elpi.API.BuiltInData.list task,"Output",N))))}) in
  if not (Debug.test_flag debug_no_typecheck) && not (Elpi.API.Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) main_query)
    then Loc.errorm "elpi: type error in file"
  else
  let out_task =
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize main_query) with
  | Elpi.API.Execute.Success { output = (tm, ()); _ } ->
    Format.printf "elpi: success\n%!" ; tm
  | Failure -> Loc.errorm "elpi: failure"
  | NoMoreSteps -> assert false
  in
  out_task

exception Arg_parse_type_error of Loc.position * string * exn

let build_quotation (naming_table: Trans.naming_table)  : Elpi.API.Quotation.quotation = 
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
   in let st, t, _ = term.embed ~depth st tm
   in st, t

let elpi_trans : Trans.trans_with_args_l = 
  fun argl env naming_table _name  ->
  let () = API.Quotation.set_default_quotation (build_quotation naming_table) in
  match argl with
  | [arg] -> (Trans.store (query arg env))
  | _ -> Loc.errorm "elpi: wrong number of arguments"

(* let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command" *)
let () = Trans.register_transform_with_args_l "lp" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"