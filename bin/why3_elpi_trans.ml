open Why3
open Elpi
open Why3_elpi
let query (arg: string) (t : Task.task) =
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
  let main_query = API.Query.compile prog loc (API.Query.Query {predicate = "transform"; arguments = (D(API.BuiltInData.string, arg, D(task,t,Q(task,"Output",N))))}) in
  if not (Elpi.API.Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) main_query)
    then Loc.errorm "elpi: type error in file"
  else
  let out_decl_list =
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize main_query) with
  | Elpi.API.Execute.Success { output = (tm, ()); _ } ->
    Format.printf "elpi: success\n%!" ; tm
  | Failure -> Loc.errorm "elpi: failure"
  | NoMoreSteps -> assert false
  in
  out_decl_list

let elpi_trans : Trans.trans_with_args = 
  fun argl _env _namtab _name  ->
    match argl with
    | [arg] -> (Trans.store (query arg))
    | _ -> Loc.errorm "elpi: wrong number of arguments"

(* let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command" *)
let () = Trans.register_transform_with_args "lp" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"