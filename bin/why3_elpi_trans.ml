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

let _debug_no_typecheck = Debug.register_flag ~desc:"Disable typechecking for Elpi transformations" "no_elpi_tc"

let query (arg: string) (_e: Env.env) quotations (t : Task.task) =
  let transform_builtins = declaration @ why3_builtin_declarations in
  document transform_builtins;
  let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi" (transform_builtins @ Elpi.Builtin.std_declarations)] in
  let elpi = (API.Setup.init ~quotations ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
  let ast = Elpi.API.Parse.program ~elpi ~files:["transform.elpi"] in
  let prog = Elpi.API.Compile.program ~elpi [ast] in
  let transform_c = Elpi.API.RawData.Constants.declare_global_symbol "transform" in
  let main_query = Elpi.API.RawQuery.compile_raw_term prog (fun state ->
    let depth = 0 in
    let state, arg_t, eg1 = Elpi.API.BuiltInData.string.embed ~depth state arg in
    let state, task_t, eg2 = task.embed ~depth [] Elpi.API.RawData.no_constraints state t in
    let state, output_uvar = Elpi.API.FlexibleData.Elpi.make ~name:"Output" state in
    let output_t = Elpi.API.RawData.mkUnifVar output_uvar ~args:[] state in
    let query_term = Elpi.API.RawData.mkAppGlobalL transform_c [arg_t; task_t; output_t] in
    (state, query_term, eg1 @ eg2)) in
  let out_task =
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize main_query) with
  | Elpi.API.Execute.Success { assignments; state; _ } ->
    let output_term = Elpi.API.Data.StrMap.find "Output" assignments in
    let _st, tm, _eg = (Elpi_api_compat.BuiltInContextualData.list task).readback ~depth:0 [] Elpi.API.RawData.no_constraints state output_term in
    Format.printf "elpi: success\n%!" ; tm
  | Failure -> Loc.errorm "elpi: failure"
  | NoMoreSteps -> assert false
  in
  out_task

let why3_quot_from_naming (naming_table: Trans.naming_table)  : Elpi.API.Quotation.quotation = 
  fun ~language:_ _st _loc text ->
   let _ = naming_table in
   failwith ("why3 quotations are not yet ported to mainline ELPI: " ^ text)

let elpi_trans : Trans.trans_with_args_l = 
  fun argl env naming_table _name  ->
  let quot = API.Quotation.new_quotations_descriptor () in
  let why3_quot = why3_quot_from_naming naming_table in
  let () = API.Quotation.set_default_quotation why3_quot ~descriptor:quot in
  let _ = API.Quotation.register_named_quotation ~name:"why3" why3_quot ~descriptor:quot in
  match argl with
  | [arg] -> (Trans.store (query arg env quot))
  | _ -> Loc.errorm "elpi: wrong number of arguments"

(* let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command" *)
let () = Trans.register_transform_with_args_l "lp" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"
