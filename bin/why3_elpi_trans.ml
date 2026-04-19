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

let transform_program_file () =
  match Sys.getenv_opt "WHY3_ELPI_PROGRAM" with
  | Some path when path <> "" -> path
  | _ -> "transform.elpi"
let transform_c = Elpi.API.RawData.Constants.declare_global_symbol "w3_transform"

let cached_program : (string * Elpi.API.Setup.elpi * Elpi.API.Compile.program) option ref = ref None

let get_program ~quotations ~builtins =
  let file = transform_program_file () in
  match !cached_program with
  | Some (cached_file, elpi, prog) when cached_file = file -> (elpi, prog)
  | _ ->
      let elpi = (API.Setup.init ~quotations ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
      let ast = Elpi.API.Parse.program ~elpi ~files:[file] in
      let prog = Elpi.API.Compile.program ~elpi [ast] in
      cached_program := Some (file, elpi, prog);
      (elpi, prog)

let collect_list_terms ~depth tm =
  let rec aux tm =
    match Elpi.API.RawData.look ~depth tm with
    | Elpi.API.RawData.Nil -> Some []
    | Elpi.API.RawData.Cons (hd, tl) ->
        begin match aux tl with
        | Some tl_terms -> Some (hd :: tl_terms)
        | None -> None
        end
    | _ -> None
  in
  aux tm

let read_output_tasks conv state output_term =
  let read_all () =
    (Elpi_api_compat.BuiltInContextualData.list conv).readback
      ~depth:0 [] Elpi.API.RawData.no_constraints state output_term
  in
  try
    let _st, tm, _eg = read_all () in
    Format.printf "elpi: success\n%!";
    tm
  with exn ->
    Format.eprintf "elpi: output readback failed: %s\n%!" (Printexc.to_string exn);
    Format.eprintf "elpi: output raw term: %a\n%!" (Elpi.API.RawPp.term 0) output_term;
    begin match collect_list_terms ~depth:0 output_term with
    | None ->
        Format.eprintf "elpi: output is not a proper list term\n%!"
    | Some tasks ->
        List.iteri
          (fun i task_tm ->
            try
              let _st, _task, _eg = conv.readback ~depth:0 [] Elpi.API.RawData.no_constraints state task_tm in
              ()
            with task_exn ->
              Format.eprintf "elpi: failing transformed task at index %d: %s\n%!"
                i (Printexc.to_string task_exn);
              Format.eprintf "elpi: failing transformed task raw:@. %a\n%!"
                (Elpi.API.RawPp.term 0) task_tm)
          tasks
    end;
    raise exn

let run_query_with prog build_query output_conv =
  let main_query = Elpi.API.RawQuery.compile_raw_term prog build_query in
  match Elpi.API.Execute.once (Elpi.API.Compile.optimize main_query) with
  | Elpi.API.Execute.Success { assignments; state; _ } ->
    let output_term = Elpi.API.Data.StrMap.find "Output" assignments in
    Some (read_output_tasks output_conv state output_term)
  | Failure -> None
  | NoMoreSteps -> assert false

let query (arg: string) (_e: Env.env) quotations (t : Task.task) =
  let transform_decl =
    Elpi.API.BuiltIn.LPCode
      {|external symbol w3_transform : string -> list tdecl -> focused-goal -> list focused-task -> prop.|}
  in
  let transform_builtins = declaration @ why3_builtin_declarations @ [transform_decl] in
  document transform_builtins;
  let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi" (transform_builtins @ Elpi.Builtin.std_declarations)] in
  let _elpi, prog = get_program ~quotations ~builtins in
  match split_focused_goal t with
  | None -> Loc.errorm "elpi: focused transform interface requires a task with a goal"
  | Some (rest, goal) ->
      match run_query_with prog (fun state ->
        let depth = 0 in
        let state, arg_t, eg1 = Elpi.API.BuiltInData.string.embed ~depth state arg in
        let state, rest_t, eg2 =
          (Elpi_api_compat.BuiltInContextualData.list tdecl).embed
            ~depth [] Elpi.API.RawData.no_constraints state rest in
        let state, goal_t, eg3 = focused_goal.embed ~depth [] Elpi.API.RawData.no_constraints state goal in
        let state, output_uvar = Elpi.API.FlexibleData.Elpi.make ~name:"Output" state in
        let output_t = Elpi.API.RawData.mkUnifVar output_uvar ~args:[] state in
        let query_term = Elpi.API.RawData.mkAppGlobalL transform_c [arg_t; rest_t; goal_t; output_t] in
        (state, query_term, eg1 @ eg2 @ eg3)) focused_task with
      | Some out_task -> out_task
      | None -> Loc.errorm "elpi: failure"

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
