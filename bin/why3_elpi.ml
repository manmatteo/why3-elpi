open Why3
open Elpi

let types = ref [||]

let declarations =
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInData in
  let open Elpi.API.BuiltInPredicate in
  [
    MLCode
      ( Pred
          ( "why_foo",
            Easy
              "Let's see if this works",
            fun ~depth:_ -> () ),
        DocAbove );
    MLCode
      ( Pred
          ( "why_print",
            In
              ( string,
                "P",
                In
                  ( string,
                    "M",
                    Easy "Print message M with prefix P." )
              ),
            fun p m ~depth:_ -> Format.printf "%s : %s" m p ),
        DocAbove );
        MLCode
          ( Pred
              ( "js_type",
                In
                  ( list string,
                    "LN",
                        Easy
                          "js_type" ),
                fun l ~depth:_ -> match l with
                | name::typ::[] when Array.mem name !types ->
                  Format.eprintf "Type: %s %s\n%!" name typ;
                | _ -> ()
                  ),
            DocAbove );]
 
 
let handle_out _f (out : unit Elpi.API.Execute.outcome) =
  match out with
  | Elpi.API.Execute.Success(data) ->
    (* Elpi returns answers as a map from query variable names to terms *)
    (* We transform it into a map from names to strings *)
    let resp =
      let open Elpi.API.Data in
      StrMap.map (fun term ->
          Elpi.API.Pp.term (data.pp_ctx) (Format.str_formatter) term;
          Format.flush_str_formatter ())
        data.assignments
    in
    Elpi.API.Data.StrMap.iter (fun var bind -> Format.printf "%s: %s" var bind) resp;
  | _ -> ()

let query (decl : Decl.decl) =
    let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi"
    (declarations @ Elpi.Builtin.std_declarations)] in
    let elpi = (API.Setup.init ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
    let loc = Elpi.API.Ast.Loc.initial "(elpi)" in
    let ast = Elpi.API.Parse.program ~elpi ~files:["test.elpi"] in
    let prog =
      let flags = Elpi.API.Compile.default_flags in
      ast |>
      Elpi.API.Compile.unit ~flags ~elpi |>
      (fun u -> Elpi.API.Compile.assemble ~elpi ~flags [u]) in
    let parsed_query = Elpi.API.(Parse.goal ~elpi ~loc:(Ast.Loc.initial "") ~text:"why_foo.") in
    let compiled_query = Elpi.API.Compile.query prog parsed_query in
    if not (Elpi.API.Compile.static_check
              ~checker:(Elpi.Builtin.default_checker ()) compiled_query) then
      Loc.errorm "elpi: type error in file";
  
    let _ =
    match Elpi.API.Execute.once (Elpi.API.Compile.optimize compiled_query) with
    | Elpi.API.Execute.Success {
        Elpi.API.Data.state; pp_ctx; constraints; output = (); _
      } -> Format.printf "elpi: success\n%!"
    | Failure -> Loc.errorm "elpi: failure"
    | NoMoreSteps -> assert false
  in [decl]

let elpi_trans = Trans.decl query None

let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"