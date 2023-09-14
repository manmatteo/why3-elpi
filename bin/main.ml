open Why3
open Elpi

let types = ref [||]

let declarations =
  let open Elpi.API.BuiltIn in
  let open Elpi.API.BuiltInData in
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
  | Success(data) ->
    (* Elpi returns answers as a map from query variable names to terms *)
    (* We transform it into a map from names to strings *)
    let resp =
      Elpi.API.Data.StrMap.map (fun term ->
          Elpi.API.Pp.term (data.pp_ctx) (Format.str_formatter) term;
          Format.flush_str_formatter ())
        data.assignments
    in
    Elpi.API.Data.StrMap.iter (fun var bind -> Format.printf "%s: %s" var bind) resp;
  | _ -> ()
let query decl =
    let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi"
    (declarations @ Elpi.Builtin.std_declarations)] in
    let elpi = (API.Setup.init ~builtins ()) in
    let goal = Elpi.API.Parse.goal ~loc:(Elpi.API.Ast.Loc.initial "mlts") ~elpi ~text:"why_foo" in
    let prog = Elpi.API.Compile.program [] ~elpi in
    let goalc = Elpi.API.Compile.query prog goal in
    let exec = Elpi.API.Compile.optimize goalc in
    let () = Elpi.API.Execute.loop exec
      ~more:(fun () -> true)
      ~pp:handle_out
  in [decl]


let elpi_trans = Trans.decl query None

let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"