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

let query (arg: string) (e: Env.env) (t : Task.task) =
  let transform_builtins = declaration in
  document transform_builtins;
  let builtins = [Elpi.API.BuiltIn.declare ~file_name:"builtins.elpi" (transform_builtins @ Elpi.Builtin.std_declarations)] in
  let elpi = (API.Setup.init ~builtins ~file_resolver:(Elpi.API.Parse.std_resolver ~paths:[] ()) ()) in
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

(* let build_quotation (naming_table: Trans.naming_table)  : Elpi.API.Quotation.quotation = 
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
   in st, t *)

let elpi_trans : Trans.trans_with_args_l = 
  fun argl env naming_table _name  ->
  (* let () = API.Quotation.set_default_quotation (build_quotation naming_table) in *)
  match argl with
  | [arg] -> (Trans.store (query arg env))
  | _ -> Loc.errorm "elpi: wrong number of arguments"

(* let () = Trans.register_transform "elpi_query" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command" *)
let () = Trans.register_transform_with_args_l "lp" elpi_trans
~desc:"Run@ a@ simple@ elpi@ command"

(* module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show x = x
  end
module Elpi_ctx_Map = (Elpi.API.Utils.Map.Make)(String)
let elpi_ctx_state =
  Elpi.API.State.declare_component ~name:"prop_decl"
    ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
    ~init:(fun () -> ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant Elpi_ctx_Map.t),
               (Elpi.API.RawData.Constants.Map.empty : Why3.Decl.decl Elpi.API.ContextualConversion.ctx_entry Elpi.API.RawData.Constants.Map.t)))
    ~start:(fun x -> x)
let elpi_pdecl_to_key ~depth:_  : Decl.prop_decl -> Decl.prsymbol = function (_,prs,_) -> prs
module Ctx_for_pdecl =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end

let elpi_is_pdecl { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
  match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
  | Elpi.API.RawData.Const _ -> None
  | Elpi.API.RawData.App (hd, elpi__idx, _) when hd == elpi_constant_type_prop_declc ->
        (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
         | Elpi.API.RawData.Const x -> Some x
         | _ -> Elpi.API.Utils.type_error "context entry applied to a non nominal")
  | _ -> None
let context_made_of_pdecl = {
    Elpi.API.ContextualConversion.is_entry_for_nominal = elpi_is_ctx;
    to_key = elpi_pdecl_to_key;
    push = elpi_push_ctx;
    pop = elpi_pop_ctx;
    conv = ctx;
    init = (fun state -> Elpi.API.State.set elpi_ctx_state state ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant Elpi_ctx_Map.t),
             (Elpi.API.RawData.Constants.Map.empty : ctx Elpi.API.ContextualConversion.ctx_entry Elpi.API.RawData.Constants.Map.t)));
    get = (fun state -> snd @@ (Elpi.API.State.get elpi_ctx_state state))
  }
let elpi_ctx = Elpi.API.BuiltIn.MLDataC ctx
class ctx_for_ctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
  : Ctx_for_ctx.t =
  object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
let (in_ctx_for_ctx : (Ctx_for_ctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
  fun ~depth h c s -> (s, ((new ctx_for_ctx) h s), c, (List.concat []))
let _ = in_ctx_for_ctx
let () = declaration := ((!declaration) @ [elpi_ctx]) *)