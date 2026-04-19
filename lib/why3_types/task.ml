open Theory
let declaration = Theory.declaration
open Why3.Task

let split_goal_tdecls tdecls =
  let rec aux acc = function
    | [] -> None
    | td :: rest ->
        match td.Why3.Theory.td_node with
        | Why3.Theory.Decl d ->
            begin match Term.goal_decl_to_focused_goal d with
            | Some goal -> Some (List.rev_append acc rest, goal)
            | None -> aux (td :: acc) rest
            end
        | _ -> aux (td :: acc) rest
  in
  aux [] tdecls

let split_focused_goal task = split_goal_tdecls (task_tdecls task)

let embed_task : (task, 'a, 'b) Elpi.API.ContextualConversion.embedding =
  fun ~depth hyp constraints state task ->
  (Elpi_api_compat.BuiltInContextualData.list tdecl).embed ~depth hyp constraints state (task_tdecls task)

let readback_task : (task, 'a, 'b) Elpi.API.ContextualConversion.readback =
  let open Elpi.API.ContextualConversion in
  fun ~depth hyp c st term ->
    let st, tdecl_list, eg =
      (Elpi_api_compat.BuiltInContextualData.list tdecl).readback ~depth hyp c st term in
    let task = List.fold_left add_tdecl None tdecl_list in
    st, task, eg

let task : (task, 'a, 'b) Elpi.API.ContextualConversion.t = {
  Elpi.API.ContextualConversion.ty = Elpi.API.Conversion.TyName "list tdecl";
  pp = Why3.Pretty.print_task;
  pp_doc = (fun _fmt () -> ());
  readback = readback_task;
  embed = embed_task;
}

let focused_task_c = Elpi.API.RawData.Constants.declare_global_symbol "focused-task"

let embed_focused_task : (task, 'a, 'b) Elpi.API.ContextualConversion.embedding =
  fun ~depth hyp constraints state task ->
    match split_focused_goal task with
    | None -> Elpi.API.Utils.error "focused-task embedding requires a task with a goal"
    | Some (rest, goal) ->
        let state, rest_tm, eg1 =
          (Elpi_api_compat.BuiltInContextualData.list tdecl).embed ~depth hyp constraints state rest in
        let state, goal_tm, eg2 = Term.focused_goal.embed ~depth hyp constraints state goal in
        state, Elpi.API.RawData.mkAppGlobalL focused_task_c [rest_tm; goal_tm], eg1 @ eg2

let readback_focused_task : (task, 'a, 'b) Elpi.API.ContextualConversion.readback =
  fun ~depth hyp constraints state tm ->
    match Elpi.API.RawData.look ~depth tm with
    | Elpi.API.RawData.App (hd, rest_tm, [goal_tm]) when hd == focused_task_c ->
        let state, rest, eg1 =
          (Elpi_api_compat.BuiltInContextualData.list tdecl).readback ~depth hyp constraints state rest_tm in
        let state, goal, eg2 = Term.focused_goal.readback ~depth hyp constraints state goal_tm in
        let tdecls = rest @ Term.focused_goal_to_tdecls goal in
        let task = List.fold_left add_tdecl None tdecls in
        state, task, eg1 @ eg2
    | _ ->
        Elpi.API.Utils.type_error
          (Format.asprintf "Not a focused-task: %a" (Elpi.API.RawPp.term depth) tm)

let focused_task : (task, 'a, 'b) Elpi.API.ContextualConversion.t = {
  Elpi.API.ContextualConversion.ty = Elpi.API.Conversion.TyName "focused-task";
  pp = Why3.Pretty.print_task;
  pp_doc = (fun fmt () ->
    Format.fprintf fmt "kind focused-task type.@\n";
    Format.fprintf fmt "external symbol focused-task : list tdecl -> focused-goal -> focused-task.@\n");
  readback = readback_focused_task;
  embed = embed_focused_task;
}

let () = declaration := !declaration @ [Elpi.API.BuiltIn.MLDataC focused_task]

open Common
open Why3.Env
let elpi_constant_type_env = "env"
let elpi_constant_type_envc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_env
let elpi_opaque_data_decl_env =
  Elpi.API.OpaqueData.declare
    { name = "env";
      doc = "The current environment can be retrieved, for example during a transformation with why3.get-env";
      pp = (pp_why_ident (fun fmt _e -> Format.fprintf fmt "env"));
      compare = (fun _ -> fun _ -> 0);
      hash = (fun e -> Why3.Weakhtbl.tag_hash (env_tag e));
      hconsed = false;
      constants = [] }
module Ctx_for_env =
  struct
    class type t = object inherit Elpi_api_compat.ctx end
  end
let env : 'c .  (env, 'c, 'csts) Elpi.API.ContextualConversion.t =
  let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } = elpi_opaque_data_decl_env in
  let embed ~depth  _ _ s t = embed ~depth s t in
  let readback ~depth  _ _ s t = readback ~depth s t in
  { embed; readback; ty; pp_doc; pp }
let elpi_embed_env = env.Elpi.API.ContextualConversion.embed
let elpi_readback_env = env.Elpi.API.ContextualConversion.readback
let elpi_env = Elpi.API.BuiltIn.MLDataC env
class ctx_for_env (h : Elpi.API.Data.hyps)  (_s : Elpi.API.Data.state) : Ctx_for_env.t =
  object (_) inherit  ((Elpi_api_compat.ctx) h) end
let in_ctx_for_env : (Ctx_for_env.t, 'csts) Elpi_api_compat.ctx_readback =
  fun ~depth:_ h c s -> (s, ((new ctx_for_env) h s), c, [])
let () = declaration := ((!declaration) @ [elpi_env])