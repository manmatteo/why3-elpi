let embed_task : task Elpi.API.Conversion.embedding =
  let open Elpi.API.ContextualConversion in
  fun ~depth st task ->
  (API.BuiltInData.list !< tdecl).embed ~depth st (Task.task_tdecls task)

let readback_task : Task.task Elpi.API.Conversion.readback =
  let open Elpi.API.ContextualConversion in
  fun ~depth st term ->
    let st, tdecl_list, eg =
      (Elpi.API.BuiltInData.list !< tdecl).readback ~depth st term in
    let task = List.fold_left Task.add_tdecl None tdecl_list in
    st, task, eg

let task : Task.task Elpi.API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "list tdecl";
  pp = Pretty.print_task;
  pp_doc = (fun _fmt () -> ());
  readback = readback_task;
  embed = embed_task;
}