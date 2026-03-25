open Common
open Why3.Env
let declaration = ref []
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