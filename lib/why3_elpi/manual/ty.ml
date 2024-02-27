let elpi_opaque_data_decl_tysymbol = Elpi.API.OpaqueData.declare {
  name = "tysymbol";
  doc = "Embedding of type symbols. Internal information (Ident, arguments) is not exposed.";
  pp = pp_why_data Pretty.print_ts;
  compare = Ty.ts_compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [("arr", Ty.ts_func)] (* [("«ts_int»", Ty.ts_int ); ("«ts_real»", Ty.ts_real ); ("«ts_bool»", Ty.ts_bool ); ("«ts_str»", Ty.ts_str )] *);
}
module Ctx_for_tysymbol =
  struct
    class type t = object inherit Elpi.API.ContextualConversion.ctx end
  end
let tysymbol : 'c .  (tysymbol, #Elpi.API.ContextualConversion.ctx as 'c, 'csts) Elpi.API.ContextualConversion.t =
  let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
    elpi_opaque_data_decl_tysymbol in
  let embed ~depth  _ _ s t = embed ~depth s t in
  let readback ~depth  _ _ s t = readback ~depth s t in
  { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp }
let elpi_embed_tysymbol = tysymbol.Elpi.API.ContextualConversion.embed
let _ = elpi_embed_tysymbol
let elpi_readback_tysymbol = tysymbol.Elpi.API.ContextualConversion.readback
let _ = elpi_readback_tysymbol
let elpi_tysymbol = Elpi.API.BuiltIn.MLDataC tysymbol
class ctx_for_tysymbol (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state) : Ctx_for_tysymbol.t =
  object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
let (in_ctx_for_tysymbol : (Ctx_for_tysymbol.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth h c s -> (s, ((new ctx_for_tysymbol) h s), c, (List.concat []))
