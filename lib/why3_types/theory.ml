open Decl
open Why3
open Elpi
open Why3.Theory
(* let theory : Theory.theory Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "theory";
  doc = "Symbol for theory (currently cannot be inspected)";
  pp = (fun fmt t -> Format.fprintf fmt "%s" t.Theory.th_name.id_string);
  compare = (fun x y -> Stdlib.compare x.th_name y.th_name);
  hash = (fun x -> Hashtbl.hash x.th_name);
  hconsed = false;
  constants = [];
} *)
let declaration = ref []
include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : theory) -> ()
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_theory = "theory"
    let _ = elpi_constant_type_theory
    let elpi_constant_type_theoryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_theory
    let _ = elpi_constant_type_theoryc
    let elpi_opaque_data_decl_theory =
      Elpi.API.OpaqueData.declare
        {
          name = "theory";
          doc = "Symbol for theory (currently cannot be inspected)";
          pp =
            (fun fmt ->
               fun t -> Format.fprintf fmt "%s" (t.Theory.th_name).id_string);
          compare = (fun x -> fun y -> Stdlib.compare x.th_name y.th_name);
          hash = (fun x -> Hashtbl.hash x.th_name);
          hconsed = false;
          constants = []
        }
    let _ = elpi_opaque_data_decl_theory
    module Ctx_for_theory =
      struct
        class type t = object inherit Elpi_api_compat.ctx end
      end
    let theory :
      'c .
        (theory, 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_theory in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = theory
    let elpi_embed_theory = theory.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_theory
    let elpi_readback_theory = theory.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_theory
    let elpi_theory = Elpi.API.BuiltIn.MLDataC theory
    let _ = elpi_theory
    class ctx_for_theory (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_theory.t =
      object (_) inherit  ((Elpi_api_compat.ctx) h) end
    let (in_ctx_for_theory :
      (Ctx_for_theory.t, 'csts) Elpi_api_compat.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_theory) h s), c, (List.concat []))
    let _ = in_ctx_for_theory
    let () = declaration := !declaration @ [elpi_theory]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : meta_arg) -> ()
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_meta_arg = "meta-arg"
    let _ = elpi_constant_type_meta_arg
    let elpi_constant_type_meta_argc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_meta_arg
    let _ = elpi_constant_type_meta_argc
    let elpi_opaque_data_decl_meta_arg =
      Elpi.API.OpaqueData.declare
        {
          Elpi.API.OpaqueData.name = "meta-arg";
          doc = "Symbol for meta args (currently cannot be inspected)";
          pp =
            (fun fmt ->
               fun m -> Format.fprintf fmt "%a" Pretty.print_meta_arg m);
          compare = Stdlib.compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    let _ = elpi_opaque_data_decl_meta_arg
    module Ctx_for_meta_arg =
      struct
        class type t = object inherit Elpi_api_compat.ctx end
      end
    let meta_arg :
      'c .
        (meta_arg, 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_meta_arg in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = meta_arg
    let elpi_embed_meta_arg = meta_arg.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_meta_arg
    let elpi_readback_meta_arg =
      meta_arg.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_meta_arg
    let elpi_meta_arg = Elpi.API.BuiltIn.MLDataC meta_arg
    let _ = elpi_meta_arg
    class ctx_for_meta_arg (h : Elpi.API.Data.hyps)
      (s : Elpi.API.Data.state) : Ctx_for_meta_arg.t =
      object (_) inherit  ((Elpi_api_compat.ctx) h) end
    let (in_ctx_for_meta_arg :
      (Ctx_for_meta_arg.t, 'csts) Elpi_api_compat.ctx_readback)
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_meta_arg) h s), c, (List.concat []))
    let _ = in_ctx_for_meta_arg
    let () = declaration := !declaration @ [elpi_meta_arg]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : meta) -> ()
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_meta = "meta"
    let _ = elpi_constant_type_meta
    let elpi_constant_type_metac =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_meta
    let _ = elpi_constant_type_metac
    let elpi_opaque_data_decl_meta =
      Elpi.API.OpaqueData.declare
        {
          name = "meta";
          doc = "Symbol for meta (currently cannot be inspected)";
          pp =
            (fun fmt -> fun m -> Format.fprintf fmt "%s" m.Theory.meta_name);
          compare = (fun x -> fun y -> Stdlib.compare x.meta_tag y.meta_tag);
          hash = (fun x -> Hashtbl.hash x.meta_tag);
          hconsed = false;
          constants = []
        }
    let _ = elpi_opaque_data_decl_meta
    module Ctx_for_meta =
      struct
        class type t = object inherit Elpi_api_compat.ctx end
      end
    let meta :
      'c .
        (meta, 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_meta in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let _ = meta
    let elpi_embed_meta = meta.Elpi.API.ContextualConversion.embed
    let _ = elpi_embed_meta
    let elpi_readback_meta = meta.Elpi.API.ContextualConversion.readback
    let _ = elpi_readback_meta
    let elpi_meta = Elpi.API.BuiltIn.MLDataC meta
    let _ = elpi_meta
    class ctx_for_meta (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_meta.t =
      object (_) inherit  ((Elpi_api_compat.ctx) h) end
    let (in_ctx_for_meta :
      (Ctx_for_meta.t, 'csts) Elpi_api_compat.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_meta) h s), c, (List.concat []))
    let _ = in_ctx_for_meta
    let () = declaration := !declaration @ [elpi_meta]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
(* Hide clones *)
(* TODO: Make this a ContextualConversion *)
(* actually, TODO is make clones work *)
let opaque_tdecl : Theory.tdecl Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "meta-arg";
  doc = "Symbol for arguments of a clone (currently cannot be inspected)";
  pp = (fun fmt t -> Format.fprintf fmt "%s"
        (match t.Theory.td_node with | Theory.Clone (t, _) -> t.th_name.Ident.id_string
        | _ -> "Wrong embedder used!"));
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}
(* 
let tdecl_declaration : (Theory.tdecl, #Ctx_for_why_simple_term.t ,'b) API.AlgebraicData.declaration =
  let open API.ContextualConversion in
  let open API.AlgebraicData in
  let open API.BuiltInContextualData in {
  ty = TyName "tdecl";
  doc = "Theory declarations";
  pp = Pretty.print_tdecl;
  constructors = [
   K("decl","Local or imported declaration",
     CA (decl,N),
     BS (fun x st -> st, Theory.create_decl x),
     MS (fun ~ok ~ko tdecl st ->
       (match tdecl.td_node with | Theory.Decl d -> ok d st | _ -> ko st)));
   K("use","Use of theory",
     A (theory,N),
     B (fun x -> Theory.create_use x),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Use t -> ok t | _ -> ko ())));
   (* K("meta","Map of metas", This breaks typing and I don't know why
     CA (meta,CA(list meta_arg,N)),
     BS (fun m args st -> st, Theory.create_meta m args),
     MS (fun ~ok ~ko tdecl st ->
       (match tdecl.td_node with | Theory.Meta (a,args) -> ok a args st | _ -> ko st))); *)
   K("clone","Clone of theory",
     A (opaque_tdecl, N),
     B (fun t -> t),
     M (fun ~ok ~ko td ->
       (match td.td_node with | Theory.Clone (_,_) -> ok td | _ -> ko ())));
  ]
}

let tdecl : (Theory.tdecl, #Ctx_for_why_simple_term.t, 'b) API.ContextualConversion.t
 = API.AlgebraicData.declare tdecl_declaration *)

(* Exported from PPX, much edited *)
let elpi_constant_type_tdecl = "tdecl"
let elpi_constant_type_tdecl_nodec = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_tdecl
let elpi_constant_constructor_tdecl_node_Decl = "decl"
let elpi_constant_constructor_tdecl_node_Declc = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_tdecl_node_Decl
let elpi_constant_constructor_tdecl_node_Use = "use"
let elpi_constant_constructor_tdecl_node_Usec = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_tdecl_node_Use
let elpi_constant_constructor_tdecl_node_Meta = "meta"
let elpi_constant_constructor_tdecl_node_Metac = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_tdecl_node_Meta
let elpi_constant_constructor_tdecl_node_Clone = "clone"
let elpi_constant_constructor_tdecl_node_Clonec = Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_constructor_tdecl_node_Clone
module Ctx_for_tdecl_node =
  struct
    class type t = object inherit Elpi_api_compat.ctx end
  end
let rec elpi_embed_tdecl =
  fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state td ->
    match td.td_node with
    | Decl elpi__9 ->
         let (elpi__state, elpi__11, elpi__10) = decl.Elpi.API.ContextualConversion.embed ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__9 in
         (elpi__state, (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_tdecl_node_Declc [elpi__11]), (List.concat [elpi__10]))
     | Use elpi__12 ->
         let (elpi__state, elpi__14, elpi__13) = theory.Elpi.API.ContextualConversion.embed ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__12 in
         (elpi__state, (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_tdecl_node_Usec [elpi__14]), (List.concat [elpi__13]))
     | Clone _ -> let (st, td, eg) = opaque_tdecl.embed ~depth:elpi__depth elpi__state td in
                  (st, (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_tdecl_node_Clonec [td]), eg)
     | Meta (elpi__15, elpi__16) ->
         let (elpi__state, elpi__19, elpi__17) = meta.Elpi.API.ContextualConversion.embed ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__15 in
         let (elpi__state, elpi__20, elpi__18) = (fun ~depth h c s t ->
                      (let embed = meta_arg.Elpi.API.ContextualConversion.embed in
                       fun ~depth h c s l ->
                                 let (s, l, eg) = Elpi.API.Utils.map_acc (embed ~depth h c) s l in
                                 (s, (Elpi.API.Utils.list_to_lp_list l), eg)) ~depth h c s t)
             ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__16 in
         (elpi__state, (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_tdecl_node_Metac [elpi__19; elpi__20]), (List.concat [elpi__17; elpi__18]))
and elpi_readback_tdecl =
  fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x ->
  match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when elpi__hd == elpi_constant_constructor_tdecl_node_Declc ->
    let (elpi__state, elpi__2, elpi__1) = decl.Elpi.API.ContextualConversion.readback ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x in
    (match elpi__xs with
     | [] -> (elpi__state, (Theory.create_decl elpi__2), (List.concat [elpi__1]))
     | _ -> Elpi.API.Utils.type_error ("Not enough arguments to constructor: " ^ (Elpi.API.RawData.Constants.show elpi_constant_constructor_tdecl_node_Declc)))
  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when elpi__hd == elpi_constant_constructor_tdecl_node_Usec ->
    let (elpi__state, elpi__4, elpi__3) = theory.Elpi.API.ContextualConversion.readback ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x in
    (match elpi__xs with
    | [] -> (elpi__state, (Theory.create_use elpi__4), (List.concat [elpi__3]))
    | _ -> Elpi.API.Utils.type_error ("Not enough arguments to constructor: " ^ (Elpi.API.RawData.Constants.show elpi_constant_constructor_tdecl_node_Usec)))
  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when elpi__hd == elpi_constant_constructor_tdecl_node_Metac ->
    let (elpi__state, elpi__8, elpi__7) = meta.Elpi.API.ContextualConversion.readback ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x in
    (match elpi__xs with
    | elpi__5::[] ->
    let (elpi__state, elpi__5, elpi__6) = (fun ~depth h c s t ->
    (let readback = meta_arg.Elpi.API.ContextualConversion.readback in
     fun ~depth h c s t -> Elpi.API.Utils.map_acc (readback ~depth h c) s (Elpi.API.Utils.lp_list_to_list ~depth t)) ~depth h c s t) ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__5 in
      (elpi__state, (Theory.create_meta elpi__8 elpi__5), (List.concat [elpi__7; elpi__6]))
    | _ -> Elpi.API.Utils.type_error ("Not enough arguments to constructor: " ^ (Elpi.API.RawData.Constants.show elpi_constant_constructor_tdecl_node_Metac)))
  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when elpi__hd == elpi_constant_constructor_tdecl_node_Clonec ->
    let (st, td, eg) = opaque_tdecl.readback ~depth:elpi__depth elpi__state elpi__x in (st, td, eg)
  | _ -> Elpi.API.Utils.type_error (Format.asprintf "Not a constructor of type %s: %a" "tdecl_node" (Elpi.API.RawPp.term elpi__depth) elpi__x)
and tdecl =
  let kind = Elpi.API.ContextualConversion.TyName "tdecl" in
  { Elpi.API.ContextualConversion.ty = kind;
    pp_doc = (fun fmt () ->
           Elpi_api_compat.Doc.kind fmt kind ~doc:"tdecl";
           Elpi_api_compat.Doc.constructor fmt ~ty:kind ~name:"decl" ~doc:"Decl" ~args:[decl.Elpi.API.ContextualConversion.ty];
           Elpi_api_compat.Doc.constructor fmt ~ty:kind ~name:"use" ~doc:"Use" ~args:[theory.Elpi.API.ContextualConversion.ty];
           Elpi_api_compat.Doc.constructor fmt ~ty:kind ~name:"meta" ~doc:"Meta" ~args:[meta.Elpi.API.ContextualConversion.ty; Elpi.API.ContextualConversion.TyApp ("list", (meta_arg.Elpi.API.ContextualConversion.ty), [])]);
    pp = (fun fmt t ->
           match t.td_node with
           | Decl d -> Format.fprintf fmt "%a" Pretty.print_decl d
           | Use t -> Format.fprintf fmt "use %s" (t.th_name).id_string
           | Clone (t, _) -> Format.fprintf fmt "clone %s" (t.th_name).id_string
           | Meta (m, _) -> Format.fprintf fmt "meta %s" m.meta_name);
    embed = elpi_embed_tdecl;
    readback = elpi_readback_tdecl
  }

let elpi_tdecl = Elpi.API.BuiltIn.MLDataC tdecl
let () = declaration := !declaration @ [elpi_tdecl]