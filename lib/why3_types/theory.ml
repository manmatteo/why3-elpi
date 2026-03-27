open Decl
module Decl_conv = Decl
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
let declaration = Decl_conv.decl_declaration
type theory = Why3.Theory.theory
[@@elpi.opaque {
  name = "theory";
  doc = "Symbol for theory (currently cannot be inspected)";
  pp =
    (fun fmt ->
       fun t -> Format.fprintf fmt "%s" (t.Theory.th_name).id_string);
  compare = (fun x -> fun y -> Stdlib.compare x.th_name y.th_name);
  hash = (fun x -> Hashtbl.hash x.th_name);
  hconsed = false;
  constants = [];
}]
[@@deriving elpi {declaration}]

type meta_arg = Why3.Theory.meta_arg
[@@elpi.opaque {
  Elpi.API.OpaqueData.name = "meta-arg";
  doc = "Symbol for meta args (currently cannot be inspected)";
  pp =
    (fun fmt ->
       fun m -> Format.fprintf fmt "%a" Pretty.print_meta_arg m);
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}]
[@@deriving elpi {declaration}]

type meta = Why3.Theory.meta
[@@elpi.opaque {
  name = "meta";
  doc = "Symbol for meta (currently cannot be inspected)";
  pp =
    (fun fmt -> fun m -> Format.fprintf fmt "%s" m.Theory.meta_name);
  compare = (fun x -> fun y -> Stdlib.compare x.meta_tag y.meta_tag);
  hash = (fun x -> Hashtbl.hash x.meta_tag);
  hconsed = false;
  constants = [];
}]
[@@deriving elpi {declaration}]
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