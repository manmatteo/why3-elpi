let theory : Theory.theory Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "theory";
  doc = "Symbol for theory (currently cannot be inspected)";
  pp = (fun fmt t -> Format.fprintf fmt "%s" t.Theory.th_name.id_string);
  compare = (fun x y -> Stdlib.compare x.th_name y.th_name);
  hash = (fun x -> Hashtbl.hash x.th_name);
  hconsed = false;
  constants = [];
}
let meta : Theory.meta Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "meta";
  doc = "Symbol for meta (currently cannot be inspected)";
  pp = (fun fmt m -> Format.fprintf fmt "%s" m.Theory.meta_name);
  compare = (fun x y -> Stdlib.compare x.meta_tag y.meta_tag);
  hash = (fun x -> Hashtbl.hash x.meta_tag);
  hconsed = false;
  constants = [];
}
let meta_arg : Theory.meta_arg Elpi.API.Conversion.t = API.OpaqueData.declare {
  Elpi.API.OpaqueData.name = "meta-arg";
  doc = "Symbol for meta args (currently cannot be inspected)";
  pp = (fun fmt m -> Format.fprintf fmt "%a" Pretty.print_meta_arg m);
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

(* Hide clones *)
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

let tdecl_declaration : (Theory.tdecl,'a,'b) API.AlgebraicData.declaration = 
  let open API.ContextualConversion in
  let open API.BuiltInData in {
  ty = TyName "tdecl";
  doc = "Theory declarations";
  pp = Pretty.print_tdecl;
  constructors = [
   K("decl","Local or imported declaration",
     A (!< decl,N),
     B (fun x -> Theory.create_decl x),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Decl d -> ok d | _ -> ko ())));
   K("use","Use of theory",
     A (theory,N),
     B (fun x -> Theory.create_use x),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Use t -> ok t | _ -> ko ())));
   K("meta","Map of metas",
     A (meta,A(list meta_arg,N)),
     B (fun m args -> Theory.create_meta m args),
     M (fun ~ok ~ko tdecl ->
       (match tdecl.td_node with | Theory.Meta (a,args) -> ok a args | _ -> ko ())));
   K("clone","Clone of theory",
     A (opaque_tdecl, N),
     B (fun t -> t),
     M (fun ~ok ~ko td ->
       (match td.td_node with | Theory.Clone (_,_) -> ok td | _ -> ko ())));
  ]
}

let tdecl = API.AlgebraicData.declare tdecl_declaration
