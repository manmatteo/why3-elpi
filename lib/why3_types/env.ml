open Common
open Why3.Env

let declaration = ref []

type env = Why3.Env.env
[@@elpi.opaque
  { Elpi.API.OpaqueData.name = "env"
  ; doc =
      "The current environment can be retrieved, for example during a \
       transformation with why3.get-env"
  ; pp = pp_why_ident (fun fmt _e -> Format.fprintf fmt "env")
  ; compare = (fun _ -> fun _ -> 0)
  ; hash = (fun e -> Why3.Weakhtbl.tag_hash (env_tag e))
  ; hconsed = false
  ; constants = []
  }]
[@@deriving elpi { declaration }]
