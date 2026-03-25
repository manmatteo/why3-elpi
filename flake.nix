{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
  };
  outputs =
    {
      self,
      flake-utils,
      opam-nix,
      nixpkgs,
    }@inputs:
    # Don't forget to put the package name instead of `throw':
    let
      package = "why3_elpi";
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};
        devPackagesQuery = {
          ocaml-lsp-server = "*";
          ocamlformat = "*";
        };
        query = devPackagesQuery // {
          ocaml-base-compiler = "*";
          # The pinned elpi branch requires atdgen but doesn't declare it in its opam file
          atdgen = "*";
          "atdgen-runtime" = "*";
        };
        scope = on.buildOpamProject' { pinDepends = true; } ./. query;
        overlay = final: prev: {
          # You can add overrides here
          ${package} = prev.${package}.overrideAttrs (_: {
            # Prevent the ocaml dependencies from leaking into dependent environments
            doNixSupport = false;
          });
          # The pinned elpi branch uses atdgen in its dune file but omits it from
          # its opam depends; also, at atdgen 2.x the OCaml library is in
          # atdgen-runtime. Patch src/dune and add atdgen-runtime.
          elpi = prev.elpi.overrideAttrs (old: {
            buildInputs = (old.buildInputs or []) ++ [ prev."atdgen-runtime" ];
            prePatch = (old.prePatch or "") + ''
              sed -i 's/(libraries yojson atdgen re)/(libraries yojson atdgen-runtime re)/g' src/dune
            '';
          });
        };
        scope' = scope.overrideScope overlay;
        # The main package containing the executable
        main = scope'.${package};
        # Packages from devPackagesQuery
        devPackages = builtins.attrValues (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');
      in
      {
        legacyPackages = scope';

        packages.default = main;

        devShells.default = pkgs.mkShell {
          inputsFrom = [ main ];
          buildInputs = devPackages ++ [
            # You can add packages from nixpkgs here
          ];
        };
      }
    );
}
