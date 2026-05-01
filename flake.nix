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
    let
      package = "why3_elpi";
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
        on = opam-nix.lib.${system};
        devPackagesQuery = {
          ocaml-lsp-server = "*";
          ocamlformat = "*";
          # alt-ergo = "*";
        };
        query = devPackagesQuery // {
          ocaml-base-compiler = "*";
          atdgen = "*";
          "atdgen-runtime" = "*";
        };
        scope = on.buildOpamProject' { pinDepends = false; } ./. query;
        overlay = final: prev: {
          # You can add overrides here
          ${package} = prev.${package}.overrideAttrs (_: {
            # Prevent the ocaml dependencies from leaking into dependent environments
            doNixSupport = false;
          });
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
            pkgs.cvc5
            pkgs.z3
            pkgs.alt-ergo
            # why3 with nix option "ideSupport" enabled
            # (pkgs.why3.override { ideSupport = true; })
          ];
        };
      }
    );
}
