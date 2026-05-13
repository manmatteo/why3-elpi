{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
    treefmt.url = "github:numtide/treefmt-nix";
  };
  outputs = {
    self,
    flake-utils,
    opam-nix,
    nixpkgs,
    treefmt,
  } @ inputs: let
    package = "why3_elpi";
  in
    flake-utils.lib.eachDefaultSystem (
      system: let
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
        query =
          devPackagesQuery
          // {
            ocaml-base-compiler = "*";
            atdgen = "*";
            "atdgen-runtime" = "*";
          };
        scope = on.buildOpamProject' {pinDepends = false;} ./. query;
        overlay = final: prev: {
          # You can add overrides here
          ${package} = prev.${package}.overrideAttrs (_: {
            # Prevent the ocaml dependencies from leaking into dependent environments
            doNixSupport = false;
          });
          elpi = prev.elpi.overrideAttrs (old: {
            buildInputs = (old.buildInputs or []) ++ [prev."atdgen-runtime"];
            prePatch =
              (old.prePatch or "")
              + ''
                sed -i 's/(libraries yojson atdgen re)/(libraries yojson atdgen-runtime re)/g' src/dune
              '';
          });
        };
        scope' = scope.overrideScope overlay;
        # The main package containing the executable
        main = scope'.${package};
        # Packages from devPackagesQuery
        devPackages = builtins.attrValues (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');
      in {
        legacyPackages = scope';

        packages.default = main;

        formatter = treefmt.lib.mkWrapper pkgs {
          projectRootFile = "dune-project";

          settings.global.excludes = ["vendored/**"];

          programs.alejandra.enable = true;
          programs.ocamlformat = {
            enable = true;
            package = scope'.ocamlformat.overrideAttrs (_: {
              meta.mainProgram = "ocamlformat";
            });
          };
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [main];
          buildInputs =
            devPackages
            ++ [
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
