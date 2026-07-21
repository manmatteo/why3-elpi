{
  inputs = {
    # Pinned to a known-good rev; newer opam-nix trips an 'ocaml-config missing'
    # overlay bug against recent opam-repository snapshots.
    opam-nix.url = "github:tweag/opam-nix/ce332e6467a888fc4b67264282b728a8c1034cde";
    # Pin the opam-repository snapshot ourselves so we control which package
    # versions are visible (elpi 3.7 only landed 2026-04-15).
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-nix.inputs.opam-repository.follows = "opam-repository";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
    treefmt.url = "github:numtide/treefmt-nix";
  };
  outputs = {
    self,
    flake-utils,
    opam-nix,
    opam-repository,
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
            # 5.3.0: the newest compiler this opam-nix's build shim handles
            # (5.4/5.5 trip an OPAMSWITCH unbound-variable error).
            ocaml-base-compiler = "5.3.0";
            # Recent opam-repository dropped ocaml-config from the default ocaml
            # metapackage closure, but opam-nix's ocaml overlay still references
            # it; request it explicitly so it stays in the resolved package set.
            ocaml-config = "*";
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
