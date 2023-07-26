{
  description = "software-foundations";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlay = final: prev: {

          my-vscode-with-coq = final.vscode-with-extensions.override {
            vscode = final.vscodium;
            vscodeExtensions = [ final.vscode-extensions.maximedenes.vscoq ];
          };

          software-foundations-shell = final.stdenv.mkDerivation {
            name = "software-foundations-shell";
            dontUnpack = true;
            nativeBuildInputs = [ final.coq_8_17 final.my-vscode-with-coq ];
            installPhase = "touch $out";
          };
        };
        pkgs = import nixpkgs { inherit system; overlays = [ overlay ]; };
      in
      {
        devShell = pkgs.software-foundations-shell;
      }
    );
}

