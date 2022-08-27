{
  description = "software-foundations";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlay = self: _: {
          software-foundations-shell = self.stdenv.mkDerivation {
            name = "software-foundations-shell";
            dontUnpack = true;
            nativeBuildInputs = [ self.coq_8_12 ];
            installPhase = "touch $out";
          };
        };
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            overlay
          ];
        };
      in
      {
        devShell = pkgs.software-foundations-shell;
      }
    );
}

