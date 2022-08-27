{
  description = "software-foundations";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlay = self: _: {

          # QuickChick = (self.coqPackages_8_15.QuickChick.override (oldAttrs: {
          #   version = ".2.0+beta";
          # })).overrideAttrs (oldAttrs: {
          #   release.".2.0+beta".sha256 = "sha256-rw9C23QpOWJlGADW1GseObZSWtpaQt/IcTZc1EANi+4=";
          # });
          QuickChick = (self.coqPackages_8_15.QuickChick.overrideAttrs (oldAttrs: {
            # release = {".2.0+beta".sha256 = "sha256-rw9C23QpOWJlGADW1GseObZSWtpaQt/IcTZc1EANi+4=";};
            src = self.fetchFromGitHub {
              owner = "QuickChick";
              repo = "QuickChick";
              rev = ".2.0+beta";
              sha256 = "sha256-rw9C23QpOWJlGADW1GseObZSWtpaQt/IcTZc1EANi+5=";
            };
            version = ".2.0+beta";
          })).override (oldAttrs: {
            version = ".2.0+beta";
          });

          software-foundations-shell = self.stdenv.mkDerivation {
            name = "software-foundations-shell";
            dontUnpack = true;
            nativeBuildInputs = [ self.coq_8_15 self.coq_8_15.ocaml self.QuickChick ];
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
        package.QuickChick = pkgs.QuickChick;
        package.coq = pkgs.coq_8_15;
        devShell = pkgs.software-foundations-shell;
      }
    );
}

