{
  description = "software-foundations";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlay = final: prev: {

          QuickChick = (final.mycoqPackages.QuickChick.overrideAttrs (oldAttrs: {
            # release = {".2.0+beta".sha256 = "sha256-rw9C23QpOWJlGADW1GseObZSWtpaQt/IcTZc1EANi+4=";};
            src = final.fetchFromGitHub {
              owner = "QuickChick";
              repo = "QuickChick";
              rev = ".2.0+beta";
              sha256 = "sha256-rw9C23QpOWJlGADW1GseObZSWtpaQt/IcTZc1EANi+5=";
            };
            version = ".2.0+beta";
          })).override (oldAttrs: {
            version = ".2.0+beta";
          });

          mycoqPackages = final.coqPackages_8_15;
          mycoq = final.coq_8_15;

          software-foundations-shell = final.stdenv.mkDerivation {
            name = "software-foundations-shell";
            dontUnpack = true;
            nativeBuildInputs = [ final.mycoq final.mycoq.ocaml final.mycoqPackages.coqide final.QuickChick ];
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

