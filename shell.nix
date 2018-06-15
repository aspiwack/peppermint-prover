with (import <nixpkgs>) {};

let
  ghc-with-pkgs = import ./nix;
in
  stdenv.mkDerivation rec {
    name = "ghc-master-env";
    env = buildEnv {
      inherit name;
      paths = buildInputs;
    };
    buildInputs = [ ghc-with-pkgs ];
  }
