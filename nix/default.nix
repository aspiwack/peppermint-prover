with (import <nixpkgs>) {};

let

  ghc-compiler = callPackage ./ghc.nix {};
  ghc-pkgs = with haskell.lib; haskell.packages.ghcHEAD.override {
    ghc = ghc-compiler;
    overrides = self : super : {
      mkDerivation = args : super.mkDerivation (args // {
        doCheck = false;
        jailbreak = true;
      });
      # package overrides here
    };
  };
  ghc-with-pkgs =
    ghc-pkgs.ghcWithPackages ( pkgs : [
    # install packages here
    cabal-install
    ]);

in

  ghc-with-pkgs
