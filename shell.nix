{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    pkgs.haskellPackages.haskell-language-server
    pkgs.ghc

    # keep this line if you use bash
    pkgs.bashInteractive
  ];
}
