{ stdenv
, fetchgit
, cacert
, git
, haskell
} :
  # This builds the fork of GHC with the desired changes.
  #
  # We do so by overriding the ghcHEAD expression which does almost
  # the right thing already (namely building GHC via the git repos).
  #
  # Note that we specify an explicit commit. This should result
  # in a fully reproducable build, but it means changes are not
  # picked up automatically.
  #
  (haskell.compiler.ghcHEAD.override { version = "8.5.20180604"; })
    .overrideAttrs
      (old :
        { src = fetchgit {
            url = "git://git.haskell.org/ghc.git";
            rev = "7df589608abb178efd6499ee705ba4eebd0cf0d1";
            sha256 = "08dis5ny8ldxlfsip2b6gw4abcp9x911r838b9hyckvlk693pbwd";
          };
        }
      )

