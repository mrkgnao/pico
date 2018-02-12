let 
  rien = import .rien/rien.nix {
    packageName = "pico";
    packagePath = ./.;

    # Instead of using <nixpkgs>, use a lock-file to stick to
    # a particular `nixpkgs` commit.
    nixpkgsLock = ./nixpkgs.json;

    ghcVersion = "ghc822";

    overrides = rec {
      jailbreak = [ "cabal-helper" "ghc-mod" "liquidhaskell" ];
      skipHaddock = justStaticExecutables;
      skipTests = [ "cabal-helper" "ghc-mod" ];
      justStaticExecutables = [ 
        "brittany" 
        "hpack"
        "ghcid"
      ];
    };
  };

in
  (rien.shell {
    # Generate Hoogle documentation?
    wantHoogle = true;

    # Haskell dependencies
    deps = hsPkgs: with hsPkgs; [
      brittany
      ghc-mod
      cabal-helper

      hpack
      ghcid
      hlint
      adjunctions
      exceptions
      hashable
      hspec
      lens
      mtl
      bound
      deriving-compat
      prettyprinter
      prettyprinter-ansi-terminal
      profunctors
      safe
      text
      uniplate
      unordered-containers
      QuickCheck
      hedgehog
      free
      comonad

      # llvm-hs
      # llvm-hs-pure
      # llvm-hs-typed

      contravariant
      unbound-generics
      ether
    ];

    # Optionally, also add sets of related packages that are
    # commonly used together.
    depSets = hsPkgs: with (rien.package-sets hsPkgs); [
      development-servers
    ];

    # Native dependencies
    nativeDeps = pkgs: with pkgs; [ 
      # z3 
      # llvm_5
    ];
  }) // { shellHook = "source setup-ghcmod.sh"; } 
