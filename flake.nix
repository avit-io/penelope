{
  description = "Penelope — verifiable Grafana dashboards in Agda";

  inputs = {
    nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/0.2511.912939";
    piforge = {
      url   = "github:avit-io/piforge";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    prometea = {
      url   = "github:avit-io/prometea";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.piforge.follows = "piforge";
    };
    henql = {
      url   = "github:avit-io/henql";
      inputs.nixpkgs.follows  = "nixpkgs";
      inputs.piforge.follows  = "piforge";
      inputs.prometea.follows = "prometea";
    };
    loquel = {
      url   = "github:avit-io/loquel";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.piforge.follows = "piforge";
    };
  };

  outputs = { self, nixpkgs, piforge, prometea, henql, loquel }:
    let
      system = "x86_64-linux";
      pkgs   = nixpkgs.legacyPackages.${system};

      penelopeLib = pkgs.stdenv.mkDerivation {
        name      = "penelope-agda-lib";
        src       = builtins.path { path = ./.; name = "penelope-src"; };
        dontBuild = true;
        installPhase = ''
          mkdir -p $out
          cp -r Penelope $out/
          printf 'name: penelope\ninclude: .\ndepend: standard-library prometea henql loquel\n' \
            > $out/penelope.agda-lib
        '';
      };

      # Requires $_cache, $_stdlib, $_prometea, $_henql to be set
      # (call after henql.lib.mkShell's hooks).
      # Usa il nix store path come sentinel per invalidare la cache quando
      # la libreria cambia (es. nuovi flag --without-K, API aggiornate).
      copyLoquel = ''
        _loquel="$_cache/loquel"
        _loquel_tag="${loquel.packages.${system}.lib}"
        if [ ! -f "$_loquel/.nix-tag" ] || [ "$(cat "$_loquel/.nix-tag")" != "$_loquel_tag" ]; then
          echo "penelope: copying loquel to $_loquel..." >&2
          rm -rf "$_loquel"
          mkdir -p "$_loquel"
          cp -r ${loquel.packages.${system}.lib}/. "$_loquel/"
          chmod -R u+w "$_loquel"
          printf 'name: loquel\ninclude: .\ndepend: standard-library\n' \
            > "$_loquel/loquel.agda-lib"
          echo "$_loquel_tag" > "$_loquel/.nix-tag"
        fi
      '';

      copyPenelope = ''
        _penelope="$_cache/penelope"
        _penelope_tag="${penelopeLib}"
        if [ ! -f "$_penelope/.nix-tag" ] || [ "$(cat "$_penelope/.nix-tag")" != "$_penelope_tag" ]; then
          echo "penelope: copying library to $_penelope..." >&2
          rm -rf "$_penelope"
          mkdir -p "$_penelope"
          cp -r ${penelopeLib}/. "$_penelope/"
          chmod -R u+w "$_penelope"
          printf 'name: penelope\ninclude: .\ndepend: standard-library prometea henql loquel\n' \
            > "$_penelope/penelope.agda-lib"
          echo "$_penelope_tag" > "$_penelope/.nix-tag"
        fi
      '';

    in
    {
      packages.${system} = {
        lib     = penelopeLib;
        default = penelopeLib;
      };

      # Dev shell for working on Penelope itself: stdlib + prometea + henql
      # + loquel in AGDA_DIR.
      devShells.${system}.default = henql.lib.mkShell {
        inherit pkgs;
        extraPackages = with pkgs; [ watchexec ];
        shellHook = copyLoquel + ''
          mkdir -p "$_cache/penelope-dev"
          printf '%s\n%s\n%s\n%s\n' \
            "$_stdlib/standard-library.agda-lib" \
            "$_prometea/prometea.agda-lib" \
            "$_henql/henql.agda-lib" \
            "$_loquel/loquel.agda-lib" \
            > "$_cache/penelope-dev/libraries"
          export AGDA_DIR="$_cache/penelope-dev"
        '';
      };

      # For consumers: stdlib + prometea + henql + loquel + penelope in AGDA_DIR.
      lib.mkShell = { pkgs, extraPackages ? [], shellHook ? "" }:
        henql.lib.mkShell {
          inherit pkgs extraPackages;
          shellHook = copyLoquel + copyPenelope + ''
            mkdir -p "$_cache/penelope-env"
            printf '%s\n%s\n%s\n%s\n%s\n' \
              "$_stdlib/standard-library.agda-lib" \
              "$_prometea/prometea.agda-lib" \
              "$_henql/henql.agda-lib" \
              "$_loquel/loquel.agda-lib" \
              "$_penelope/penelope.agda-lib" \
              > "$_cache/penelope-env/libraries"
            export AGDA_DIR="$_cache/penelope-env"
          '' + shellHook;
        };

      # For consumers: compila `<mainModule>.agda` da `src` con l'intero
      # stack (stdlib, prometea, henql, loquel, penelope) e installa lo
      # stdout del binario in $out/<name>.json. Contratto: il main
      # stampa il JSON della dashboard su stdout (run (putStr …)).
      #
      # Il wrapper agda-28 di piforge legge $HOME/.cache/piforge/
      # libraries-2.8.0 e salta la copia della stdlib se
      # $HOME/.cache/piforge/stdlib-2.3 esiste già: pre-seediamo l'intera
      # directory con le cinque librerie prima di invocarlo.
      lib.buildDashboard = { pkgs, src, name, mainModule ? "Main" }:
        let
          sys      = pkgs.stdenv.hostPlatform.system;
          agda     = piforge.packages.${sys}."agda-28";
          stdlib   = piforge.packages.${sys}."stdlib-28";
          ghc      = pkgs.haskell.packages.ghc910.ghcWithPackages (ps: with ps; [
            text bytestring containers unordered-containers hashable
          ]);
          seedLib = nm: drv: dep: ''
            mkdir -p "$_base/${nm}"
            cp -r ${drv}/. "$_base/${nm}/"
            chmod -R u+w "$_base/${nm}"
            printf 'name: ${nm}\ninclude: .\ndepend: ${dep}\n' \
              > "$_base/${nm}/${nm}.agda-lib"
          '';
        in pkgs.stdenv.mkDerivation {
          pname   = "penelope-dashboard-${name}";
          version = "0.1";
          inherit src;

          nativeBuildInputs = [ agda ghc pkgs.gmp pkgs.zlib ];

          # Titoli/JSON possono contenere non-ASCII (·, è, …): senza un
          # locale UTF-8 il runtime GHC non sa codificarli su stdout e
          # Agda non riesce a stampare i propri errori (ℕ, ÷, …).
          LC_ALL = "C.UTF-8";

          buildPhase = ''
            runHook preBuild

            export HOME=$TMPDIR/home
            _base="$HOME/.cache/piforge"
            mkdir -p "$_base/stdlib-2.3"
            cp -r ${stdlib}/. "$_base/stdlib-2.3/"
            chmod -R u+w "$_base/stdlib-2.3"

            ${seedLib "prometea" prometea.packages.${sys}.lib "standard-library"}
            ${seedLib "henql"    henql.packages.${sys}.lib    "standard-library prometea"}
            ${seedLib "loquel"   loquel.packages.${sys}.lib   "standard-library"}
            ${seedLib "penelope" penelopeLib                  "standard-library prometea henql loquel"}

            printf '%s\n%s\n%s\n%s\n%s\n' \
              "$_base/stdlib-2.3/standard-library.agda-lib" \
              "$_base/prometea/prometea.agda-lib" \
              "$_base/henql/henql.agda-lib" \
              "$_base/loquel/loquel.agda-lib" \
              "$_base/penelope/penelope.agda-lib" \
              > "$_base/libraries-2.8.0"

            agda --compile ${mainModule}.agda

            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            mkdir -p "$out"
            ./${mainModule} > "$out/${name}.json"
            runHook postInstall
          '';
        };
    };
}
