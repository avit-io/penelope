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
      copyLoquel = ''
        _loquel="$_cache/loquel"
        if [ ! -d "$_loquel" ]; then
          echo "penelope: copying loquel to $_loquel (one-time setup)..." >&2
          mkdir -p "$_loquel"
          cp -r ${loquel.packages.${system}.lib}/. "$_loquel/"
          chmod -R u+w "$_loquel"
          printf 'name: loquel\ninclude: .\ndepend: standard-library\n' \
            > "$_loquel/loquel.agda-lib"
        fi
      '';

      copyPenelope = ''
        _penelope="$_cache/penelope"
        if [ ! -d "$_penelope" ]; then
          echo "penelope: copying library to $_penelope (one-time setup)..." >&2
          mkdir -p "$_penelope"
          cp -r ${penelopeLib}/. "$_penelope/"
          chmod -R u+w "$_penelope"
          printf 'name: penelope\ninclude: .\ndepend: standard-library prometea henql loquel\n' \
            > "$_penelope/penelope.agda-lib"
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
    };
}
