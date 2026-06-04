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
  };

  outputs = { self, nixpkgs, piforge, prometea, henql }:
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
          printf 'name: penelope\ninclude: .\ndepend: standard-library prometea henql\n' \
            > $out/penelope.agda-lib
        '';
      };

      # Requires _cache, _stdlib, _prometea, _henql to be set
      # (call after henql.lib.mkShell's hooks).
      copyPenelope = ''
        _penelope="$_cache/penelope"
        if [ ! -d "$_penelope" ]; then
          echo "penelope: copying library to $_penelope (one-time setup)..." >&2
          mkdir -p "$_penelope"
          cp -r ${penelopeLib}/. "$_penelope/"
          chmod -R u+w "$_penelope"
          printf 'name: penelope\ninclude: .\ndepend: standard-library prometea henql\n' \
            > "$_penelope/penelope.agda-lib"
        fi
      '';

    in
    {
      packages.${system} = {
        lib     = penelopeLib;
        default = penelopeLib;
      };

      # Dev shell for working on Penelope itself: stdlib + prometea + henql in AGDA_DIR.
      # Agda resolves penelope.agda-lib by walking up from the source file
      # (vale anche per Examples/Tela.agda, che vive sotto `include: .`).
      devShells.${system}.default = henql.lib.mkShell {
        inherit pkgs;
        extraPackages = with pkgs; [ watchexec ];
      };

      # For consumers: stdlib + prometea + henql + penelope in AGDA_DIR.
      lib.mkShell = { pkgs, extraPackages ? [], shellHook ? "" }:
        henql.lib.mkShell {
          inherit pkgs extraPackages;
          shellHook = copyPenelope + ''
            mkdir -p "$_cache/penelope-env"
            printf '%s\n%s\n%s\n%s\n' \
              "$_stdlib/standard-library.agda-lib" \
              "$_prometea/prometea.agda-lib" \
              "$_henql/henql.agda-lib" \
              "$_penelope/penelope.agda-lib" \
              > "$_cache/penelope-env/libraries"
            export AGDA_DIR="$_cache/penelope-env"
          '' + shellHook;
        };
    };
}
