{
  description = "agda-parametricity: Deriving parametricity results in Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Build the parametricity library using agdaPackages.mkDerivation
        # This follows modern Agda library packaging conventions
        parametricity = pkgs.agdaPackages.mkDerivation {
          pname = "parametricity";
          version = "0.0.3";

          # libraryName should match the name in parametricity.agda-lib
          libraryName = "parametricity";

          # libraryFile specifies the .agda-lib filename
          libraryFile = "parametricity.agda-lib";

          src = ./.;

          # Declare dependencies - mkDerivation makes these available during build
          buildInputs = [ pkgs.agdaPackages.standard-library ];

          # The default buildPhase runs: agda --build-library
          # This automatically builds all modules listed in the .agda-lib
          # No need to override unless custom build steps are required

          meta = with pkgs.lib; {
            description = "Deriving parametricity results in Agda: theorems for free";
            homepage = "https://github.com/np/agda-parametricity";
            license = licenses.bsd3;
            platforms = platforms.unix;
            maintainers = [ ];
          };
        };

        # Agda with standard library and parametricity for development
        agdaWithPackages = pkgs.agda.withPackages (ps: [
          ps.standard-library
          # Can add other dependencies here as needed
        ]);

      in {
        packages = {
          default = parametricity;
          parametricity = parametricity;
        };

        # Development shell with Agda and tools
        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithPackages
            pkgs.git
          ];

          shellHook = ''
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Agda parametricity development environment"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Agda version: $(agda --version | head -n1)"
            echo ""
            echo "Available commands:"
            echo "  agda parametricity.agda       - Type check main module"
            echo "  agda --build-library           - Build entire library"
            echo "  agda --library=parametricity   - Use library explicitly"
            echo "  nix build                      - Build the library package"
            echo "  nix flake check                - Run checks"
            echo ""
            echo "Library file: parametricity.agda-lib"
            echo "Dependencies: standard-library"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
          '';
        };

        # Alias for backwards compatibility
        devShell = self.devShells.${system}.default;

        # Check that the library type-checks
        checks = {
          type-check = parametricity;
        };
      }
    );
}
