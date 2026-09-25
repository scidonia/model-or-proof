{
  description = "model-or-proof: wall-clock and cost comparison between TLA+ model checking and theorem-prover verification closed by an AI proof loop";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.${system}.default = pkgs.mkShell {
        packages = with pkgs; [
          tlaplus # TLC, the model checking side
          python3 # harness
          python3Packages.pytest # scenario runner
          jq # result-row inspection
          z3 # SMT solver available to the prover side
        ];
      };
    };
}
