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
          elan # Lean toolchain manager — the toolchain version comes from Mathlib's lean-toolchain
          git # lake materializes Mathlib from git; declared here so provisioning is not host-dependent
          curl # `lake exe cache get` fetches oleans over HTTP
          python3 # harness
          python3Packages.pytest # scenario runner
          jq # result-row inspection
          z3 # SMT solver available to the prover side
        ];
      };
    };
}
