{ description = "Application packaged using poetry2nix";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.poetry2nix =
    { url = "github:nix-community/poetry2nix/master";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";             };

  outputs = {self, nixpkgs, flake-utils, poetry2nix}:
    let out =
      system: let
        pkgs = import nixpkgs {inherit system;  overlays = [poetry2nix.overlay];};
        python = pkgs.python310;
        poetryEnv = pkgs.poetry2nix.mkPoetryEnv
          { inherit python;  projectDir = ./.;
            overrides = [pkgs.poetry2nix.defaultPoetryOverrides]; };
        tl = with pkgs;
          ( texlive.combine
            { inherit (texlive) scheme-basic standalone xkeyval pgf tikz-cd; } );
        pyEnv = python.withPackages (p: with p; [poetry]);
      in rec
        { devShell = pkgs.mkShell { buildInputs = [tl pkgs.pdf2svg pyEnv]; };
          packages.default = devShell;                           };
    in
      with flake-utils.lib; eachSystem defaultSystems out;                         }
