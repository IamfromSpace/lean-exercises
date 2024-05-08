let
  pkgs = import ./pinned.nix;
in
  pkgs.mkShell {
    nativeBuildInputs =
      [ pkgs.lean4
      ];
  }
