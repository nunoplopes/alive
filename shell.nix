{ pkgs ? import <nixpkgs> {} }:


pkgs.mkShell {
  packages =
    let
      my-python-packages = ps: with ps; [ z3 stopit ];
    in
    [
      (pkgs.python2.withPackages my-python-packages)
    ];
}
