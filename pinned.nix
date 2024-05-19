import
  (builtins.fetchTarball {
    name = "nixos-23.11";
    url = "https://github.com/nixos/nixpkgs/archive/refs/tags/23.11.tar.gz";
    sha256 = "sha256:1ndiv385w1qyb3b18vw13991fzb9wg4cl21wglk89grsfsnra41k";
  })
  {}
