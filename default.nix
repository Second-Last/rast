{ lib
, mlton
, stdenv
}:

stdenv.mkDerivation rec {
  pname = "rast";
  version = "2024-03-22";

  src = ./.;

  nativeBuildInputs = [ mlton ];

  buildPhase = ''
    make -C rast/src
  '';

  installPhase =''
    mkdir -p $out/bin
    cp rast/src/rast $out/bin/
  '';

  meta = with lib; {
    homepage = "https://bitbucket.org/fpfenning/rast/src/master/rast/";
    description = ''
      An implementation of two fragments of Resource-Aware Session Types (Rast): subsingleton logic and pure linear logic. Both support index objects from arithmetic and temporal ergometric types to express and check parallel time and total work.
    '';
    licenses = licenses.mit;
  };
}
