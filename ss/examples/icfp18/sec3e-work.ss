#options --work=send --time=none --syntax=explicit

type bits1 = +{b0 : |>bits1, b1 : |>bits1, $ : |>|> 1}

type bits0 = +{b0 : bits0, b1 : bits0, $ : 1}

proc copy : bits1 |- bits0

proc copy = caseL ( b0 => getL ; R.b0 ; copy
                  | b1 => getL ; R.b1 ; copy
                  | $  => getL ; R.$ ; getL ; waitL ; closeR )

proc plus1 : bits1 |{1}- bits0

proc plus1 = caseL ( b0 => getL ; R.b1 ; work ; copy
                   | b1 => getL ; R.b0 ; plus1
                   | $  => getL ; R.b1 ; getL ; R.$ ; waitL ; closeR )

proc zero : . |{4}- bits1

proc zero = R.$ ; payR ; payR ; closeR

exec zero

proc one : . |{5}- bits0

proc one = zero || plus1

exec one

(* would need to rewrite for explicit syntax *)
(*
type bits3 = +{b0 : |>|>bits3, b1 : |>|>bits3, $ : |>|>|>|>|>|> 1}
proc plus2 : bits3 |- bits0

proc plus2 = plus1 || plus1
*)

% This is an imprecise type since each message carries a potential of 1
% We only need potential in the b0, $ and leading b1 messages

proc compress : bits1 |- bits0
proc skip1s : bits1 |- bits0

proc compress = caseL ( b0 => getL ; R.b0 ; compress
                      | b1 => getL ; R.b1 ; skip1s
                      | $  => getL ; R.$ ; getL ; waitL ; closeR )

proc skip1s = caseL ( b0 => getL ; R.b0 ; compress
                    | b1 => getL ; work ; skip1s
                    | $  => getL ; R.$ ; getL ; waitL ; closeR )

proc x : . |{20}- bits1

proc x = R.b1 ; payR ; R.b0 ; payR ; R.b1 ; payR ; R.b1 ; payR ; R.b1 ; payR ; 
         R.b0 ; payR ; R.b1 ; payR ; R.b1 ; payR ; R.$ ; payR ; payR ; closeR

exec x

proc x_compressed : . |{20}- bits0

proc x_compressed = x || compress

exec x_compressed

% We can fix this problem by introducing a more precise type
% Basically, we start with bits1' and on encountering a b1, we switch to fbits1
% fbits1 provides no potential for the b1 bits

type pbits1 = +{b0 : |>pbits1, b1 : |> fbits1, $ : |>|> 1}
type fbits1 = +{b0 : |> pbits1, b1 : fbits1, $ : |>|> 1}

proc pcompress : pbits1 |- bits0
proc pskip1s : fbits1 |- bits0

proc pcompress = caseL ( b0 => getL ; R.b0 ; pcompress
                       | b1 => getL ; R.b1 ; pskip1s
                       | $  => getL ; R.$ ; getL ; waitL ; closeR )

proc pskip1s = caseL ( b0 => getL ; R.b0 ; pcompress
                     | b1 => pskip1s
                     | $  => getL ; R.$ ; getL ; waitL ; closeR )

proc fx : . |{17}- pbits1

proc fx = R.b1 ; payR ; R.b0 ; payR ; R.b1 ; payR ; R.b1 ; R.b1 ; 
         R.b0 ; payR ; R.b1 ; payR ; R.b1 ; R.$ ; payR ; payR ; closeR

exec fx

proc fx_compressed : . |{17}- bits0

proc fx_compressed = fx || pcompress

exec fx_compressed

