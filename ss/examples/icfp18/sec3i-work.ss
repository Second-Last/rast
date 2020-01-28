#options --work=send --syntax=implicit

type bits1 = +{b0 : |>bits1, b1 : |>bits1, $ : |>|> 1}

type bits0 = +{b0 : bits0, b1 : bits0, $ : 1}

proc copy : bits1 |- bits0

proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy
                  | $  => R.$ ; waitL ; closeR )

proc plus1 : bits1 |{1}- bits0

proc plus1 = caseL ( b0 => R.b1 ; copy
                   | b1 => R.b0 ; plus1
                   | $  => R.b1 ; R.$ ; waitL ; closeR )

% This is an imprecise type since each message carries a potential of 1
% We only need potential in the b0, $ and leading b1 messages

proc compress : bits1 |- bits0
proc skip1s : bits1 |- bits0

proc compress = caseL ( b0 => R.b0 ; compress
                      | b1 => R.b1 ; skip1s
                      | $  => R.$ ; waitL ; closeR )

proc skip1s = caseL ( b0 => R.b0 ; compress
                    | b1 => skip1s
                    | $  => R.$ ; waitL ; closeR )

% We can fix this problem by introducing a more precise type
% Basically, we start with bits1' and on encountering a b1, we switch to fbits1
% fbits1 provides no potential for the b1 bits

type pbits1 = +{b0 : |>pbits1, b1 : |> fbits1, $ : |>|> 1}
type fbits1 = +{b0 : |> pbits1, b1 : fbits1, $ : |>|> 1}

proc pcompress : pbits1 |- bits0
proc pskip1s : fbits1 |- bits0

proc pcompress = caseL ( b0 => R.b0 ; pcompress
                       | b1 => R.b1 ; pskip1s
                       | $  => R.$ ; waitL ; closeR )

proc pskip1s = caseL ( b0 => R.b0 ; pcompress
                     | b1 => pskip1s
                     | $  => R.$ ; waitL ; closeR )

