#options --syntax=explicit --terminate=equi
#test error

% one of the processes fails to terminate

% Binary numbers
% no leading 0s permitted

% without intersections and subtyping, this requires a lot of
% code duplication

type std = +{b0 : pos, b1 : std, e : 1}
type pos = +{b0 : pos, b1 : std}

proc Rb1 : std |- std
proc Re : 1 |- std
proc Rb1 = R.b1 ; <->
proc Re = R.e ; <->

proc zero : std
proc zero = R.e ; closeR

proc ex0 : std
proc ex0 = zero
exec ex0

proc error_pos : pos
proc error_pos = error_pos

proc std2std : std |- std       % could use <->
proc pos2pos : pos |- pos       % could use <->
proc pos2std : pos |- std       % total identity coercion
proc std2pos : std |- pos       % partial coercion; can go into an infinite loop!

proc std2std = caseL ( b0 => R.b0 ; pos2pos
                     | b1 => R.b1 ; std2std
                     | e => R.e ; waitL ; closeR )
proc pos2pos = caseL ( b0 => R.b0 ; pos2pos
                     | b1 => R.b1 ; std2std )
proc pos2std = caseL ( b0 => R.b0 ; pos2pos
                     | b1 => R.b1 ; std2std )
proc std2pos = caseL ( b0 => R.b0 ; pos2pos
                     | b1 => R.b1 ; std2std
                     | e => waitL ; error_pos )

proc succ : std |- pos
proc succ = caseL ( b0 => R.b1 ; pos2std
                  | b1 => R.b0 ; succ
                  | e => R.b1 ; waitL ; R.e ; closeR )

proc ex3 : pos
proc ex3 = zero || succ || pos2std || succ || pos2std || succ
exec ex3

proc dbl : std |- std
proc dbl = caseL ( b0 => R.b0 ; R.b0 ; <->
                 | b1 => R.b0 ; R.b1 ; <->
                 | e => R.e ; <-> )

proc pred : pos |- std          % no type ? |- pos
proc pred = caseL ( b0 => R.b1 ; pred
                  | b1 => dbl)        % avoid introducing leading 0!

proc ex2 : std
proc ex2 = ex3 || pred
exec ex2

proc one : pos
proc one = zero || succ 

proc ex1 : pos
proc ex1 = one
exec ex1

% width x = number of bits x (roughly the log)
proc width : std |- std
proc width = caseL ( b0 => pos2std || width || succ || pos2std
                   | b1 => width || succ || pos2std
                   | e => R.e ; <-> )

proc ex7 : std
proc ex7 = R.b1 ; R.b1 ; R.b1 ; R.e ; closeR

proc ex3b : std
proc ex3b = ex7 || width

% sq2 x = x * x for x = 2^y
proc sq2 : std |- std
proc sq2 = caseL ( b0 => pos2std || sq2 || dbl || dbl % (2x)^2 = 4x^2
                 | b1 => sq2 || dbl || succ || pos2std     % (2x+1)^2 = 4x^2 + 4x + 1, but x = 0!
                 | e => Re )               % 0^2 = 0

proc ex64 : std
proc ex64 = ex7 || succ || pos2std || sq2
exec ex64

% exp x = 2^x
proc exp2 : std |- std
proc exp2 = caseL ( b0 => pos2std || exp2 || sq2  % 2^(2x) = (2^x)^2
                  | b1 => exp2 || sq2 || dbl      % 2^(2x+1) = 2*2^(2x)
                  | e =>  Re || Rb1 )

proc ex5 : std
proc ex5 = ex7 || std2pos || pred || std2pos || pred  % partial coercions used here!

proc ex32 : std
proc ex32 = ex5 || exp2
exec ex32
