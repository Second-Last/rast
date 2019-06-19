#options --work=none --syntax=implicit
#test error

type nat{n} = +{z : ?{n = 0}. 1,
                s : ?{n > 0}. nat{n-1}}
type even{n} = +{z : ?{n = 0}. 1,
                 s : ?{n > 0}. odd{n-1}}
type odd{n} = +{s : ?{n > 0}. even{n-1}}

proc zero : nat{0}
proc zero = R.z ; closeR

proc succ{n} : nat{n} |- nat{n+1}
proc succ{n} = R.s ; <->

% without subtyping, write coercions
proc even2nat{n} : even{n} |- nat{n}
proc odd2nat{n} : odd{n} |- nat{n}

proc even2nat{n} =
  caseL ( z => R.z ; <->
        | s => R.s ; odd2nat{n-1} )
proc odd2nat{n} =
  caseL ( s => R.s ; even2nat{n-1} )


proc nat2even{n} : nat{2*n} |- even{2*n}
proc nat2odd{n} : nat{2*n+1} |- odd{2*n+1}

proc nat2even{n} =
  caseL ( z => R.z ; <->
        | s => R.s ; nat2odd{n-1} )
proc nat2odd{n} =
  caseL ( z => impossibleL {2*n+1 = 0} % not allowed with implicit syntax
        | s => R.s ; nat2even{n} )

proc double{n} : nat{n} |- even{2*n}
proc double{n} =
  caseL ( z => R.z ; waitL ; closeR
        | s => R.s ; R.s ; double{n-1} )

proc quadruple{n} : nat{n} |- even{4*n}
proc quadruple{n} = double{n} || even2nat{2*n} || double{2*n}

proc quad_test : even{8}
proc quad_test = zero || succ{0} || succ{1} || quadruple{2}
exec quad_test

% ----------------

type bare_nat = +{z : 1, s : bare_nat}

proc forget{n} : nat{n} |- bare_nat
proc forget{n} =
  caseL ( z => waitL; R.z ; closeR
        | s => R.s ; forget{n-1} )

% the exponential function 2^n can be programmed, but not typed
% proc exp{n} : nat{n} |- nat{2^n}
% proc exp{n} =
%   caseL ( z => R.s ; R.z ; closeR
%         | s => exp{n-1} || double{2^(n-1)} )
