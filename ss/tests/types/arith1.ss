#options --work=none --syntax=explicit
#test success

type nat{n} = +{z : ?{n = 0}. 1,
                s : ?{n > 0}. nat{n-1}}
type even{n} = +{z : ?{n = 0}. 1,
                 s : ?{n > 0}. odd{n-1}}
type odd{n} = +{s : ?{n > 0}. even{n-1}}

proc zero : nat{0}
proc zero = R.z ; assertR {0 = 0} ; closeR

proc succ{n} : nat{n} |- nat{n+1}
proc succ{n} = R.s ; assertR {n+1 > 0} ; <->

% without subtyping, write coercions
proc even2nat{n} : even{n} |- nat{n}
proc odd2nat{n} : odd{n} |- nat{n}

proc even2nat{n} =
  caseL ( z => R.z ; <->
        | s => R.s ;
               assumeL {n > 0} ; assertR {n > 0} ;
               odd2nat{n-1} )
proc odd2nat{n} =
  caseL ( s => R.s ;
               assumeL {n > 0} ; assertR {n > 0} ;
               even2nat{n-1} )


proc nat2even{n} : nat{2*n} |- even{2*n}
proc nat2odd{n} : nat{2*n+1} |- odd{2*n+1}

proc nat2even{n} =
  caseL ( z => R.z ; <->
        | s => R.s ;
               assumeL {2*n > 0} ; assertR {2*n > 0} ;
               nat2odd{n-1} )
proc nat2odd{n} =
  caseL ( z => impossibleL {2*n+1 = 0}
        | s => R.s ;
               assumeL {2*n+1 > 0} ; assertR {2*n+1 > 0} ;
               nat2even{n} )

proc double{n} : nat{n} |- even{2*n}
proc double{n} =
  caseL ( z => R.z ; assumeL {n = 0} ; assertR {n = 0};
               waitL ; closeR
        | s => assumeL {n > 0} ;
               R.s ; assertR {n > 0} ;
               R.s ; assertR {n+1 > 0} ;
               double{n-1} )

proc quadruple{n} : nat{n} |- even{4*n}
proc quadruple{n} = double{n} || even2nat{2*n} || double{2*n}

proc quad_test : even{8}
proc quad_test = zero || succ{0} || succ{1} || quadruple{2}
exec quad_test

% ----------------

type bare_nat = +{z : 1, s : bare_nat}

proc forget{n} : nat{n} |- bare_nat
proc forget{n} =
  caseL ( z => assumeL {n = 0}; waitL; R.z ; closeR
        | s => assumeL {n > 0}; R.s ; forget{n-1} )

% the exponential function 2^n can be programmed, but not typed
% proc exp{n} : nat{n} |- nat{2^n}
% proc exp{n} =
%   caseL ( z => assumeL {n = 0} ; R.s ; assertR {2^0 > 0} ; R.z ; assertR {0 = 0} ; closeR
%         | s => assumeL {n > 0} ; (exp{n-1} || double{2^(n-1)}) )

proc dbl : bare_nat |- bare_nat
proc dbl =
  caseL ( z => R.z ; waitL ; closeR
        | s => R.s ; R.s ; dbl )

proc exp : bare_nat |- bare_nat
proc exp =
  caseL ( z => R.s ; R.z ; waitL ; closeR
        | s => exp || dbl )

proc n32 : bare_nat
proc n32 = zero || succ{0} || succ{1} || succ{2} || succ{3} || succ{4} || forget{5} || exp
exec n32
