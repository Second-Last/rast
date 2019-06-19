#options --syntax=implicit
#test success

% this fails because eagerly receiving
% p:n >= 0 from the left means the left
% type 'one' does not match the left type
% of finish{3} : ?{3 >= 0}. one.  This could
% be fixed by using subtyping:
% n = 3 |- one <: ?{n >= 0}.one witnessed by
% n = 3 |= (assertR {n >= 0} ; <->) : one |- ?{3 >= 0}.one

type one = 1
type get1{n} = &{get: ?{n > 0-1}. one}

proc finish{n} : ?{n > 0-1}. one |- one
proc finish{n} = waitL ; closeR

proc test : get1{3} |- one
proc test = L.get ; finish{3} || <->
