#options --time=recv --syntax=implicit --terminate=equi
#test success

% This uses the lax model of cost: we can insert imaginary
% actions (assert, assume) before the temporal cost of an action
% has been accounted for.
%
% see modarith-time-i-strict.ss for a more complicated version
% that insists on a strict sequencing

type word{w} = +{ b0 : ?{w > 0}. ()word{w-1},
                  b1 : ?{w > 0}. ()word{w-1},
                  e  : ?{w = 0}. ()1 }

% 0
proc zero : word{4}
proc zero = R.b0 ; R.b0 ; R.b0 ; R.b0 ; R.e ; closeR

% copy n = n
proc copy{w} : word{w} |- ()word{w}
proc copy{w} = caseL ( b0 => R.b0 ; copy{w-1}
                     | b1 => R.b1 ; copy{w-1}
                     | e  => R.e  ; waitL ; closeR )

% succ n = n+1
proc succ{w} : word{w} |- ()word{w}
proc succ{w} = caseL ( b0 => R.b1 ; copy{w-1}
                     | b1 => R.b0 ; succ{w-1}
                     | e  => R.e ; waitL ; closeR ) % mod 2^w!

% pred n = n-1
proc pred{w} : word{w} |- ()word{w}
proc pred{w} = caseL ( b0 => R.b1 ; pred{w-1}
                     | b1 => R.b0 ; copy{w-1}
                     | e  => R.e ; waitL ; closeR )

% comp n = ~n (bitwise complement)
proc comp{w} : word{w} |- ()word{w}
proc comp{w} = caseL ( b0 => R.b1 ; comp{w-1}
                     | b1 => R.b0 ; comp{w-1}
                     | e  => R.e ; waitL ; closeR )

% neg n = -n
proc neg{w} : word{w} |- ()()word{w}
proc neg{w} = comp{w} || succ{w}

% -1 = ~0
proc minus_one_a : ()()word{4}
proc minus_one_a = zero || neg{4}
exec minus_one_b

% -1 = 0-1
proc minus_one_b : ()word{4}
proc minus_one_b = zero || pred{4}
exec minus_one_b

% shl0 n = 2*n
% shl1 n = 2*n+1
proc shl0{w} : word{w} |- ()word{w} (* shift left, fill in 0 *)
proc shl1{w} : word{w} |- ()word{w} (* shift left, fill in 1 *)

proc shl0{w} = caseL ( b0 => R.b0 ; shl0{w-1}
                     | b1 => R.b0 ; shl1{w-1}
                     | e  => R.e ; waitL ; closeR )
proc shl1{w} = caseL ( b0 => R.b1 ; shl0{w-1}
                     | b1 => R.b1 ; shl1{w-1}
                     | e  => R.e ; waitL ; closeR )

% 8 = -8 = (0+1)<<3
proc eight : ({4})word{4}
proc eight = zero || succ{4} || shl0{4} || shl0{4} || shl0{4}
exec eight

% shr n = n/2, preserving sign and rounding towards -infinity
proc shr{w}  : word{w} |- ()()word{w}
proc shr0{w} : word{w} |- ()word{w+1}  % copy each bit, left filling with 0
proc shr1{w} : word{w} |- ()word{w+1}  % copy each bit, left filling with 1

proc shr{w} = caseL ( b0 => shr0{w-1}
                    | b1 => shr1{w-1}
                    | e  => waitL ; R.e ; closeR )

proc shr0{w} = caseL ( b0 => R.b0 ; shr0{w-1}
                     | b1 => R.b1 ; shr1{w-1}
                     | e  => R.b0 ;          (* copy last bit, which was 0 *)
                             waitL ; R.e ; closeR )

proc shr1{w} = caseL ( b0 => R.b0 ; shr0{w-1}
                     | b1 => R.b1 ; shr1{w-1}
                     | e  => R.b1 ;          (* copy last bit, which was 0 *)
                             waitL ; R.e ; closeR )

% -8>>1 = -4
proc minus_four : ({4+2})word{4}
proc minus_four = eight || shr{4}
exec minus_four

% 6 = (0+1+1+1)*2
proc six : ({4})word{4}
proc six = zero || succ{4} || succ{4} || succ{4} || shl0{4}
exec six

% 3 = 6>>1
proc three : ({4+2})word{4}
proc three = six || shr{4}
exec three

% 1 = 3>>1
proc one : ({4+2+2})word{4}
proc one = three || shr{4}
exec one

(*
proc drain : word{w} |- ({w+2})1
proc drain{w} = caseL ( b0 => drain{w-1}
                      | b1 => drain{w-1}
                      | e => waitL ; closeR )
*)

proc finish : word{0} |- ()()1
proc finish = caseL ( e => waitL ; closeR )

(*
 * To represent binary operations we use an alternating
 * interleaving of the two numbers.  Because we are in the
 * subsingleton fragment, we cannot create this but we have
 * to apply unary operations to the even or odd bits of
 * the interleaved representation.
 *
 * To replicate or operate on these numbers, rates are
 * doubled or cut in half, so we need a more general type
 * of word.
 *)

type wordx{w}{r} = +{ b0 : ?{w > 0}. ()({r})wordx{w-1}{r},
                      b1 : ?{w > 0}. ()({r})wordx{w-1}{r},
                      e  : ?{w = 0}. ()1 }

% ? proc duplicate : wordx{w}{2*r+1} |- ()wordx{2*w}{r}
proc duplicate{w} : wordx{w}{1} |- ()wordx{2*w}{0}
proc duplicate{w} =
     caseL ( b0 => R.b0 ; R.b0 ; duplicate{w-1}
           | b1 => R.b1 ; R.b1 ; duplicate{w-1}
           | e => R.e ; waitL ; closeR )

% *_e = applies to even bits, *_o to odd bits
proc copy_e{w} : wordx{2*w}{0} |- ()wordx{2*w}{0}
proc copy_o{w} : wordx{2*w+1}{0} |- ()wordx{2*w+1}{0}
proc copy_e{w} = caseL ( b0 => R.b0 ; copy_o{w-1}
                       | b1 => R.b1 ; copy_o{w-1}
                       | e  => R.e ; waitL ; closeR )
proc copy_o{w} = caseL ( b0 => R.b0 ; copy_e{w}
                       | b1 => R.b1 ; copy_e{w}
                       % e impossible
                       )

proc succ0_e{w} : wordx{2*w}{0} |- ()wordx{2*w}{0}
proc succ0_o{w} : wordx{2*w+1}{0} |- ()wordx{2*w+1}{0}
proc succ0_e{w} =
     caseL ( b0 => R.b1 ; copy_o{w-1}
           | b1 => R.b0 ; succ0_o{w-1}
           | e  => R.e ; waitL ; closeR )
proc succ0_o{w} =
     caseL ( b0 => R.b0 ; succ0_e{w}
           | b1 => R.b1 ; succ0_e{w}
           % e impossible
           )

proc succ1_e{w} : wordx{2*w}{0} |- ()wordx{2*w}{0}
proc succ1_o{w} : wordx{2*w+1}{0} |- ()wordx{2*w+1}{0}
proc succ1_e{w} =
     caseL ( b0 => R.b0 ; succ1_o{w-1}
           | b1 => R.b1 ; succ1_o{w-1}
           | e  => R.e ; waitL ; closeR )
proc succ1_o{w} =
     caseL ( b0 => R.b1 ; copy_e{w}
           | b1 => R.b0 ; succ1_e{w}
           % e impossible
           )

% ? proc plus : wordx{2*w}{r} |- ()()wordx{w}{2*r+1}
proc plus{w} : wordx{2*w}{0} |- ()()wordx{w}{1}
proc plus1{w} : wordx{2*w}{0} |- ()()wordx{w}{1}
proc plus{w} =
     caseL ( b0 => caseL ( b0 => R.b0 ; plus{w-1}
                         | b1 => R.b1 ; plus{w-1} )
           | b1 => caseL ( b0 => R.b1 ; plus{w-1}
                         | b1 => R.b0 ; plus1{w-1} )
           | e  => waitL ; R.e ; closeR ) % waitL first, otherwise output comes too soon
proc plus1{w} =
     caseL ( b0 => caseL ( b0 => R.b1 ; plus{w-1}
                         | b1 => R.b0 ; plus1{w-1} )
           | b1 => caseL ( b0 => R.b0 ; plus1{w-1}
                         | b1 => R.b1 ; plus1{w-1} )
           | e  => waitL ; R.e ; closeR ) % waitL first, otherwise output comes too soon

proc threex : wordx{4}{1}
proc threex = R.b1 ; R.b1 ; R.b0 ; R.b0 ; R.e ; closeR

% (3+2)+(3+1) = 9
proc nine : ({6})wordx{4}{1}
proc nine = threex        %     0011 =   <3> : wordx{4}{1}
         || duplicate{4}  % 00001111 = <3,3> : ()wordx{8}{0}
         || succ0_e{4}    % 00011010 = <3,4> : ()()wordx{8}{0}
         || succ0_e{4}    % 00011011 = <3,5> : ()()()wordx{8}{0}
         || succ1_e{4}    % 00110001 = <4,5> : (4)wordx{8}{0}
         || plus{4}       %     1001 :   <9> : (6)wordx{4}{1}
exec nine
