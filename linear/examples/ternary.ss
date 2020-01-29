#test success
#options

%%% Balanced ternary representation of integers
%%% Because our index domains is natural numbers,
%%% only the natural numbers are permitted here.
%%% To change this, we would have to either change
%%% the index domain or index ternary numbers with
%%% pairs tern{p}{n} representing a if a = p-n.

%%% We do not bother with disallowing leading zeros.

type tern{a} =
  +{ m1 : ?b. ?{a+1 = 3*b}. tern{b},   % a = 3*b-1
     z0 : ?b. ?{a = 3*b}. tern{b},   % a = 3*b
     p1 : ?b. ?{a = 3*b+1}. tern{b},   % a = 3*b+1
     e : ?{a = 0}. 1 }         % a = 0

decl zero : . |- (x : tern{0})
proc x <- zero = x.e ; close x

decl one : . |- (x : tern{1})
proc x <- one = x.p1 ; send x {0} ; x.e ; close x

(*
decl m_one : . |- (x : tern{-1})
proc x <- m_one = x.m1 ; send x {0} ; x.e ; close x
*)

(*
decl neg : (x : tern{a}) |- (y : tern{-a})
proc y <- neg{a} x =
 case x ( m1 => {a'} <- recv x ;
                y.p1 ; send y {-a'} ;
                y <- neg{a'} x
        | z0 => {a'} <- recv x ;
                y.z0 ; send y {-a'} ;
                y <- neg{a'} x
        | p1 => {a'} <- recv x ;
                y.m1 ; send y {-a'} ;
                y <- neg{a'} x
        | e => wait x ;
               y.e ; close y )
*)

decl succ{a} : (x : tern{a}) |- (y : tern{a+1})
proc y <- succ{a} x =
  case x ( m1 => {a'} <- recv x ;
                 y.z0 ; send y {a'} ;
                 y <-> x
         | z0 => {a'} <- recv x ;
                 y.p1 ; send y {a'} ;
                 y <-> x
         | p1 => {a'} <- recv x ;
                 y.m1 ; send y {a'+1} ;
                 y <- succ{a'} x
         | e => y.p1 ; send y {0} ;
                y.e ; wait x ; close y )

decl pred{a} : (x : tern{a+1}) |- (y : tern{a})
proc y <- pred{a} x =
  case x ( m1 => {a'} <- recv x ;       % a+2 = 3*a', x : tern{a'} |- y : tern{a}
                 y.p1 ; send y {a'-1} ; % a = 3*(a'-1)+1, x : tern{a'} |- y : tern{a'-1}
                 y <- pred{a'-1} x
         | z0 => {a'} <- recv x ;
                 y.m1 ; send y {a'} ;
                 y <-> x
         | p1 => {a'} <- recv x ;
                 y.z0 ; send y {a'} ;
                 y <-> x
         % impossible here, due to natural numbers
         % | e => y.m1 ; send y {0} ;
         %      y.e ; wait x ; close y
         )


%%% This would be easier to write with processes
%%% triple_m1, triple_z0, and triple_p1 but we output
%%% the ternary bits directly, for stylistic variety.
%%% Crib sheet:
(* 
  2*(3n-1) = 3(2*n)-2 = 3(2*n-1)+1
  2*(3n+0) = 3(2*n)+0
  2*(3n+1) = 3(2*n)+2 = 3(2*n+1)-1
*)

decl dbl{a} : (x : tern{a}) |- (y : tern{2*a})
proc y <- dbl{a} x =
  case x ( m1 => {a'} <- recv x ;       % a+1 = 3*a', x : tern{a'} |- y : tern{2*a}
                 y.p1 ; send y {2*a'-1} ; % a+1 = 3*a', 2*a = 3*(2*a')+1, x : tern{a'} |- y : tern{2*a'-1}
                 z <- dbl{a'} x ;    % a+1 = 3*a', 2*a = 3*(2*a')+1, z : tern{2*a'} |- y : tern{2*a'-1}
                 y <- pred{2*a'-1} z
         | z0 => {a'} <- recv x ;
                 y.z0 ; send y {2*a'} ;
                 y <- dbl{a'} x
         | p1 => {a'} <- recv x ;
                 y.m1 ; send y {2*a'+1} ;
                 z <- dbl{a'} x ;
                 y <- succ{2*a'} z
         | e => wait x ;
                y.e ; close y )

%%% from arith.ss
%---------------
type bin{n} = +{ b0 : ?{n > 0}. ?k. ?{n = 2*k}. bin{k},
                 b1 : ?{n > 0}. ?k. ?{n = 2*k+1}. bin{k},  % n > 0 is redundant here
                 e : ?{n = 0}. 1 }

decl zero_bin : . |- (x : bin{0})
decl succ_bin{n} : (x : bin{n}) |- (y : bin{n+1})

proc x <- zero_bin = x.e ; close x

proc y <- succ_bin{n} x =
  case x ( b0 => {n'} <- recv x ;
                 y.b1 ; send y {n'} ;
                 y <-> x
         | b1 => {n'} <- recv x ;
                 y.b0 ; send y {n'+1} ;
                 y <- succ_bin{n'} x
         | e => y.b1 ; send y {0} ;
                y.e ; wait x ; close y )

%%% Building numbers without leading zeros
decl dbl0{n} : (x : bin{n}) |- (y : bin{2*n})
decl dbl1{n} : (x : bin{n}) |- (y : bin{2*n+1})

proc y <- dbl0{n} x =
  case x ( b0 => {n'} <- recv x ;
                 y.b0 ; send y {n} ;
                 y.b0 ; send y {n'} ;
                 y <-> x
         | b1 => {n'} <- recv x ;
                 y.b0 ; send y {n} ;
                 y.b1 ; send y {n'} ;
                 y <-> x
         | e => y.e ; wait x ; close y )

proc y <- dbl1{n} x =
  y.b1 ; send y {n} ;
  y <-> x

%%% Predecessor defined only on strictly positive numbers
%%% It would be simpler to say (x : bin{n+1}) |- (y : bin{n}).
%%% We chose this formulation for stylistic variety

decl pred_bin{n|n > 0} : (x : bin{n}) |- (y : bin{n-1})
proc y <- pred_bin{n} x =
  case x ( b0 => {n'} <- recv x ;    % 2*k-1 = 2*(k-1)+1
                 y.b1 ; send y {n'-1} ;
                 y <- pred_bin{n'} x
         | b1 => {n'} <- recv x ;
                 y <- dbl0{n'} x  % 2*k+1-1 = 2*k
         % no case for e
         )
%---------------
%%% end from arith.ss

% 3*(2n+0) = 6*n   = 2(3*n)+0
% 3*(2n+1) = 6*n+3 = 2((3*n)+1)+1
% 3*0 = 0
decl times3{n} : (x : bin{n}) |- (y : bin{3*n})
proc y <- times3{n} x =
  case x ( b0 => {n'} <- recv x ;
                 z <- times3{n'} x ;
                 y <- dbl0{3*n'} z
         | b1 => {n'} <- recv x ;
                 z <- times3{n'} x ;
                 w <- succ_bin{3*n'} z ;
                 y <- dbl1{3*n'+1} w
         | e => wait x ;
                y <- zero_bin
         )


decl tern2bin{n} : (x : tern{n}) |- (y : bin{n})
proc y <- tern2bin{n} x =
  case x ( m1 => {n'} <- recv x ;
                 z <- tern2bin{n'} x ;
                 w <- times3{n'} z ;
                 y <- pred_bin{3*n'} w
                 % tern2bin || times3 || pred
         | z0 => {n'} <- recv x ;
                 z <- tern2bin{n'} x ;
                 y <- times3{n'} z
                 % tern2bin || times3
         | p1 => {n'} <- recv x ;
                 z <- tern2bin{n'} x ;
                 w <- times3{n'} z ;
                 y <- succ_bin{3*n'} w
         | e => wait x ;
                y <- zero_bin
         )

decl bin2tern{n} : (x : bin{n}) |- (y : tern{n})
proc y <- bin2tern{n} x =
  case x ( b0 => {k} <- recv x ;
                 z <- bin2tern{k} x ;
                 y <- dbl{k} z
                 % bin2tern || dbl
         | b1 => {k} <- recv x ;
                 z <- bin2tern{k} x ;
                 w <- dbl{k} z ;
                 y <- succ{2*k} w
                 % bin2tern || dbl || inc
         | e => wait x ;
                y <- zero
         )
