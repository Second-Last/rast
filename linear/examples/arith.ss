#test approx success
#options --syntax=implicit

%%% Binary arithmetic
%%% Natural numbers indexed by value, with no leading zeros allowed
%%% One example (multiplication) has nonlinear constraints,
%%% therefore this file is labeled as 'approx success'

%%% bin{n} = binary numbers of value n, no leading zeros allowed
type bin{n} = +{ b0 : ?{n > 0}. ?k. ?{n = 2*k}. bin{k},
                 b1 : ?{n > 0}. ?k. ?{n = 2*k+1}. bin{k},  % n > 0 is redundant here
                 e : ?{n = 0}. 1 }

decl zero : . |- (x : bin{0})
decl succ{n} : (x : bin{n}) |- (y : bin{n+1})

proc x <- zero <- = x.e ; close x

proc y <- succ{n} <- x =
  case x ( b0 => {n'} <- recv x ;
                 y.b1 ; send y {n'} ;
                 y <- x
         | b1 => {n'} <- recv x ;
                 y.b0 ; send y {n'+1} ;
                 y <- succ{n'} <- x
         | e => y.b1 ; send y {0} ;
                y.e ; wait x ; close y )

decl plus{m}{n} : (x : bin{m}) (y : bin{n}) |- (z : bin{m+n})
proc z <- plus{m}{n} <- x y =
  case x ( b0 => {m'} <- recv x ;
                 case y ( b0 => {n'} <- recv y ;
                                z.b0 ; send z {m'+n'} ;
                                z <- plus{m'}{n'} <- x y
                        | b1 => {n'} <- recv y ;
                                z.b1 ; send z {m'+n'} ;
                                z <- plus{m'}{n'} <- x y
                        | e => wait y ;
                               z.b0 ; send z {m'} ;
                               z <- x )
         | b1 => {m'} <- recv x ;
                 case y ( b0 => {n'} <- recv y ;
                          z.b1 ; send z {m'+n'} ;
                          z <- plus{m'}{n'} <- x y
                        | b1 => {n'} <- recv y ;
                          z.b0 ; send z {m'+n'+1} ;
                          w <- plus{m'}{n'} <- x y ;
                          z <- succ{m'+n'} <- w
                        | e => wait y ;
                               z.b1 ; send z {m'} ;
                               z <- x )
         | e => wait x ; z <- y )

%%% Deallocating a binary number (necessary due to linearity)
decl drop{n} : (x : bin{n}) |- (u : 1)
proc u <- drop{n} <- x =
  case x ( b0 => {n'} <- recv x ; u <- drop{n'} <- x
         | b1 => {n'} <- recv x ; u <- drop{n'} <- x
         | e => wait x ; close u )

%%% Building numbers without leading zeros
decl dbl0{n} : (x : bin{n}) |- (y : bin{2*n})
decl dbl1{n} : (x : bin{n}) |- (y : bin{2*n+1})

proc y <- dbl0{n} <- x =
  case x ( b0 => {n'} <- recv x ;
                 y.b0 ; send y {n} ;
                 y.b0 ; send y {n'} ;
                 y <- x
         | b1 => {n'} <- recv x ;
                 y.b0 ; send y {n} ;
                 y.b1 ; send y {n'} ;
                 y <- x
         | e => y.e ; wait x ; close y )

(*
proc y <- dbl0{n} <- x =
  y.b0 ; send y {n} ;
  y <- x
*)
% gives error
% arith.ss:79.10-79.20:error:assertion not entailed: true |/= 2*n > 0
%  y.b0 ; send y {n} ;
%         ~~~~~~~~~~ 
% because it could introduce leading zeros.


proc y <- dbl1{n} <- x =
  y.b1 ; send y {n} ;
  y <- x

%%% Duplicating a binary number (necessary due to linearity)
decl dup{n} : (x : bin{n}) |- (xx : bin{n} * bin{n} * 1)
proc xx <- dup{n} <- x =
  case x ( b0 => {n'} <- recv x ;
                 xx' <- dup{n'} <- x ;
                 x1' <- recv xx' ;
                 x2' <- recv xx' ; wait xx' ;
                 x1 <- dbl0{n'} <- x1' ; send xx x1 ; 
                 x2 <- dbl0{n'} <- x2' ; send xx x2 ;
                 close xx
         | b1 => {n'} <- recv x ;
                 xx' <- dup{n'} <- x ;
                 x1' <- recv xx' ;
                 x2' <- recv xx' ; wait xx' ;
                 x1 <- dbl1{n'} <- x1' ; send xx x1 ;
                 x2 <- dbl1{n'} <- x2' ; send xx x2 ;
                 close xx
         | e => wait x ;
                x1 <- zero <- ; send xx x1 ;
                x2 <- zero <- ; send xx x2 ;
                close xx )

%%% Predecessor defined only on strictly positive numbers
decl pred{n|n > 0} : (x : bin{n}) |- (y : bin{n-1})
proc y <- pred{n} <- x =
  case x ( b0 => {n'} <- recv x ;    % 2*k-1 = 2*(k-1)+1
                 y.b1 ; send y {n'-1} ;
                 y <- pred{n'} <- x
         | b1 => {n'} <- recv x ;
                 y <- dbl0{n'} <- x  % 2*k+1-1 = 2*k
         % no case for e
         )

% Alternative formulation without explicit constraint
decl pred'{n} : (x : bin{n+1}) |- (y : bin{n})
proc y <- pred'{n} <- x =
  case x ( b0 => {n'} <- recv x ;    % 2*k-1 = 2*(k-1)+1
                 y.b1 ; send y {n'-1} ;
                 y <- pred'{n'-1} <- x
         | b1 => {n'} <- recv x ;
                 y <- dbl0{n'} <- x  % 2*k+1-1 = 2*k
         % no case for e
         )

%%% Orders, to verify comparisons
type ord{m}{n} = +{ lt : ?{m < n}. 1,
                    eq : ?{m = n}. 1,
                    gt : ?{m > n}. 1 }

%%% Typing of comparisons requires
%%% ord{2*m}{2*n} = ord{m}{n}
%%% and ord{2*m+1}{2*n+1} = ord{m}{n}

decl compare{m}{n} : (x : bin{m}) (y : bin{n}) |- (o : ord{m}{n})
proc o <- compare{m}{n} <- x y =
  case x ( b0 => {m'} <- recv x ;
                 case y ( b0 => {n'} <- recv y ;
                                o' <- compare{m'}{n'} <- x y ;  % ord{2*m}{2*n} = ord{m}{n}
                                case o' ( lt => wait o' ;
                                                o.lt ; close o
                                        | eq => wait o' ;
                                                o.eq ; close o
                                        | gt => wait o' ;
                                                o.gt ; close o )
                        | b1 => {n'} <- recv y ;
                                o' <- compare{m'}{n'} <- x y ;  % ord{2*m+1}{2*n+1} = ord{m}{n}
                                case o' ( lt => wait o' ;
                                                o.lt ; close o
                                        | eq => wait o' ;
                                                o.lt ; close o
                                        | gt => wait o' ;
                                                o.gt ; close o )
                        | e => wait y ; u <- drop{m'} <- x ; wait u ;
                               o.gt ; close o )
         | b1 => {m'} <- recv x ;
                 case y ( b0 => {n'} <- recv y ;
                                o' <- compare{m'}{n'} <- x y ;
                                case o' ( lt => wait o' ;
                                                o.lt ; close o
                                        | eq => wait o' ;
                                                o.gt ; close o
                                        | gt => wait o' ;
                                                o.gt ; close o )
                        | b1 => {n'} <- recv y ;
                                o' <- compare{m'}{n'} <- x y ;
                                case o' ( lt => wait o' ;
                                                o.lt ; close o
                                        | eq => wait o' ;
                                                o.eq ; close o
                                        | gt => wait o' ;
                                                o.gt ; close o )
                        | e => wait y ; u <- drop{m'} <- x ; wait u ;
                               o.gt ; close o )
         | e => wait x ;
                case y ( b0 => {n'} <- recv y ;
                               u <- drop{n'} <- y ; wait u ;
                               o.lt ; close o
                       | b1 => {n'} <- recv y ;
                               u <- drop{n'} <- y ; wait u ;
                               o.lt ; close o
                       | e => wait y ;
                              o.eq ; close o ) )

%%% Multiplication requires duplicating and dropping numbers
%%% and generates constraints beyond Presburger arithmetic.
%%% The commented alternative could introduce leading zeros.

decl times{m}{n} : (x : bin{m}) (y : bin{n}) |- (z : bin{m*n})
proc z <- times{m}{n} <- x y =
  case x ( b0 => {m'} <- recv x ;
                 xy <- times{m'}{n} <- x y ;  % (2*x)*y = 2*(x*y)
                 % z.b0 ; send z {m'*n} ;  % bug discovered with refinement types
                 z <- dbl0{m'*n} <- xy
         | b1 => {m'} <- recv x ;
                 yy <- dup{n} <- y ;
                 y1 <- recv yy ; y2 <- recv yy ; wait yy ;
                 xy <- times{m'}{n} <- x y1 ; % (2*x+1)*y = 2*x*y + y
                 z' <- dbl0{m'*n} <- xy ;
                 z <- plus{2*m'*n}{n} <- z' y2
         | e => wait x ;               % 0*y = 0
                u <- drop{n} <- y; wait u;
                z <- zero <- )

%%% Unary natural numbers
%%% Indexed by their value
type nat{n} = +{ zero : ?{n = 0}. 1,
                 succ : ?{n > 0}. nat{n-1} }

decl zero_nat : . |- (x : nat{0})
proc x <- zero_nat <- = x.zero ; close x

decl succ_nat{n} : (y : nat{n}) |- (x : nat{n+1})
proc x <- succ_nat{n} <- y = x.succ ; x <- y

decl pred_nat{n|n > 0} : (y : nat{n}) |- (x : nat{n-1})
proc x <- pred_nat{n} <- y = case y ( succ => x <- y )

decl plus_nat{m}{n} : (y : nat{m}) (z : nat{n}) |- (x : nat{n+m})
proc x <- plus_nat{m}{n} <- y z =
  case y ( zero => wait y ; x <- z
         | succ => x.succ ;
                   x <- plus_nat{m-1}{n} <- y z )

decl drop_nat{n} : (x : nat{n}) |- (u : 1)
decl dup_nat{n} : (x : nat{n}) |- (xx : nat{n} * nat{n} * 1)

proc u <- drop_nat{n} <- x =
  case x ( zero => wait x ; close u 
         | succ => u <- drop_nat{n-1} <- x )

proc xx <- dup_nat{n} <- x =
  case x ( zero => wait x ;
                   x1 <- zero_nat <- ; send xx x1 ;
                   x2 <- zero_nat <- ; send xx x2 ;
                   close xx
         | succ => yy <- dup_nat{n-1} <- x ;
                   x <- recv yy ; y <- recv yy ; wait yy ;
                   x1 <- succ_nat{n-1} <- x ; send xx x1 ;
                   x2 <- succ_nat{n-1} <- y ; send xx x2 ;
                   close xx )

%%% Comparison, this time requires ord{m+1}{n+1} = ord{m}{n}
decl compare_nat{m}{n} : (x : nat{m}) (y : nat{n}) |- (o : ord{m}{n})
proc o <- compare_nat{m}{n} <- x y =
  case x ( zero => case y ( zero => o.eq ; wait x ; wait y ;
                                    close o
                          | succ => o.lt ; wait x ;
                                    u <- drop_nat{n-1} <- y ; wait u ;
                                    close o )
         | succ => case y ( zero => o.gt ; wait y ;
                                    u <- drop_nat{m-1} <- x ; wait u ;
                                    close o
                          | succ => o <- compare_nat{m-1}{n-1} <- x y ) )

decl double_nat{n} : (y : nat{n}) |- (x : nat{2*n})
proc x <- double_nat{n} <- y =
  case y ( zero => wait y ; x <- zero_nat <-
         | succ => z <- double_nat{n-1} <- y ;
                   z' <- succ_nat{2*n-2} <- z ;
                   x <- succ_nat{2*n-1} <- z' )

%%% Conversions between unary and binary representations

decl nat2bin{n} : (x : nat{n}) |- (b : bin{n})
proc b <- nat2bin{n} <- x =
  case x ( zero => wait x ;
                   b <- zero <-
         | succ => b' <- nat2bin{n-1} <- x ;
                   b <- succ{n-1} <- b' )

decl bin2nat{n} : (b : bin{n}) |- (x : nat{n})
proc x <- bin2nat{n} <- b =
  case b ( b0 => {n'} <- recv b ;
                 z <- bin2nat{n'} <- b ;
                 x <- double_nat{n'} <- z
         | b1 => {n'} <- recv b ;
                 z <- bin2nat{n'} <- b ;
                 z' <- double_nat{n'} <- z ;
                 x <- succ_nat{2*n'} <- z'
         | e => wait b ;
                x <- zero_nat <- )
