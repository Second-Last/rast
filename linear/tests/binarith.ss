#test approx success
#options --syntax=implicit

%%% Binary arithmetic
%%% indexed by value
%%% no leading zeros allowed
%%% one example (multiplication) has nonlinear constraints

type bin{n} = +{ b0 : ?{n > 0}. ?k. ?{n = 2*k}. bin{k},
                 b1 : ?{n > 0}. ?k. ?{n = 2*k+1}. bin{k},  % n > 0 is redundant here
                 e : ?{n = 0}. 1 }

decl zero : . |- (x : bin{0})
decl succ{n} : (y : bin{n}) |- (x : bin{n+1})

proc x <- zero <- = x.e ; close x
proc x <- succ{n} <- y =
  case y ( b0 => {n'} <- recv y ;
                 x.b1 ; send x {n'} ;
                 x <- y
         | b1 => {n'} <- recv y ;
                 x.b0 ; send x {n'+1} ;
                 x <- succ{n'} <- y
         | e => x.b1 ; send x {0} ;
                x.e ; wait y ; close x )

decl plus{m}{n} : (y : bin{m}) (z : bin{n}) |- (x : bin{m+n})
proc x <- plus{m}{n} <- y z =
  case y ( b0 => {m'} <- recv y ;
                 case z ( b0 => {n'} <- recv z ;
                                x.b0 ; send x {m'+n'} ;
                                x <- plus{m'}{n'} <- y z
                        | b1 => {n'} <- recv z ;
                                x.b1 ; send x {m'+n'} ;
                                x <- plus{m'}{n'} <- y z
                        | e => wait z ;
                               x.b0 ; send x {m'} ;
                               x <- y )
         | b1 => {m'} <- recv y ;
                 case z ( b0 => {n'} <- recv z ;
                          x.b1 ; send x {m'+n'} ;
                          x <- plus{m'}{n'} <- y z
                        | b1 => {n'} <- recv z ;
                          x.b0 ; send x {m'+n'+1} ;
                          w <- plus{m'}{n'} <- y z ;
                          x <- succ{m'+n'} <- w
                        | e => wait z ;
                               x.b1 ; send x {m'} ;
                               x <- y )
         | e => wait y ; x <- z )

decl drop{n} : (y : bin{n}) |- (u : 1)
proc u <- drop{n} <- y =
  case y ( b0 => {n'} <- recv y ; u <- drop{n'} <- y
         | b1 => {n'} <- recv y ; u <- drop{n'} <- y
         | e => wait y ; close u )

% next two processes ensure no leading zeros are produced
decl dbl0{n} : (y : bin{n}) |- (x : bin{2*n})
decl dbl1{n} : (y : bin{n}) |- (x : bin{2*n+1})

(* make sure no leading 0s are produced *)
proc x <- dbl0{n} <- y =
  case y ( b0 => {n'} <- recv y ;
                 x.b0 ; send x {n} ;
                 x.b0 ; send x {n'} ;
                 x <- y
         | b1 => {n'} <- recv y ;
                 x.b0 ; send x {n} ;
                 x.b1 ; send x {n'} ;
                 x <- y
         | e => x.e ; wait y ; close x )

proc x <- dbl1{n} <- y =
  x.b1 ; send x {n} ;
  x <- y

decl dup{n} : (y : bin{n}) |- (yy : bin{n} * bin{n} * 1)
proc yy <- dup{n} <- y =
  case y ( b0 => {n'} <- recv y ;
                 yy' <- dup{n'} <- y ;
                 y1' <- recv yy' ;
                 y2' <- recv yy' ; wait yy' ;
                 y1 <- dbl0{n'} <- y1' ; send yy y1 ; 
                 y2 <- dbl0{n'} <- y2' ; send yy y2 ;
                 close yy
         | b1 => {n'} <- recv y ;
                 yy' <- dup{n'} <- y ;
                 y1' <- recv yy' ;
                 y2' <- recv yy' ; wait yy' ;
                 y1 <- dbl1{n'} <- y1' ; send yy y1 ;
                 y2 <- dbl1{n'} <- y2' ; send yy y2 ;
                 close yy
         | e => wait y ;
                y1 <- zero <- ; send yy y1 ;
                y2 <- zero <- ; send yy y2 ;
                close yy )

decl pred{n|n > 0} : (y : bin{n}) |- (x : bin{n-1})
proc x <- pred{n} <- y =
  case y ( b0 => {n'} <- recv y ;    % 2*k-1 = 2*(k-1)+1
                 x.b1 ; send x {n'-1} ;
                 x <- pred{n'} <- y
         | b1 => {n'} <- recv y ;
                 x <- dbl0{n'} <- y  % 2*k+1-1 = 2*k
         )

type ord{m}{n} = +{ lt : ?{m < n}. 1,
                    eq : ?{m = n}. 1,
                    gt : ?{m > n}. 1 }

decl compare{m}{n} : (x : bin{m}) (y : bin{n}) |- (o : ord{m}{n})
proc o <- compare{m}{n} <- x y =
  case x ( b0 => {m'} <- recv x ;
                 case y ( b0 => {n'} <- recv y ;
                                o' <- compare{m'}{n'} <- x y ;
                                case o' ( lt => wait o' ;
                                                o.lt ; close o
                                        | eq => wait o' ;
                                                o.eq ; close o
                                        | gt => wait o' ;
                                                o.gt ; close o )
                        | b1 => {n'} <- recv y ;
                                o' <- compare{m'}{n'} <- x y ;
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

% next example goes beyond Presburger constraints
decl times{m}{n} : (y : bin{m}) (z : bin{n}) |- (x : bin{m*n})
proc x <- times{m}{n} <- y z =
  case y ( b0 => {m'} <- recv y ;
                 % x.b0 ; send x {m'*n} ;  % bug discovered with refinement types
                 x' <- times{m'}{n} <- y z ;  % (2*y)*z = 2*(y*z)
                 x <- dbl0{m'*n} <- x'
         | b1 => {m'} <- recv y ;
                 zz <- dup{n} <- z ;
                 z1 <- recv zz ; z2 <- recv zz ; wait zz ;
                 x' <- times{m'}{n} <- y z1 ; % (2*y+1)*z = 2*y*z + z
                 w <- dbl0{m'*n} <- x' ;
                 x <- plus{2*m'*n}{n} <- w z2
         | e => wait y ;               % 0*z = 0
                u <- drop{n} <- z; wait u;
                x <- zero <- )

