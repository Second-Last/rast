#test success
#options --work=none --time=none --syntax=implicit

%%% Integer counter (with positive and negative numbers)
%%% where a is represented by x-y for two natural numbers
%%% x and y

%%% Unary natural numbers, copied from binarith.ss
%--------------------------------------------------
type nat{n} = +{ zero : ?{n = 0}. 1,
                 succ : ?{n > 0}. nat{n-1} }

decl zero_nat : . |- (x : nat{0})
proc x <- zero_nat <- = x.zero ; close x

decl succ_nat{n} : (y : nat{n}) |- (x : nat{n+1})
proc x <- succ_nat{n} <- y = x.succ ; x <- y

%%% pred not needed here
decl pred_nat{n|n > 0} : (y : nat{n}) |- (x : nat{n-1})
proc x <- pred_nat{n} <- y = case y ( succ => x <- y )

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

%--------------------------------------------------
type ord{x}{y} = +{ lt : ?{x < y}. 1,
                    eq : ?{x = y}. 1,
                    gt : ?{x > y}. 1 }

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
%--------------------------------------------------


type intctr{x}{y} = &{ inc : intctr{x+1}{y},
                       dec : intctr{x}{y+1},
                       sgn : +{ neg : ?{x < y}. intctr{x}{y},
                                zer : ?{x = y}. intctr{x}{y},
                                pos : ?{x > y}. intctr{x}{y} } }

decl izero : . |- (a : intctr{0}{0})
proc a <- izero <- =
  z1 <- zero_nat <-;
  z2 <- zero_nat <-;
  a <- counter{0}{0} <- z1 z2

decl counter{x}{y} : (p : nat{x}) (n : nat{y}) |- (a : intctr{x}{y})
proc a <- counter{x}{y} <- p n =
  case a ( inc => p' <- succ_nat{x} <- p ;
                  a <- counter{x+1}{y} <- p' n
         | dec => n' <- succ_nat{y} <- n ;      
                  a <- counter{x}{y+1} <- p n'
         | sgn => pp <- dup_nat{x} <- p ;
                  p1 <- recv pp ; p2 <- recv pp ; wait pp ;
                  nn <- dup_nat{y} <- n ;
                  n1 <- recv nn ; n2 <- recv nn ; wait nn ;
                  c <- compare_nat{x}{y} <- p1 n1 ;
                  case c ( lt => wait c ; a.neg ; a <- counter{x}{y} <- p2 n2
                         | eq => wait c ; a.zer ; a <- counter{x}{y} <- p2 n2
                         | gt => wait c ; a.pos ; a <- counter{x}{y} <- p2 n2 ) )
