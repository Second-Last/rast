#test success
#options --work=none --time=none --syntax=implicit

% copied from primes-idx.ss

type nat{n} = +{succ : ?{n > 0}. nat{n-1},
                zero : ?{n = 0}. 1}

decl zero : . |- (x : nat{0})
decl succ{n} : (y : nat{n}) |- (x : nat{n+1})

proc x <- zero <- = x.zero ; close x
proc x <- succ{n} <- y = x.succ ; x <- y

%--------------------
decl deallocate{n} : (x : nat{n}) |- (u : 1)
decl duplicate{n} : (x : nat{n}) |- (xx : nat{n} * nat{n} * 1)

proc u <- deallocate{n} <- x =
  case x ( succ => u <- deallocate{n-1} <- x
         | zero => wait x ; close u )

proc xx <- duplicate{n} <- x =
  case x ( succ => yy <- duplicate{n-1} <- x ;
                   y1 <- recv yy ; y2 <- recv yy ; wait yy ;
                   x1 <- succ{n-1} <- y1 ; send xx x1 ;
                   x2 <- succ{n-1} <- y2 ; send xx x2 ;
                   close xx
         | zero => wait x ;
                   x1 <- zero <- ; send xx x1 ;
                   x2 <- zero <- ; send xx x2 ;
                   close xx )

type ord{x}{y} = +{ lt : ?{x < y}. 1,
                    eq : ?{x = y}. 1,
                    gt : ?{x > y}. 1 }

decl compare{x}{y} : (n : nat{x}) (k : nat{y}) |- (o : ord{x}{y})
proc o <- compare{x}{y} <- n k =
  case n ( succ => case k ( succ => o <- compare{x-1}{y-1} <- n k
                          | zero => o.gt ; wait k ;
                                    u <- deallocate{x-1} <- n ; wait u ;
                                    close o )
         | zero => case k ( succ => o.lt ; wait n ;
                                    u <- deallocate{y-1} <- k ; wait u ;
                                    close o
                          | zero => o.eq ; wait n ; wait k ;
                                    close o ) )

%--------------------
type int{x}{y} = &{ inc : int{x+1}{y},
                    dec : int{x}{y+1},
                    sgn : +{ neg : ?{x < y}. int{x}{y},
                             zer : ?{x = y}. int{x}{y},
                             pos : ?{x > y}. int{x}{y} } }

decl izero : . |- (a : int{0}{0})
proc a <- izero <- =
  z1 <- zero <-;
  z2 <- zero <-;
  a <- counter{0}{0} <- z1 z2

decl counter{x}{y} : (p : nat{x}) (n : nat{y}) |- (a : int{x}{y})
proc a <- counter{x}{y} <- p n =
  case a ( inc => p' <- succ{x} <- p ;
                  a <- counter{x+1}{y} <- p' n
         | dec => n' <- succ{y} <- n ;      
                  a <- counter{x}{y+1} <- p n'
         | sgn => pp <- duplicate{x} <- p ;
                  p1 <- recv pp ; p2 <- recv pp ; wait pp ;
                  nn <- duplicate{y} <- n ;
                  n1 <- recv nn ; n2 <- recv nn ; wait nn ;
                  c <- compare{x}{y} <- p1 n1 ;
                  case c ( lt => wait c ; a.neg ; a <- counter{x}{y} <- p2 n2
                         | eq => wait c ; a.zer ; a <- counter{x}{y} <- p2 n2
                         | gt => wait c ; a.pos ; a <- counter{x}{y} <- p2 n2 ) )
