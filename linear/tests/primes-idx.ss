#test success
#options --work=none --time=none --syntax=implicit

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

%--------------------
type stream{k} = +{prime : ?{k > 0}. stream{k-1},
                   composite : ?{k > 0}. stream{k-1},
                   end : ?{k = 0}. 1}

decl filter{k}{n1}{n2}{n|n = n1+n2}
    : (t : stream{k}) (c : nat{n1}) (d : nat{n2}) |- (s : stream{k})
proc s <- filter{k}{n1}{n2}{n} <- t c d =
  case t ( prime => case c ( succ => s.prime ; % not divisible by us
                             d' <- succ{n2} <- d ;
                             s <- filter{k-1}{n1-1}{n2+1}{n} <- t c d'
                           | zero => wait c ; % divisible by us: not prime
                             s.composite ;
                             z <- zero <- ;
                             s <- filter{k-1}{n2}{0}{n} <- t d z ) % cyclic loop
         | composite => s.composite ;  % alrady composite
                        case c ( succ => d' <- succ{n2} <- d ;
                                         s <- filter{k-1}{n1-1}{n2+1}{n} <- t c d'
                               | zero => wait c ;
                                 z <- zero <- ;
                                 s <- filter{k-1}{n2}{0}{n} <- t d z )
         | end => wait t ;
                  u <- deallocate{n1} <- c ; wait u ;
                  u <- deallocate{n2} <- d ; wait u ;
                  s.end ; close s )

decl head{k}{n}{kn|kn = k+n} : (t : stream{k}) (x : nat{n}) |- (s : stream{k})
proc s <- head{k}{n}{kn} <- t x =
  case t ( prime => s.prime ; % not divisible: new prime
                    z <- zero <- ;
                    xx <- duplicate{n} <- x ;
                    x1 <- recv xx ; x2 <- recv xx ; wait xx ;
                    f <- filter{k-1}{n}{0}{n} <- t x1 z ;
                    x' <- succ{n} <- x2 ;
                    s <- head{k-1}{n+1}{kn} <- f x'
         | composite => s.composite ;
                        x' <- succ{n} <- x ;
                        s <- head{k-1}{n+1}{kn} <- t x'
         | end => wait t ;
                  u <- deallocate{n} <- x ; wait u ;
                  s.end ; close s )

decl candidates{n} : (x : nat{n}) |- (s : stream{n})
proc s <- candidates{n} <- x =
  case x ( succ => s.prime ;
                   s <- candidates{n-1} <- x
         | zero => wait x ;
                   s.end ; close s )

decl primes{n} : (x : nat{n}) |- (s : stream{n})
proc s <- primes{n} <- x =
  t <- candidates{n} <- x ;
  c0 <- zero <- ;
  c1 <- succ{0} <- c0 ; % first position is 2, not 1
  s <- head{n}{1}{n+1} <- t c1
