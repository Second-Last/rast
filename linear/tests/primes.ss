#test success
#options --work=none --time=none --syntax=implicit

type nat = +{succ : nat, zero : 1}

decl zero : . |- (x : nat)
decl succ : (y : nat) |- (x : nat)

proc x <- zero <- = x.zero ; close x
proc x <- succ <- y = x.succ ; x <- y

%--------------------
decl deallocate : (x : nat) |- (u : 1)
decl duplicate : (x : nat) |- (xx : nat * nat * 1)

proc u <- deallocate <- x =
  case x ( succ => u <- deallocate <- x
         | zero => wait x ; close u )

proc xx <- duplicate <- x =
  case x ( succ => yy <- duplicate <- x ;
                   y1 <- recv yy ; y2 <- recv yy ; wait yy ;
                   x1 <- succ <- y1 ; send xx x1 ;
                   x2 <- succ <- y2 ; send xx x2 ;
                   close xx
         | zero => wait x ;
                   x1 <- zero <- ; send xx x1 ;
                   x2 <- zero <- ; send xx x2 ;
                   close xx )

%--------------------
type stream = +{prime : stream, composite : stream, end : 1}

decl filter : (t : stream) (c : nat) (d : nat) |- (s : stream)
proc s <- filter <- t c d =
  case t ( prime => case c ( succ => s.prime ; % not divisible by us
                             d' <- succ <- d ;
                             s <- filter <- t c d'
                           | zero => wait c ; % divisible by us: not prime
                             s.composite ;
                             z <- zero <- ;
                             s <- filter <- t d z ) % cyclic loop
         | composite => s.composite ;  % alrady composite
                        case c ( succ => d' <- succ <- d ;
                                         s <- filter <- t c d'
                               | zero => wait c ;
                                 z <- zero <- ;
                                 s <- filter <- t d z )
         | end => wait t ;
                  u <- deallocate <- c ; wait u ;
                  u <- deallocate <- d ; wait u ;
                  s.end ; close s )

decl head : (t : stream) (x : nat) |- (s : stream)
proc s <- head <- t x =
  case t ( prime => s.prime ; % not divisible: new prime
                    z <- zero <- ;
                    xx <- duplicate <- x ;
                    x1 <- recv xx ; x2 <- recv xx ; wait xx ;
                    f <- filter <- t x1 z ;
                    x' <- succ <- x2 ;
                    s <- head <- f x'
         | composite => s.composite ;
                        x' <- succ <- x ;
                        s <- head <- t x'
         | end => wait t ;
                  u <- deallocate <- x ; wait u ;
                  s.end ; close s )

decl candidates : (x : nat) |- (s : stream)
proc s <- candidates <- x =
  case x ( succ => s.prime ;
                   s <- candidates <- x
         | zero => wait x ;
                   s.end ; close s )

decl primes : (x : nat) |- (s : stream)
proc s <- primes <- x =
  t <- candidates <- x ;
  c0 <- zero <- ;
  c1 <- succ <- c0 ; % first position is 2, not 1
  s <- head <- t c1
