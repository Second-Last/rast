#test success

type nat = +{zero : 1, succ : nat}

decl zero : . |- (x : nat)
proc x <- zero <- = x.zero ; close x

exec zero

decl succ : (y : nat) |- (x : nat)
proc x <- succ <- y =
  x.succ ; x <- y


decl three : . |- (x : nat)
proc x <- three <- =
  x0 <- zero <- ;
  x1 <- succ <- x0 ;
  x2 <- succ <- x1 ;
  x3 <- succ <- x2 ;
  x <- x3

exec three

type bin = +{ b0 : bin, b1 : bin, e : 1 }
decl bzero : . |- (x : bin)
decl bsucc : (x : bin) |- (y : bin)
decl dbl0 : (x : bin) |- (y : bin)
decl dbl1 : (x : bin) |- (y : bin)

proc x <- bzero <- = x.e ; close x
proc y <- bsucc <- x =
  case x ( b0 => y.b1 ; y <- x
         | b1 => y.b0 ; y <- bsucc <- x
         | e => y.b1 ; y.e ; wait x ; close y )
proc y <- dbl0 <- x = y.b0 ; y <- x
proc y <- dbl1 <- x = y.b1 ; y <- x

decl nat2bin : (x : nat) |- (b : bin)
proc b <- nat2bin <- x =
  case x ( zero => wait x ;
                   b <- bzero <-
         | succ => b' <- nat2bin <- x ;
                   b <- bsucc <- b' )

decl n13 : . |- (x : nat)
proc x <- n13 <- =
  x.succ ; x.succ ; x.succ ;
  x.succ ; x.succ ; x.succ ;
  x.succ ; x.succ ; x.succ ;
  x.succ ; x.succ ; x.succ ;
  x.succ ; x.zero ; close x

exec n13

decl b13 : . |- (b : bin)
proc b <- b13 <- =
  x <- n13 <- ;
  b <- nat2bin <- x

exec b13

type ctr = &{ inc : ctr, val : bin }

decl empty : . |- (c : ctr)
decl bit0 : (d : ctr) |- (c : ctr)
decl bit1 : (d : ctr) |- (c : ctr)

proc c <- empty <- =
  case c ( inc => d <- empty <- ;
                  c <- bit1 <- d
         | val => c <- bzero <- )

proc c <- bit0 <- d =
  case c ( inc => c <- bit1 <- d
         | val => c.b0 ; d.val ; c <- d )

proc c <- bit1 <- d =
  case c ( inc => d.inc ;
                  c <- bit0 <- d
         | val => c.b1 ; d.val ; c <- d )

decl b5 : . |- (b : bin)
proc b <- b5 <- =
  c <- empty <- ;
  c.inc ; c.inc ; c.inc ; c.inc ; c.inc ;
  c.val ; b <- c

exec b5

decl dup : (x : bin) |- (xx : bin * bin * 1)
proc xx <- dup <- x =
  case x ( b0 => xx' <- dup <- x ;
                 x1' <- recv xx' ;
                 x2' <- recv xx' ;
                 wait xx' ;
                 x1 <- dbl0 <- x1' ; send xx x1 ;
                 x2 <- dbl0 <- x2' ; send xx x2 ;
                 close xx
        | b1 => xx' <- dup <- x ;
                 x1' <- recv xx' ;
                 x2' <- recv xx' ;
                 wait xx' ;
                 x1 <- dbl1 <- x1' ; send xx x1 ;
                 x2 <- dbl1 <- x2' ; send xx x2 ;
                 close xx
        | e => wait x ;
               x1 <- bzero <- ; send xx x1 ;
               x2 <- bzero <- ; send xx x2 ;
               close xx )

decl bb13 : . |- (xx : bin * bin * 1)
proc xx <- bb13 <- =
  x <- b13 <- ;
  xx <- dup <- x

exec bb13

type list = +{ nil : 1, cons : nat * list }
decl nil : . |- (l : list)
proc l <- nil <- = l.nil ; close l

type seg = list -o list

decl empty_seg : . |- (s : seg)
decl concat : (s1 : seg) (s2 : seg) |- (s : seg)
decl one : (x : nat) |- (s : seg)
decl seg2list : (s : seg) |- (l : list)

proc s <- empty_seg <- =
  t <- recv s ;
  s <- t

proc s <- concat <- s1 s2 =
  t <- recv s ;
  send s2 t ;
  send s1 s2 ;
  s <- s1

proc s <- one <- x =
  t <- recv s ; 
  s.cons ; send s x ;
  s <- t

proc l <- seg2list <- s =
  n <- nil <- ;
  send s n ;
  l <- s

decl l201 : . |- (l : list)
proc l <- l201 <- =
  z <- zero <- ;
  s0 <- one <- z ;
  z <- zero <- ;
  sz <- succ <- z ;
  s1 <- one <- sz ;
  s01 <- concat <- s0 s1 ;
  z <- zero <- ;
  sz <- succ <- z ;
  ssz <- succ <- sz ;
  s2 <- one <- ssz ;
  s201 <- concat <- s2 s01 ;
  l <- seg2list <- s201

exec l201
