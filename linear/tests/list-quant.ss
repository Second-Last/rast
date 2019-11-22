#test success
#options --syntax=implicit

type A = 1
type list{n} = +{cons : ?{n > 0}. A * list{n-1}, nil : ?{n = 0}. 1}

decl fwd{n} : (x : list{n}) |- (y : list{n})

proc y <- fwd{n} <- x = y <- x

decl copy{n} : (x : list{n}) |- (y : list{n})

proc y <- copy{n} <- x =
  case x (
    cons => a <- recv x ;
            y.cons ;
            send y a ;
            y <- copy{n-1} <- x
  | nil => wait x ;
           y.nil ;
           close y
  )

decl alternate{m}{n} : (l1 : list{m}) (l2 : list{n}) |- (l : list{m+n})

proc l <- alternate{m}{n} <- l1 l2 =
  case l1 (
    cons => x <- recv l1 ;
            l.cons ;
            send l x ;
            l <- alternate{n}{m-1} <- l2 l1
  | nil => wait l1 ;
           l <- l2
  )

decl append{m}{n} : (l1 : list{m}) (l2 : list{n}) |- (l : list{m+n})

proc l <- append{m}{n} <- l1 l2 =
  case l1 (
    cons => x <- recv l1 ;
            l.cons ;
            send l x ;
            l <- append{m-1}{n} <- l1 l2
  | nil => wait l1 ;
           l <- l2
  )

decl nil : . |- (l : list{0})

proc l <- nil <- =
  l.nil ;
  close l

decl cons{n} : (x : A) (t : list{n}) |- (l : list{n+1})
proc l <- cons{n} <- x t =
  l.cons ;
  send l x ;
  l <- t

decl cons2{n} : (x : A) (y : A) (t : list{n}) |- (l : list{n+2})

proc l <- cons2{n} <- x y t =
  l.cons ;
  send l x ;
  l.cons ;
  send l y ;
  l <- t

type mapperAB = &{next : A -o B * mapperAB,
                  done : 1}

type B = 1

type listA{n} = +{cons : ?{n > 0}. A * listA{n-1}, nil : ?{n = 0}. 1}
type listB{n} = +{cons : ?{n > 0}. B * listB{n-1}, nil : ?{n = 0}. 1}

decl map{n} : (l : listA{n}) (m : mapperAB) |- (k : listB{n})

proc k <- map{n} <- l m =
  case l (
    cons => x <- recv l ;
            m.next ;
            send m x ;
            y <- recv m ;
            k.cons ;
            send k y ;
            k <- map{n-1} <- l m
   | nil => wait l ;
            m.done ;
            wait m ;
            k.nil ;
            close k
  )

type folderAB = &{next : A -o B -o B * folderAB,
                  done : 1}

decl fold{n} : (b : B) (l : listA{n}) (f : folderAB) |- (r : B)

proc r <- fold{n} <- b l f =
  case l (
    cons => x <- recv l ;
            f.next ;
            send f x ;
            send f b ;
            b <- recv f ;
            r <- fold{n-1} <- b l f
   | nil => f.done ;
            wait l ;
            wait f ;
            r <- b
  )

decl rev{n} : (l : list{n}) |- (k : list{n})

proc k <- rev{n} <- l =
  e <- nil <- ;
  k <- revhelper{0}{n} <- l e

decl revhelper{m}{n} : (l : list{n}) (r : list{m}) |- (k : list{m+n})

proc k <- revhelper{m}{n} <- l r =
  case l (
    cons => x <- recv l ;
            rr <- cons{m} <- x r ;
            k <- revhelper{m+1}{n-1} <- l rr
   | nil => wait l ;
            k <- r
  )

type listlist{m}{n} = +{cons : ?{n > 0}. list{m} * listlist{m}{n-1}, nil : ?{n = 0}. 1}

decl flatten{m}{n} : (l : listlist{m}{n}) |- (k : list{m*n})

proc k <- flatten{m}{n} <- l =
  case l (
    cons => x <- recv l ;
            kt <- flatten{m}{n-1} <- l ;
            k <- append{m*(n-1)}{m} <- kt x
   | nil => wait l ;
            k <- nil <- 
  )

decl split{n} : (l : list{2*n}) |- (k : list{n} * list{n})
decl splithelper{m}{n}{p} : (l : list{2*m}) (l1 : list{n}) (l2 : list{p}) |- (k : list{m+n} * list{m+p})

proc k <- splithelper{m}{n}{p} <- l l1 l2 =
  case l (
    cons => x <- recv l ;
            case l (
              cons => y <- recv l ;
                      l1n <- cons{n} <- x l1 ;
                      l2n <- cons{p} <- y l2 ;
                      k <- splithelper{m-1}{n+1}{p+1} <- l l1n l2n
            )
   | nil => wait l ;
            send k l1 ;
            k <- l2
  )

proc k <- split{n} <- l =
  l1 <- nil <- ;
  l2 <- nil <- ;
  k <- splithelper{n}{0}{0} <- l l1 l2

decl head{n} : (l : list{n+1}) |- (k : A * list{n})

proc k <- head{n} <- l =
  case l (
    cons => x <- recv l ;
            send k x ;
            k <- l
  )

type checker = &{next : A -o +{true : A * checker,
                               false : A * checker},
                 done : 1}

decl insert{n} : (x : A) (l : list{n}) (ch : checker) |- (k : list{n+1})

proc k <- insert{n} <- x l ch =
  case l (
    cons => y <- recv l ;
            ch.next ;
            send ch y ;
            case ch (
              true => y <- recv ch ;
                      ch.done ;
                      wait ch ;
                      l1 <- cons{n-1} <- y l ;
                      k <- cons{n} <- x l1
            | false => y <- recv ch ;
                       l1 <- insert{n-1} <- x l ch ;
                       k <- cons{n} <- y l1
            )
  | nil => wait l ;
           e <- nil <- ;
           ch.done ;
           wait ch ;
           k <- cons{0} <- x e
  )

type partitioner{a}{b} = & {next : A -o +{true : ?{a > 0}. A * partitioner{a-1}{b},
                                          false : ?{b > 0}. A * partitioner{a}{b-1}},
                            done : 1}

decl partition{m}{n} : (l : list{m+n}) (ch : partitioner{m}{n}) |- (k : list{m} * list{n})
decl partitionhelper{a}{b}{n}{p} : (l : list{a+b}) (l1 : list{n}) (l2 : list{p}) (ch : partitioner{a}{b}) |- (k : list{a+n} * list{b+p})

proc k <- partitionhelper{a}{b}{n}{p} <- l l1 l2 ch =
  case l (
    cons => x <- recv l ;
            ch.next ;
            send ch x ;
            case ch (
              true => x <- recv ch ;
                      l1n <- cons{n} <- x l1 ;
                      k <- partitionhelper{a-1}{b}{n+1}{p} <- l l1n l2 ch
            | false => x <- recv ch ;
                       l2n <- cons{p} <- x l2 ;
                       k <- partitionhelper{a}{b-1}{n}{p+1} <- l l1 l2n ch
            )
  | nil => wait l ;
           ch.done ;
           wait ch ;
           send k l1 ;
           k <- l2
  )

proc k <- partition{m}{n} <- l ch =
  l1 <- nil <- ;
  l2 <- nil <- ;
  k <- partitionhelper{m}{n}{0}{0} <- l l1 l2 ch

type bool = +{true : 1, false : 1}

type satisfier = &{next : A -o bool * satisfier,
                   done : 1}

decl forall{n} : (l : list{n}) (s : satisfier) |- (b : bool)
decl exists{n} : (l : list{n}) (s : satisfier) |- (b : bool)
decl tt : . |- (b : bool)
decl ff : . |- (b : bool)
decl and : (a : bool) (b : bool) |- (c : bool)
decl or : (a : bool) (b : bool) |- (c : bool)

proc b <- forall{n} <- l s =
  case l (
    cons => x <- recv l ;
            s.next ;
            send s x ;
            bx <- recv s ;
            bt <- forall{n-1} <- l s ;
            b <- and <- bt bx
  | nil => wait l ;
           s.done ;
           wait s ;
           b <- tt <- 
  )

proc b <- exists{n} <- l s =
  case l (
    cons => x <- recv l ;
            s.next ;
            send s x ;
            bx <- recv s ;
            bt <- exists{n-1} <- l s ;
            b <- or <- bt bx
  | nil => wait l ;
           s.done ;
           wait s ;
           b <- tt <- 
  )

proc b <- tt <- =
  b.true ;
  close b

proc b <- ff <- =
  b.false ;
  close b

proc c <- and <- a b =
  case a (
    true => case b (
              true => c.true ;
                      wait a ;
                      wait b ;
                      close c
            | false => c.false ;
                       wait a ;
                       wait b ;
                       close c
    )
  | false => case b (
              true => c.false ;
                      wait a ;
                      wait b ;
                      close c
            | false => c.false ;
                       wait a ;
                       wait b ;
                       close c
    )
  )

proc c <- or <- a b =
  case a (
    true => case b (
              true => c.true ;
                      wait a ;
                      wait b ;
                      close c
            | false => c.true ;
                       wait a ;
                       wait b ;
                       close c
            )
  | false => case b (
              true => c.true ;
                      wait a ;
                      wait b ;
                      close c
            | false => c.false ;
                       wait a ;
                       wait b ;
                       close c
             )
  )

type eq = &{next : A -o A -o bool * eq,
            done : 1}

decl equal{n} : (l1 : list{n}) (l2 : list{n}) (e : eq) |- (b : bool)

proc b <- equal{n} <- l1 l2 e =
  case l1 (
    cons => x <- recv l1 ;
            case l2 (
              cons => y <- recv l2 ;
                      e.next ;
                      send e x ;
                      send e y ;
                      bxy <- recv e ;
                      bt <- equal{n-1} <- l1 l2 e ;
                      b <- and <- bxy bt
            )
  | nil => wait l1 ;
           case l2 (
             nil => wait l2 ;
                    e.done ;
                    wait e ;
                    b <- tt <- 
           )
  )

type comparer = &{next : A -o A -o A * A * bool * comparer,
                  done : 1}

decl merge{m}{n} : (l1 : list{m}) (l2 : list{n}) (c : comparer) |- (l : list{m+n})

proc l <- merge{m}{n} <- l1 l2 c =
  case l1 (
    cons => x <- recv l1 ;
            case l2 (
              cons => y <- recv l2 ;
                      c.next ;
                      send c x ;
                      send c y ;
                      x <- recv c ;
                      y <- recv c ;
                      b <- recv c ;
                      ln <- merge{m-1}{n-1} <- l1 l2 c ;
                      case b (
                        true => ly <- cons{m+n-2} <- y ln ;
                                wait b ;
                                l <- cons{m+n-1} <- x ly
                      | false => lx <- cons{m+n-2} <- x ln ;
                                 wait b ;
                                 l <- cons{m+n-1} <- y lx
                      )
            | nil => wait l2 ;
                     c.done ;
                     wait c ;
                     l <- cons{m-1} <- x l1
            )
  | nil => wait l1 ;
           c.done ;
           wait c ;
           l <- l2
  )

decl mergesort{n} : (l : list{2*n}) (c : comparer) |- (k : list{2*n})

proc k <- mergesort{n} <- l c =
  l2 <- split{n} <- l ;
  l1 <- recv l2 ;
  k <- merge{n}{n} <- l1 l2 c