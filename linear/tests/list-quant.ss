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

