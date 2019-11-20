#test success
#options --syntax=explicit

type A = 1
type list{n} = +{cons : ?{n > 0}. A * list{n-1}, nil : ?{n = 0}. 1}

decl fwd{n} : (x : list{n}) |- (y : list{n})

proc y <- fwd{n} <- x = y <- x

decl copy{n} : (x : list{n}) |- (y : list{n})

proc y <- copy{n} <- x =
  case x (
    cons => assume x {n > 0} ;
            a <- recv x ;
            y.cons ;
            assert y {n > 0} ;
            send y a ;
            y <- copy{n-1} <- x
  | nil => assume x {n = 0} ;
           wait x ;
           y.nil ;
           assert y {n = 0} ;
           close y
  )

