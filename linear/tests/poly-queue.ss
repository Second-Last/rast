#test success
#options --work=send --syntax=explicit

type A = 1
type queue{n} = &{ins : <{2*n}| A -o queue{n+1},
                  del : <{2}| +{none : ?{n = 0}. 1,
                                some : ?{n > 0}. A * queue{n-1}}}

decl empty : . |- (s : queue{0})
decl elem{n} : (x : A) (t : queue{n}) |- (s : queue{n+1})

proc s <- elem{n} <- x t =
  case s (
    ins => get s {2*(n+1)} ;
           t.ins ;
           pay t {2*n} ;
           y <- recv s ;
           send t y ;
           s <- elem{n+1} <- x t
  | del => get s {2} ;
           s.some ;
           assert s {n+1 > 0} ;
           send s x ;
           s <- t
  )

proc s <- empty <- =
  case s (
    ins => get s {0} ;
           x <- recv s ;
           e <- empty <- ;
           s <- elem{0} <- x e
  | del => get s {2} ;
           s.none ;
           assert s {0 = 0} ;
           close s
  )