#test success
#options --work=send --syntax=explicit

type queue{n} = &{ins : <{n}| queue{n+1},
                  del : <{2}| +{none : ?{n = 0}. 1,
                                some : ?{n > 0}. queue{n-1}}}

decl empty : . |- (s : queue{0})
decl elem{n} : (t : queue{n}) |- (s : queue{n+1})

proc s <- elem{n} t =
  case s (
    ins => get s {(n+1)} ;
           t.ins ;
           pay t {n} ;
           s <- elem{n+1} t
  | del => get s {2} ;
           s.some ;
           assert s {n+1 > 0} ;
           work ;
           s <-> t
  )

proc s <- empty =
  case s (
    ins => get s {0} ;
           e <- empty ;
           s <- elem{0} e
  | del => get s {2} ;
           s.none ;
           assert s {0 = 0} ;
           close s
  )