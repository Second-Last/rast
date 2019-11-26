#test success
#options --syntax=implicit

type A = 1
type queue{n} = &{ins : A -o queue{n+1},
                  del : +{none : ?{n = 0}. 1,
                          some : ?{n > 0}. A * queue{n-1}}}

decl empty : . |- (q : queue{0})
decl elem{n} : (x : A) (t : queue{n}) |- (q : queue{n+1})

proc q <- empty <- =
  case q (
    ins => x <- recv q ;
           e <- empty <- ;
           q <- elem{0} <- x e
  | del => q.none ;
           close q
  )

proc q <- elem{n} <- x t =
  case q (
    ins => y <- recv q ;
           q1 <- elem{n} <- x t ;
           q <- elem{n+1} <- y q1
  | del => q.some ;
           send q x ;
           q <- t
  )

type tree{w}{h} = +{leaf : ?{h = 0}. 1,
                    node : ?{h > 0}. A * children{w}{h-1}}

type children{w}{h} = +{nil : ?{w = 0}. 1,
                        cons : ?{w > 0}. tree{w-1}{h}}

type list{n} = +{nil : ?{n = 0}. 1, cons : ?{n > 0}. A * list{n-1}}

decl bfs{w}{h} : (t : tree{w}{h}) (q : queue{0}) |- (n : list{w*h})
decl bfs_helper{w}{h}{n} : (t : tree{w}{h}) (q : queue{n}) |- (n : list{w*h})

proc n <- bfs_helper{w}{h}{n} <- t q =
  q.del ;
  case q (
    
  )