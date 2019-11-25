type A = 1

type stack{n} = &{ins : A -o stack{n+1},
                  del : +{none : ?{n = 0}. 1,
                          some : ?{n > 0}. A * stack{n-1}}}

decl empty : . |- (s : stack{0})
decl elem{n} : (x : A) (t : stack{n}) |- (s : stack{n+1})

proc s <- empty <- =
  case s (
    ins => x <- recv s ;
           e <- empty <- ;
           s <- elem{0} <- x e
  | del => s.none ;
           close s
  )

proc s <- elem{n} <- x t =
  case s (
    ins => y <- recv s ;
           tn <- elem{n} <- x t ;
           s <- elem{n+1} <- y tn
  | del => s.some ;
           send s x ;
           s <- t
  )

type word{n} = +{char : ?{n > 0}. A * word{n-1}, end : ?{n = 0}. 1}

decl rev{n} : (w : word{n}) |- (r : word{n})
decl push{m}{n} : (w : word{n}) (s : stack{m}) |- (r : word{n+m})
decl pop{m} : (s : stack{m}) |- (r : word{m})

proc r <- push{m}{n} <- w s =
  case w (
    char => a <- recv w ;
            s.ins ;
            send s a ;
            r <- push{m+1}{n-1} <- w s
   | end => wait w ;
            r <- pop{m} <- s
  )

proc r <- pop{m} <- s =
  s.del ;
  case s (
    none => wait s ;
            r.end ;
            close r
  | some => a <- recv s ;
            r.char ;
            send r a ;
            r <- pop{m-1} <- s
  )

proc r <- rev{n} <- w =
  s <- empty <- ;
  r <- push{0}{n} <- w s

type editor{n} = +{next : char * editor,
                   undo : char * editor}

