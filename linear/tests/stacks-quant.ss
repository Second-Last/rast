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

type char = 1

type editor{n1}{n2} = +{moveL : +{first : ?{n1 = 0}. editor{0}{n2},
                                  notfirst : ?{n1 > 0}. editor{n1-1}{n2+1}},
                        moveR : +{last : ?{n2 = 0}. editor{n1}{0},
                                  notlast : ?{n2 > 0}. editor{n1+1}{n2-1}},
                        input : char -o editor{n1+1}{n2},
                        delete : +{empty : ?{n1 = 0}. editor{0}{n2},
                                   notempty : ?{n1 > 0}. editor{n1-1}{n2}}}

decl start_editor_proc{n | n > 0} : (s1 : stack{0}) (s2 : stack{n}) |- (e : editor{0}{n})
decl editor_proc{n1 | n1 > 0}{n2} : (s1 : stack{n1}) (s2 : stack{n2}) |- (e : editor{n1}{n1+n2})
decl last_editor_proc{n | n > 0} : (s1 : stack{n}) (s2 : stack{0}) |- (e : editor{n}{n})
decl empty_editor_proc : (s1 : stack{0}) (s2 : stack{0}) |- (e : editor{0}{0})
decl edit : . |- (e : editor{0}{0})


