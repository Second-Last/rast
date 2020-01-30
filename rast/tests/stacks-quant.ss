#test success
#options --syntax=implicit

type A = 1

type stack{n} = &{ins : A -o stack{n+1},
                  del : +{none : ?{n = 0}. 1,
                          some : ?{n > 0}. A * stack{n-1}}}

decl empty : . |- (s : stack{0})
decl elem{n} : (x : A) (t : stack{n}) |- (s : stack{n+1})

proc s <- empty =
  case s (
    ins => x <- recv s ;
           e <- empty ;
           s <- elem{0} x e
  | del => s.none ;
           close s
  )

proc s <- elem{n} x t =
  case s (
    ins => y <- recv s ;
           tn <- elem{n} x t ;
           s <- elem{n+1} y tn
  | del => s.some ;
           send s x ;
           s <-> t
  )

type word{n} = +{char : ?{n > 0}. A * word{n-1}, end : ?{n = 0}. 1}

decl rev{n} : (w : word{n}) |- (r : word{n})
decl push{m}{n} : (w : word{n}) (s : stack{m}) |- (r : word{n+m})
decl pop{m} : (s : stack{m}) |- (r : word{m})

proc r <- push{m}{n} w s =
  case w (
    char => a <- recv w ;
            s.ins ;
            send s a ;
            r <- push{m+1}{n-1} w s
   | end => wait w ;
            r <- pop{m} s
  )

proc r <- pop{m} s =
  s.del ;
  case s (
    none => wait s ;
            r.end ;
            close r
  | some => a <- recv s ;
            r.char ;
            send r a ;
            r <- pop{m-1} s
  )

proc r <- rev{n} w =
  s <- empty ;
  r <- push{0}{n} w s

type char = 1

type editor{n1}{n2} = &{moveL : +{first : ?{n1 = 0}. editor{0}{n2},
                                  notfirst : ?{n1 > 0}. editor{n1-1}{n2+1}},
                        moveR : +{last : ?{n2 = 0}. editor{n1}{0},
                                  notlast : ?{n2 > 0}. editor{n1+1}{n2-1}},
                        input : char -o editor{n1+1}{n2},
                        delete : +{empty : ?{n1 = 0}. editor{0}{n2},
                                   notempty : ?{n1 > 0}. char * editor{n1-1}{n2}}}

decl editor_proc{n1}{n2} : (s1 : stack{n1}) (s2 : stack{n2}) |- (e : editor{n1}{n2})
decl edit : . |- (e : editor{0}{0})

proc e <- editor_proc{n1}{n2} s1 s2 =
  case e (
    moveL => s1.del ;
             case s1 (
               none => e.first ;
                       wait s1 ;
                       s1 <- empty ;
                       e <- editor_proc{n1}{n2} s1 s2
              | some => e.notfirst ;
                        c <- recv s1 ;
                        s2.ins ;
                        send s2 c ;
                        e <- editor_proc{n1-1}{n2+1} s1 s2
             )
  | moveR => s2.del ;
             case s2 (
               none => e.last ;
                       wait s2 ;
                       s2 <- empty ;
                       e <- editor_proc{n1}{n2} s1 s2
              | some => e.notlast ;
                        c <- recv s2 ;
                        s1.ins ;
                        send s1 c ;
                        e <- editor_proc{n1+1}{n2-1} s1 s2
             )
  | input => c <- recv e ;
             s1.ins ;
             send s1 c ;
             e <- editor_proc{n1+1}{n2} s1 s2
  | delete => s1.del ;
              case s1 (
                none => wait s1 ;
                        e.empty ;
                        s1 <- empty ;
                        e <- editor_proc{n1}{n2} s1 s2
              | some => c <- recv s1 ;
                        e.notempty ;
                        send e c ;
                        e <- editor_proc{n1-1}{n2} s1 s2
              )
  )

proc e <- edit =
  s1 <- empty ;
  s2 <- empty ;
  e <- editor_proc{0}{0} s1 s2

type nat = +{z : 1, s : nat}

type operator = +{plus : 1, minus : 1, mult : 1}

type postfix{n}{v} = +{num : ?{n > 0}. nat * postfix{n-1}{v+1},
                       op : ?{n > 0}. ?{v > 1}. operator * postfix{n-1}{v-1},
                       end : ?{n = 0}. ?{v = 1}. 1}

decl natempty : . |- (s : natstack{0})

type natstack{n} = &{ins : nat -o natstack{n+1},
                     del : +{none : ?{n = 0}. 1,
                             some : ?{n > 0}. nat * natstack{n-1}}}

decl succ : (m : nat) |- (n : nat)
decl pred : (m : nat) |- (n : nat)
decl add : (n1 : nat) (n2 : nat) |- (n : nat)
decl subtract : (n1 : nat) (n2 : nat) |- (n : nat)
decl multiply : (n1 : nat) (n2 : nat) |- (n : nat)

decl operate : (o : operator) (n1 : nat) (n2 : nat) |- (n : nat)

proc n <- operate o n1 n2 =
  case o (
    plus => wait o ;
            n <- add n1 n2
  | minus => wait o ;
             n <- subtract n1 n2
  | mult => wait o ;
            n <- multiply n1 n2
  )

proc n <- pred m =
  case m (
    z => n.z ;
         wait m ;
         close n
  | s => n <-> m
  )

proc n <- succ m =
  n.s ;
  n <-> m

proc n <- add n1 n2 =
  case n2 (
    z => wait n2 ;
         n <-> n1
  | s => n1' <- succ n1 ;
         n <- add n1' n2
  )

proc n <- subtract n1 n2 =
  case n2 (
    z => wait n2 ;
         n <-> n1
  | s => n1' <- pred n1 ;
         n <- subtract n1' n2
  )

decl evaluate{n} : (e : postfix{n}{0}) |- (N : nat)
decl eval0{n} : (e : postfix{n}{0}) (s : natstack{0}) |- (N : nat)
decl eval1{n} : (e : postfix{n}{1}) (s : natstack{1}) |- (N : nat)
decl eval2{n}{v} : (e : postfix{n}{v+2}) (s : natstack{v+2}) |- (N : nat)
decl eval11{n}{v} : (e : postfix{n}{v+1}) (s : natstack{v+1}) |- (N : nat)


proc N <- evaluate{n} e =
  s <- natempty ;
  N <- eval0{n} e s

proc N <- eval0{n} e s =
  case e (
    num => n <- recv e ;
           s.ins ;
           send s n ;
           N <- eval1{n-1} e s
  )

proc N <- eval1{n} e s =
  case e (
    num => n <- recv e ;
           s.ins ;
           send s n ;
           N <- eval2{n-1}{0} e s
  | end => wait e ;
           s.del ;
           case s (
             some => n <- recv s ;
                     s.del ;
                     case s (
                       none => wait s ;
                               N <-> n
                     )
           )
  )

proc N <- eval2{n}{v} e s =
  case e (
    num => n <- recv e ;
           s.ins ;
           send s n ;
           N <- eval2{n-1}{v+1} e s
  | op => o <- recv e ;
          s.del ;
          case s (
            some => n1 <- recv s ;
                    s.del ;
                    case s (
                      some => n2 <- recv s ;
                              n <- operate o n1 n2 ;
                              s.ins ;
                              send s n ;
                              N <- eval11{n-1}{v} e s
                    )
          )
  )

proc N <- eval11{n}{v} e s =
  s.del ;
  case s (
    some => n1 <- recv s ;
            s.del ;
            case s (
              none => wait s ;
                      s <- natempty ;
                      s.ins ;
                      send s n1 ;
                      N <- eval1{n} e s
            | some => n2 <- recv s ;
                      s.ins ;
                      send s n2 ;
                      s.ins ;
                      send s n1 ;
                      N <- eval2{n}{v-1} e s
            )
  )