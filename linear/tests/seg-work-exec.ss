#test success
#options --work=send --time=none --syntax=implicit

type nat = +{ zero : 1, succ : nat }
decl zero : . |{2}- (x : nat)
decl one : . |{3}- (x : nat)
decl two : . |{4}- (x : nat)

proc x <- zero <- = x.zero ; close x
proc x <- one <- = x.succ ; x <- zero <-
proc x <- two <- = x.succ ; x <- one <-
exec zero
exec one
exec two

type list{n} = +{ cons : ?{n > 0}. nat * list{n-1},
                  nil : ?{n = 0}. 1 }

decl nil : . |{2}- (l : list{0})
proc l <- nil <- = l.nil ; close l

decl cons{n} : (x : nat) (t : list{n}) |{2}- (l : list{n+1})
proc l <- cons{n} <- x t =
       l.cons ; send l x ; l <- t

type seg{n} = !k. list{k} -o list{n+k}

decl empty : . |{1}- (s : seg{0})
proc s <- empty <- =
       {k} <- recv s ;
       t <- recv s ;
       s <- t

decl singleton : (x : nat) |{2}- (s : seg{1})
proc s <- singleton <- x =
       {k} <- recv s ;
       t <- recv s ;
       t' <- cons{k} <- x t ;
       s <- t'

decl concat{n1}{n2} : (s1 : seg{n1}) (s2 : seg{n2}) |{2}- (s : seg{n1+n2})
proc s <- concat{n1}{n2} <- s1 s2  =
       {k} <- recv s ;
       t <- recv s ;
       send s2 {k} ;
       send s2 t ;
       send s1 {n2+k} ;
       send s1 s2 ;
       s <- s1

decl prepend{n} : (x : nat) (t : seg{n}) |{4}- (s : seg{n+1})
proc s <- prepend{n} <- x t =
       u <- singleton <- x ;
       s <- concat{1}{n} <- u t

decl append{n} : (x : nat) (t : seg{n}) |{4}- (s : seg{n+1})
proc s <- append{n} <- x t =
       u <- singleton <- x ;
       s <- concat{n}{1} <- t u

decl tolist{n} : (s : seg{n}) |{5}- (l : list{n})
proc l <- tolist{n} <- s =
       t <- nil <- ;
       send s {0} ;
       send s t ;
       l <- s

decl l201 : . |{27}- (l : list{3})
proc l <- l201 <- =
  s <- empty <- ;   % 1 erg
  z <- zero <- ;    % 2 erg
  sz <- one <- ;    % 3
  ssz <- two <- ;   % 4
  s0 <- prepend{0} <- z s ;  % 4
  s01 <- append{1} <- sz s0 ; % 4
  s201 <- prepend{2} <- ssz s01 ; % 4
  l <- tolist{3} <- s201 % 5

exec l201
