#test success
#options --work=send --time=none --syntax=implicit

type A = 1

type list{n} = +{ cons : ?{n > 0}. A * list{n-1},
                  nil : ?{n = 0}. 1 }

decl nil : . |{2}- (l : list{0})
proc l <- nil <- = l.nil ; close l

decl cons{n} : (x : A) (t : list{n}) |{2}- (l : list{n+1})
proc l <- cons{n} <- x t =
       l.cons ; send l x ; l <- t

type seg{n}{k} = list{k} -o list{n+k}

decl empty{k} : . |{1}- (s : seg{0}{k})
proc s <- empty{k} <- =
       t <- recv s;
       s <- t

decl one{k} : (x : A) |{2}- (s : seg{1}{k})
proc s <- one{k} <- x =
       t <- recv s ;
       t' <- cons{k} <- x t ;
       s <- t'

decl concat{n1}{n2}{k} : (s1 : seg{n1}{n2+k}) (s2 : seg{n2}{k}) |{2}- (s : seg{n1+n2}{k})
proc s <- concat{n1}{n2}{k} <- s1 s2  =
       t <- recv s ;
       send s2 t ;
       send s1 s2 ;
       s <- s1

decl prepend{n}{k} : (x : A) (t : seg{n}{k}) |{4}- (s : seg{n+1}{k})
proc s <- prepend{n}{k} <- x t =
       u <- one{n+k} <- x ;
       s <- concat{1}{n}{k} <- u t

decl append{n}{k} : (x : A) (t : seg{n}{k+1}) |{4}- (s : seg{n+1}{k})
proc s <- append{n}{k} <- x t =
       u <- one{k} <- x ;
       s <- concat{n}{1}{k} <- t u

decl tolist{n} : (s : seg{n}{0}) |{5}- (l : list{n})
proc l <- tolist{n} <- s =
       t <- nil <- ;
       send s t ;
       l <- s
