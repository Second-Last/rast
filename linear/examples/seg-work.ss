#test success
#options --work=send --time=none --syntax=implicit

%%% List segments, as linear "functions" from a tail to a list
%%% Tracks size of the segments and work required for various
%%% operations, which are all constant-work.

%%% Polymorphism is "faked", for now.
type A = 1

%%% Lists here do not carry any potential, but nil and cons do.

type list{n} = +{ cons : ?{n > 0}. A * list{n-1},
                  nil : ?{n = 0}. 1 }

decl nil : . |{2}- (l : list{0})
proc l <- nil <- = l.nil ; close l

decl cons{n} : (x : A) (t : list{n}) |{2}- (l : list{n+1})
proc l <- cons{n} <- x t =
       l.cons ; send l x ; l <- t

%%% Segments are processes that receive a list (the tail)
%%% and become a list.  The tail is parameterized over
%%% its length k so that arbitrary tails can be added
%%% to a segment.

type seg{n} = !k. list{k} -o list{n+k}

%%% Empty segment
decl empty : . |{1}- (s : seg{0})
proc s <- empty <- =
       {k} <- recv s ;
       t <- recv s ;
       s <- t

%%% Singleton segment
decl one : (x : A) |{2}- (s : seg{1})
proc s <- one <- x =
       {k} <- recv s ;
       t <- recv s ;
       t' <- cons{k} <- x t ;
       s <- t'

%%% Concatenation of two segments, with only
%%% two units of work
decl concat{n1}{n2} : (s1 : seg{n1}) (s2 : seg{n2}) |{2}- (s : seg{n1+n2})
proc s <- concat{n1}{n2} <- s1 s2  =
       {k} <- recv s ;
       t <- recv s ;
       send s2 {k} ;
       send s2 t ;
       send s1 {n2+k} ;
       send s1 s2 ;
       s <- s1

%%% Prepending an element to a segment
decl prepend{n} : (x : A) (t : seg{n}) |{4}- (s : seg{n+1})
proc s <- prepend{n} <- x t =
       u <- one <- x ;
       s <- concat{1}{n} <- u t

%%% Appending an element to a segment
decl append{n} : (x : A) (t : seg{n}) |{4}- (s : seg{n+1})
proc s <- append{n} <- x t =
       u <- one <- x ;
       s <- concat{n}{1} <- t u

%%% Converting a segement to a list
decl tolist{n} : (s : seg{n}) |{5}- (l : list{n})
proc l <- tolist{n} <- s =
       t <- nil <- ;
       send s {0} ;
       send s t ;
       l <- s
