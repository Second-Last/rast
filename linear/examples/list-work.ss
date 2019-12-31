#test success
#options --work=send --syntax=implicit

%%% natural numbers as "generic" list elements
type nat = +{zero : 1, succ : nat}

type list{n}{p} = +{cons : ?{n > 0}. |{p}> nat * list{n-1}{p},
                    nil : ?{n = 0}. 1}

decl nil{p} : . |{2}- (l : list{0}{p})
proc l <- nil{p} <- = l.nil ; close l

decl cons{n}{p} : (x : nat) (t : list{n}{p}) |{p+2}- (l : list{n+1}{p})
proc l <- cons{n}{p} <- x t = l.cons ; send l x ; l <- t

decl append{n}{k}{p} : (l1 : list{n}{p+2}) (l2 : list{k}{p}) |- (l : list{n+k}{p})
proc l <- append{n}{k}{p} <- l1 l2 =
  case l1 ( cons => l.cons ;
                    n <- recv l1 ; send l n ;
                    l <- append{n-1}{k}{p} <- l1 l2
          | nil => wait l1 ; l <- l2 )

decl rev{n}{k}{p} : (l : list{n}{p+2}) (a : list{k}{p}) |- (r : list{n+k}{p})

proc r <- rev{n}{k}{p} <- l a =
  case l ( cons => x <- recv l ;
                   a' <- cons{k}{p} <- x a ;
                   r <- rev{n-1}{k+1}{p} <- l a'
         | nil => wait l ; r <- a )

decl drain2{n}{p} : (k : list{n}{p+2}) |{2}- (l : list{n}{p})
proc l <- drain2{n}{p} <- k =
  case k ( cons => x <- recv k ;
                   l.cons ; send l x ;
                   l <- drain2{n-1}{p} <- k
         | nil => wait k ; l.nil ; close l )

decl charge2{n}{p} : (k : list{n}{p}) |{4*n+2}- (l : list{n}{p+2})
proc l <- charge2{n}{p} <- k =
  case k ( cons => x <- recv k ;
                   l.cons ; send l x ;
                   l <- charge2{n-1}{p} <- k
         | nil => wait k ; l.nil ; close l )


decl alternate{m}{n}{p} : (l1 : list{m}{p+2}) (l2 : list{n}{p+2}) |{2}- (l : list{m+n}{p})
proc l <- alternate{m}{n}{p} <- l1 l2 =
  case l1 ( cons => x <- recv l1 ;
                    l.cons ; send l x ;
                    l <- alternate{n}{m-1}{p} <- l2 l1
          | nil => wait l1 ;
                   l <- drain2{n}{p} <- l2 )

type mapper = &{ next : nat -o nat * mapper,
                 done : 1 }

decl map{n}{p} : (k : list{n}{p+4}) (m : mapper) |{3}- (l : list{n}{p})

proc l <- map{n}{p} <- k m =
  case k ( cons => x <- recv k ;
                   m.next ; send m x ;
                   y <- recv m ;
                   l.cons ; send l y ;
                   l <- map{n-1}{p} <- k m
         | nil => wait k ;
                  m.done ; wait m ;
                  l.nil ; close l )

type folder = &{ next : nat -o nat -o nat * folder,
                 done : 1 }

decl fold{n}{p} :  (f : folder) (k : list{n}{p+3}) (y : nat) |{1}- (r : nat)
proc r <- fold{n}{p} <- f k y =
  case k ( cons => x <- recv k ;
                   f.next ; send f x ; send f y ; 
                   y' <- recv f ;
                   r <- fold{n-1}{p} <- f k y'
         | nil => wait k ;                   
                  f.done ; wait f ;
                  r <- y )

decl split{n}{p} : (l : list{2*n}{p+5}) |{7}- (l12 : list{n}{p} * list{n}{p} * 1)
decl split'{n}{p} : (l : list{2*n+1}{p+5}) |{7}- (l12 : list{n}{p} * list{n+1}{p} * 1)

proc l12 <- split{n}{p} <- l =
  case l (cons => x <- recv l ;
                  l12' <- split'{n-1}{p} <- l ;
                  l1' <- recv l12' ; l2' <- recv l12' ; wait l12' ;
                  l1 <- cons{n-1}{p} <- x l1' ;
                  send l12 l1 ; send l12 l2' ; close l12
         | nil => wait l ;
                  l1 <- nil{p} <- ; send l12 l1 ;
                  l2 <- nil{p} <- ; send l12 l2 ; close l12 )
proc l12 <- split'{n}{p} <- l =                   
  case l (cons => x <- recv l ;
                  l12' <- split{n}{p} <- l ;
                  l1' <- recv l12' ; l2' <- recv l12' ; wait l12' ;
                  l2 <- cons{n}{p} <- x l2' ;
                  send l12 l1' ; send l12 l2 ; close l12
         % no nil case
         )

%%% Stack data structure
%%% Prepay for pop during push operation
type stack{n} = &{ push : <{4}| nat -o stack{n+1},
                   pop : +{ none : ?{n = 0}. 1,
                            some : ?{n > 0}. nat * stack{n-1} } }

%%% Stack implemented as a list where each element
%%% has potential 2 as needed for the pop operation
decl stack_list{n} : (l : list{n}{2}) |{2}- (s : stack{n})
proc s <- stack_list{n} <- l =
  case s ( push => x <- recv s ;
                   l' <- cons{n}{2} <- x l ;
                   s <- stack_list{n+1} <- l'
         | pop => case l ( cons => s.some ;
                                   x <- recv l ;
                                   send s x ;
                                   s <- stack_list{n-1} <- l
                         | nil => s.none ; wait l ;
                                  close s ) )

decl stack_new{n} : . |{4}- (s : stack{0})
proc s <- stack_new{n} <- =
  l0 <- nil{2} <- ;
  s <- stack_list{0} <- l0

%%% Stack as a chain of elements
%%% Each element has potential 2 for the pop operation
decl bot : . |{2}- (s : stack{0})
decl top{n} : (x : nat) (t : stack{n}) |{2}- (s : stack{n+1})

proc s <- bot <- =
  case s ( push => x <- recv s ;
                   e <- bot <- ;
                   s <- top{0} <- x e
         | pop => s.none ; close s )

proc s <- top{n} <- x t =
  case s ( push => y <- recv s ;
                   t' <- top{n} <- x t ;
                   s <- top{n+1} <- y t'
         | pop => s.some ; send s x ;
                  s <- t )

%%% Queue data structure
%%% First version using two lists, with constant amortized
%%% cost for for enqueue and dequeue operations

type queue{n} = &{ enq : <{6}| nat -o queue{n+1},
                   deq : <{4}| deq_reply{n} }
type deq_reply{n} = +{ none : ?{n = 0}. 1,
                       some : ?{n > 0}. nat * queue{n-1} }

decl queue_lists{n1}{n2} : (in : list{n1}{4}) (out : list{n2}{2}) |- (q : queue{n1+n2})
decl queue_rev{n1} : (in : list{n1}{4}) |{4}- (q : deq_reply{n1})

proc q <- queue_lists{n1}{n2} <- in out =
  case q ( enq => x <- recv q ;
                  in' <- cons{n1}{4} <- x in ;
                  q <- queue_lists{n1+1}{n2} <- in' out
         | deq => case out ( cons => x <- recv out ;
                                     q.some ; send q x ;
                                     q <- queue_lists{n1}{n2-1} <- in out
                           | nil => wait out ;
                                    q <- queue_rev{n1} <- in ) )

proc q <- queue_rev{n1} <- in =
  out0 <- nil{2} <- ;
  out <- rev{n1}{0}{2} <- in out0 ;
  case out ( cons => x <- recv out ;
                     q.some ; send q x ;
                     in0 <- nil{4} <- ;
                     q <- queue_lists{0}{n1-1} <- in0 out
           | nil => wait out ;
                    q.none ; close q )

decl queue_new : . |{4}- (q : queue{0})
proc q <- queue_new <- =
  in0 <- nil{4} <- ;
  out0 <- nil{2} <- ;
  q <- queue_lists{0}{0} <- in0 out0


%%% Queue as a bucket brigade
%%% The cost of enq here cannot be amortized

type queue'{n} = &{ enq : <{2*n+2}| nat -o queue'{n+1},
                    deq : +{ none : ?{n = 0}. 1,
                             some : ?{n > 0}. nat * queue'{n-1} } }

decl back : . |{2}- (q : queue'{0})
decl front{n} : (x : nat) (r : queue'{n}) |{2}- (q : queue'{n+1})

proc q <- back <- =
  case q ( enq => x <- recv q ;
                  b <- back <- ;
                  q <- front{0} <- x b
         | deq => q.none ; close q )

proc q <- front{n} <- x r =
  case q ( enq => y <- recv q ;
                  r.enq ; send r y ;
                  q <- front{n+1} <- x r
         | deq => q.some ; send q x ;
                  q <- r )
