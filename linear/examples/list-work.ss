#test approx success
#options --work=send --syntax=implicit

%%% Lists, indexed by their size and potential carried by
%%% each element.  Since true polymorphism isn't currently
%%% supported, we just have lists of natural numbers
%%% but all code is parametric in this choice
%%%
%%% Examples:
%%%
%%% append, reverse, alternate, split
%%% map, fold, filter
%%% stack as a list, stack as a chain
%%% queue as two lists, queue as a bucket brigade

%%% Run this with -v (--verbose) to see the values
%%% in the lists resulting from evaluation

%%% natural numbers as "generic" list elements
% type nat = +{zero : 1, succ : nat}
type nat = ?k. 1

type list{n}{p} = +{ cons : ?{n > 0}. |{p}> nat * list{n-1}{p},
                     nil : ?{n = 0}. 1 }

decl nil{p} : . |{2}- (l : list{0}{p})
proc l <- nil{p} = l.nil ; close l

decl cons{n}{p} : (x : nat) (t : list{n}{p}) |{p+2}- (l : list{n+1}{p})
proc l <- cons{n}{p} x t = l.cons ; send l x ; l <-> t

%%% append
decl append{n}{k}{p} : (l1 : list{n}{p+2}) (l2 : list{k}{p}) |- (l : list{n+k}{p})
proc l <- append{n}{k}{p} l1 l2 =
  case l1 ( cons => x <- recv l1 ;
                    l.cons ; send l x ;
                    l <- append{n-1}{k}{p} l1 l2
          | nil => wait l1 ; l <-> l2 )

%%% Version of append where all lists have the same
%%% potential and we pay the cost up front, externally
decl append'{n}{k}{p} : (l1 : list{n}{p}) (l2 : list{k}{p}) |{2*n}- (l : list{n+k}{p})
proc l <- append'{n}{k}{p} l1 l2 =
  case l1 ( cons => x <- recv l1 ;
                    l.cons ; send l x ;
                    l <- append'{n-1}{k}{p} l1 l2
          | nil => wait l1 ; l <-> l2 )

%%% reverse
decl rev{n}{k}{p} : (l : list{n}{p+2}) (a : list{k}{p}) |- (r : list{n+k}{p})
proc r <- rev{n}{k}{p} l a =
  case l ( cons => x <- recv l ;
                   a' <- cons{k}{p} x a ;
                   r <- rev{n-1}{k+1}{p} l a'
         | nil => wait l ; r <-> a )

decl reverse{n}{p} : (l : list{n}{p+2}) |{2}- (r : list{n}{p})
proc r <- reverse{n}{p} l =
  a <- nil{p} ;
  r <- rev{n}{0}{p} l a

%%% Split a list into two: one with the even elements and one with the odd ones
%%% We could also have l12 : list{n}{p} * list{n}{p} with less work required,
%%% but the code is somewhat asymmetric.
%%% This example illustrates that cases that are impossible, according to the
%%% type, are reconstructed
decl split{n}{p} : (l : list{2*n}{p+5}) |{7}- (l12 : list{n}{p} * list{n}{p} * 1)
decl split'{n}{p} : (l : list{2*n+1}{p+5}) |{7}- (l12 : list{n}{p} * list{n+1}{p} * 1)

proc l12 <- split{n}{p} l =
  case l ( cons => x <- recv l ;
                   l12' <- split'{n-1}{p} l ;
                   l1' <- recv l12' ; l2' <- recv l12' ; wait l12' ;
                   l1 <- cons{n-1}{p} x l1' ;
                   send l12 l1 ; send l12 l2' ; close l12
         | nil => wait l ;
                  l1 <- nil{p} ; send l12 l1 ;
                  l2 <- nil{p} ; send l12 l2 ; close l12 )
proc l12 <- split'{n}{p} l =                   
  case l ( cons => x <- recv l ;
                   l12' <- split{n}{p} l ;
                   l1' <- recv l12' ; l2' <- recv l12' ; wait l12' ;
                   l2 <- cons{n}{p} x l2' ;
                   send l12 l1' ; send l12 l2 ; close l12
         % no nil case
         )

%%% Draining and recharging of potential
%%% We could drain arbitrary potential q, but recharging arbitrary
%%% potential would require (simple) nonlinear constraints.
decl drain2{n}{p} : (k : list{n}{p+2}) |{2}- (l : list{n}{p})
proc l <- drain2{n}{p} k =
  case k ( cons => x <- recv k ;
                   l.cons ; send l x ;
                   l <- drain2{n-1}{p} k
         | nil => wait k ; l.nil ; close l )

decl charge2{n}{p} : (k : list{n}{p}) |{4*n+2}- (l : list{n}{p+2})
proc l <- charge2{n}{p} k =
  case k ( cons => x <- recv k ;
                   l.cons ; send l x ;
                   l <- charge2{n-1}{p} k
         | nil => wait k ; l.nil ; close l )

%%% Next, the version with nonlinear constraints on potential
%%% These are actually easily solved
decl drain{n}{p}{q} : (k : list{n}{p+q+2}) |{2}- (l : list{n}{p})
proc l <- drain{n}{p}{q} k =
  case k ( cons => x <- recv k ;
                   l.cons ; send l x ;
                   l <- drain{n-1}{p}{q} k
         | nil => wait k ; l.nil ; close l )

decl charge{n}{p}{q} : (k : list{n}{p}) |{(q+2)*n+2}- (l : list{n}{p+q})
proc l <- charge{n}{p}{q} k =
  case k ( cons => x <- recv k ;
                   l.cons ; send l x ;
                   l <- charge{n-1}{p}{q} k
         | nil => wait k ; l.nil ; close l )


%%% Alternating elements of two lists 
decl alternate{m}{n}{p} : (l1 : list{m}{p+2}) (l2 : list{n}{p+2}) |{2}- (l : list{m+n}{p})
proc l <- alternate{m}{n}{p} l1 l2 =
  case l1 ( cons => x <- recv l1 ;
                    l.cons ; send l x ;
                    l <- alternate{n}{m-1}{p} l2 l1
          | nil => wait l1 ;
                   l <- drain2{n}{p} l2 )

%%% map
%%% Due to linearity, this is implemented using a mapper
%%% process of recursive type.  However, the type for map
%%% requires some nonlinear constraints
type mapper{q} = &{ next : <{q+1}| nat -o nat * mapper{q},
                    done : <{1}| 1 }

decl map{n}{p}{q} : (k : list{n}{p+4}) (m : mapper{q}) |{3+(n*(q+1)+1)}- (l : list{n}{p})

proc l <- map{n}{p}{q} k m =
  case k ( cons => x <- recv k ;
                   m.next ; send m x ;
                   y <- recv m ;
                   l.cons ; send l y ;
                   l <- map{n-1}{p}{q} k m
         | nil => wait k ;
                  m.done ; wait m ;
                  l.nil ; close l )

%%% fold
%%% Due to linearity, this is implemented using a folder
%%% process of recursive type
%%% For examples, a folder should be parameterized by potential (see mapper{q})
type folder = &{ next : nat -o nat -o nat * folder,
                 done : 1 }

decl fold{n}{p} :  (f : folder) (k : list{n}{p+3}) (y : nat) |{1}- (r : nat)
proc r <- fold{n}{p} f k y =
  case k ( cons => x <- recv k ;
                   f.next ; send f x ; send f y ; 
                   y' <- recv f ;
                   r <- fold{n-1}{p} f k y'
         | nil => wait k ;                   
                  f.done ; wait f ;
                  r <-> y )

%%% filter
%%% Due to linearity, this is implemented using a selector process
%%% of recursive type which returns the element it is given to test.
%%% For examples, a selector should be parameterized by potential (see mapper{q})
type selector = &{ next : nat -o +{ false : selector, true : nat * selector },
                   done : 1 }

%%% This example illustrates one way to deal with lists of uncertain
%%% length, here bounded by the length of the input list

%%% bdd_list{n} is a list of some length m <= n
%%% The nil, cons, and resize operations could be expanded in-line, but
%%% we separate them out to isolate them.
type bdd_list{n}{p} = ?m. ?{m <= n}. list{m}{p}

decl bdd_nil{p} : . |{2}- (l : bdd_list{0}{p})
proc l <- bdd_nil{p} = send l {0} ; l.nil ; close l

decl bdd_cons{n}{p} : (x : nat) (k : bdd_list{n}{p}) |{p+2}- (l : bdd_list{n+1}{p})
proc l <- bdd_cons{n}{p} x k =
  {m} <- recv k ;
  send l {m+1} ;
  l.cons ; send l x ; l <-> k

decl bdd_resize{n}{p} : (k : bdd_list{n}{p}) |- (l : bdd_list{n+1}{p})
proc l <- bdd_resize{n}{p} k =
  {m} <- recv k ;
  send l {m} ;
  l <-> k

decl filter{n}{p} : (s : selector) (k : list{n}{p+4}) |{3}- (l : bdd_list{n}{p})
proc l <- filter{n}{p} s k =
  case k ( cons => x <- recv k ;
                   s.next ; send s x ;
                   case s ( false => l' <- filter{n-1}{p} s k ;
                                     l <- bdd_resize{n-1}{p} l'
                          | true => x' <- recv s ;
                                    l' <- filter{n-1}{p} s k ;
                                    l <- bdd_cons{n-1}{p} x' l' )
          | nil => wait k ; s.done ; wait s ;
                   l <- bdd_nil{p} )

%%% Stack data structure
%%% Prepay for pop during push operation
type stack{n} = &{ push : <{4}| nat -o stack{n+1},
                   pop : +{ none : ?{n = 0}. 1,
                            some : ?{n > 0}. nat * stack{n-1} } }

%%% Stack implemented as a list where each element
%%% has potential 2 as needed for the pop operation
decl stack_list{n} : (l : list{n}{2}) |{2}- (s : stack{n})
proc s <- stack_list{n} l =
  case s ( push => x <- recv s ;
                   l' <- cons{n}{2} x l ;
                   s <- stack_list{n+1} l'
         | pop => case l ( cons => s.some ;
                                   x <- recv l ;
                                   send s x ;
                                   s <- stack_list{n-1} l
                         | nil => s.none ; wait l ;
                                  close s ) )

decl stack_new{n} : . |{4}- (s : stack{0})
proc s <- stack_new{n} =
  l0 <- nil{2} ;
  s <- stack_list{0} l0

%%% Stack as a chain of elements
%%% Each element has potential 2 for the pop operation
decl bot : . |{2}- (s : stack{0})
decl top{n} : (x : nat) (t : stack{n}) |{2}- (s : stack{n+1})

proc s <- bot =
  case s ( push => x <- recv s ;
                   e <- bot ;
                   s <- top{0} x e
         | pop => s.none ; close s )

proc s <- top{n} x t =
  case s ( push => y <- recv s ;
                   t' <- top{n} x t ;
                   s <- top{n+1} y t'
         | pop => s.some ; send s x ;
                  s <-> t )

%%% Queue data structure
%%% First version using two lists, with constant amortized
%%% cost for for enqueue and dequeue operations

type queue{n} = &{ enq : <{6}| nat -o queue{n+1},
                   deq : <{4}| deq_reply{n} }
type deq_reply{n} = +{ none : ?{n = 0}. 1,
                       some : ?{n > 0}. nat * queue{n-1} }

decl queue_lists{n1}{n2} : (in : list{n1}{4}) (out : list{n2}{2}) |- (q : queue{n1+n2})
decl queue_rev{n1} : (in : list{n1}{4}) |{4}- (q : deq_reply{n1})

proc q <- queue_lists{n1}{n2} in out =
  case q ( enq => x <- recv q ;
                  in' <- cons{n1}{4} x in ;
                  q <- queue_lists{n1+1}{n2} in' out
         | deq => case out ( cons => x <- recv out ;
                                     q.some ; send q x ;
                                     q <- queue_lists{n1}{n2-1} in out
                           | nil => wait out ;
                                    q <- queue_rev{n1} in ) )

proc q <- queue_rev{n1} in =
  out <- reverse{n1}{2} in ;
  case out ( cons => x <- recv out ;
                     q.some ; send q x ;
                     in0 <- nil{4} ;
                     q <- queue_lists{0}{n1-1} in0 out
           | nil => wait out ;
                    q.none ; close q )

decl queue_new : . |{4}- (q : queue{0})
proc q <- queue_new =
  in0 <- nil{4} ;
  out0 <- nil{2} ;
  q <- queue_lists{0}{0} in0 out0


%%% Queue as a bucket brigade
%%% The cost of enq here cannot be amortized

type queue'{n} = &{ enq : <{2*n+2}| nat -o queue'{n+1},
                    deq : +{ none : ?{n = 0}. 1,
                             some : ?{n > 0}. nat * queue'{n-1} } }

decl back : . |{2}- (q : queue'{0})
decl front{n} : (x : nat) (r : queue'{n}) |{2}- (q : queue'{n+1})

proc q <- back =
  case q ( enq => x <- recv q ;
                  b <- back ;
                  q <- front{0} x b
         | deq => q.none ; close q )

proc q <- front{n} x r =
  case q ( enq => y <- recv q ;
                  r.enq ; send r y ;
                  q <- front{n+1} x r
         | deq => q.some ; send q x ;
                  q <-> r )

%%% Examples

decl the{k} : . |{1}- (n : nat)
proc n <- the{k} = send n {k} ; close n

decl list123{p} : . |{(p+2+1)*3+2}- (l : list{3}{p})
proc l <- list123{p} =
  k1 <- the{1} ;
  k2 <- the{2} ;
  k3 <- the{3} ;
  l.cons ; send l k1 ; 
  l.cons ; send l k2 ;
  l.cons ; send l k3 ;
  l.nil ; close l

decl list45{p} : . |{(p+2+1)*2+2}- (l : list{2}{p})
proc l <- list45{p} =
  k4 <- the{4} ;
  k5 <- the{5} ;
  l.cons ; send l k4 ; l.cons ; send l k5 ;
  l.nil ; close l

decl list12345_2 : . |{23+12}- (l : list{5}{2})
proc l <- list12345_2 =
  l1 <- list123{4} ;
  l2 <- list45{2} ;
  l <- append{3}{2}{2} l1 l2

decl list54321_0 : . |{23+12+2}- (l : list{5}{0})
proc l <- list54321_0 =
  l1 <- list12345_2 ;
  l <- reverse{5}{0} l1

decl split54321_0 : . |{(23+12+2)+37+7}- (ll : list{2}{0} * list{3}{0} * 1)
proc ll <- split54321_0 =
  l_0 <- list54321_0 ;
  l_5 <- charge{5}{0}{5} l_0 ;
  ll <- split'{2}{0} l_5

decl alt45231_0 : . |{81+10+14+2}- (l : list{5}{0})
proc l <- alt45231_0 =
  ll <- split54321_0 ;
  l1 <- recv ll ; l2 <- recv ll ; wait ll ;
  l1' <- charge{2}{0}{2} l1 ;
  l2' <- charge{3}{0}{2} l2 ;
  l <- alternate{2}{3}{0} l1' l2'

decl m_plus1 : . |- (m : mapper{1})
proc m <- m_plus1 =
  case m ( next => x <- recv m ;
                   {k} <- recv x ; wait x ;
                   y <- the{k+1} ;   % 1 erg
                   send m y ;           % 1 erg (fixed overhead)
                   m <- m_plus1
         | done => close m )

decl map56342_0 : . |{107+32+14}- (l : list{5}{0})
proc l <- map56342_0 =
  l_0 <- alt45231_0 ;            % 107 erg
  l_4 <- charge{5}{0}{4} l_0 ;   % 32 erg
  m <- m_plus1 ;
  l <- map{5}{0}{1} l_4 m        % 14 erg

exec list12345_2
exec list54321_0
exec split54321_0
exec alt45231_0
exec map56342_0

%%% Currently no examples for fold, filter, stacks, or queues
