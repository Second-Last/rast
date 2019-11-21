#test success
#options --work=none --time=none --syntax=implicit

type nat = +{zero : 1, succ : nat}

type list{n} = +{cons : ?{n > 0}. nat * list{n-1},
                 nil : ?{n = 0}. 1}

decl nil : . |- (l : list{0})
proc l <- nil <- = l.nil ; close l

decl cons{n} : (x : nat) (t : list{n}) |- (l : list{n+1})
proc l <- cons{n} <- x t = l.cons ; send l x ; l <- t

decl append{n}{k} : (l1 : list{n}) (l2 : list{k}) |- (l : list{n+k})

proc l <- append{n}{k} <- l1 l2 =
  case l1 ( cons => l.cons ;
                    n <- recv l1 ; send l n ;
                    l <- append{n-1}{k} <- l1 l2
          | nil => wait l1 ; l <- l2 )

decl rev{n}{k} : (l : list{n}) (a : list{k}) |- (r : list{n+k})
proc r <- rev{n}{k} <- l a =
  case l ( cons => a.cons ;
                   x <- recv l ; send a x ;
                   r <- rev{n-1}{k+1}
         | nil => wait l ; r <- a )

type stack{n} = &{ push : nat -o stack{n+1},
                   pop : +{ none : ?{n = 0}. 1,
                            some : ?{n > 0}. nat * stack{n-1} } }

decl stack_list{n} : (l : list{n}) |- (s : stack{n})
proc s <- stack_list{n} <- l =
  case s ( push => x <- recv s ;
                   l' <- cons{n} <- x l ;
                   s <- stack_list{n+1} <- l'
         | pop => case l ( cons => s.some ;
                                   x <- recv l ;
                                   send s x ;
                                   s <- stack_list{n-1} <- l
                         | nil => s.none ; wait l ;
                                  close s ) )
