#test success
#options --work=send --time=none --syntax=implicit

type nat = +{zero : 1, succ : nat}

type list{n}{p} = +{cons : ?{n > 0}. |{p}> nat * list{n-1}{p},
                    nil : ?{n = 0}. 1}

decl nil : . |{2}- (l : list{0}{0})
proc l <- nil <- = l.nil ; close l

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

type stack{n} = &{ push : <{4}| nat -o stack{n+1},
                   pop : +{ none : ?{n = 0}. 1,
                            some : ?{n > 0}. nat * stack{n-1} } }

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
