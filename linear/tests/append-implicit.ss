#test success
#options --work=none --time=none --syntax=implicit

type nat = +{zero : 1, succ : nat}

type list = +{cons : nat * list, nil : 1}

decl nil : . |- (l : list)
proc l <- nil = l.nil ; close l

decl cons : (x : nat) (t : list) |- (l : list)
proc l <- cons x t = l.cons ; send l x ; l <-> t

decl append : (l1 : list) (l2 : list) |- (l : list)

proc l <- append l1 l2 =
  case l1 ( cons => l.cons ;
                    n <- recv l1 ; send l n ;
                    l <- append l1 l2
          | nil => wait l1 ; l <-> l2 )

type stack = &{ push : nat -o stack,
                pop : +{ none : 1, some : nat * stack } }

decl stack_list : (l : list) |- (s : stack)
proc s <- stack_list l =
  case s ( push => x <- recv s ;
                   l' <- cons x l ;
                   s <- stack_list l'
         | pop => case l ( cons => s.some ;
                                   x <- recv l ;
                                   send s x ;
                                   s <- stack_list l
                         | nil => s.none ; wait l ;
                                  close s ) )
