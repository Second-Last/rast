#test success
#options --work=none --time=none --syntax=implicit

type bin = +{ b0 : bin,
              b1 : bin,
              e : 1 }

decl zero : . |- (x : bin)
decl succ : (y : bin) |- (x : bin)

proc x <- zero =
  x.e ;
  close x

proc x <- succ y =
  case y ( b0 => x.b1 ;
                 x <-> y
         | b1 => x.b0 ;
                 x <- succ y
         | e => x.b1 ;
                x.e ;
                wait y ;
                close x
         )

decl dealloc : (y : bin) |- (u : 1)
proc u <- dealloc y =
  case y ( b0 => u <- dealloc y
         | b1 => u <- dealloc y
         | e => wait y ;
                close u
         )

% t : trie       represents a multiset of n binary numbers
% t.ins(x)       inserts one new copy of x into the trie t
% t.del(x) = c   deletes all copies of x from the tri t, returning the multiplicity of x

type trie = &{ ins : bin -o trie,
               del : bin -o bin * trie }


decl leaf : . |- (t : trie)
decl node : (l : trie) (c : bin) (r : trie) |- (t : trie)

proc t <- leaf =
  case t ( ins => x <- recv t ;
                  case x ( b0 => l <- leaf ;
                                 z <- zero ;
                                 r <- leaf ;
                                 l.ins ;
                                 send l x ;
                                 t <- node l z r
                         | b1 => l <- leaf ;
                                 z <- zero ;
                                 r <- leaf ;
                                 r.ins ;
                                 send r x ;
                                 t <- node l z r
                         | e =>  wait x ;
                                 l <- leaf ;
                                 z <- zero ;
                                 o <- succ z ;
                                 r <- leaf ;
                                 t <- node l o r )
         | del => x <- recv t ;
                  u <- dealloc x ; wait u ;
                  z <- zero ;
                  send t z ;
                  t <- leaf
         )

proc t <- node l c r =
  case t ( ins => x <- recv t ;
                  case x ( b0 => l.ins ;
                                 send l x ;
                                 t <- node l c r
                         | b1 => r.ins ;
                                 send r x ;
                                 t <- node l c r
                         | e => wait x ;
                                c' <- succ c ;
                                t <- node l c' r )
          | del => x <- recv t ;
                   case x ( b0 => l.del ;
                                  send l x ;
                                  a <- recv l ;
                                  send t a ;
                                  t <- node l c r
                          | b1 => r.del ;
                                  send r x ;
                                  a <- recv r ;
                                  send t a ;
                                  t <- node l c r
                          | e =>  wait x ;
                                  send t c ;
                                  z <- zero ;
                                  t <- node l z r
                          )
          )
