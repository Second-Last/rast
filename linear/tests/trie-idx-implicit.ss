#test success
#options --work=none --time=none --syntax=implicit

% bin{n} = binary numbers of value n
% leading 0s are allowed here, but could be
% eliminated with b0 : ?{k}. ?{n > 0 & n = 2*k}. bin{k}

type bin{n} = +{ b0 : ?k. ?{n = 2*k}. bin{k},
                 b1 : ?k. ?{n = 2*k+1}. bin{k},
                 e : ?{n = 0}. 1 }

decl zero : . |- (x : bin{0})
decl succ{n} : (y : bin{n}) |- (x : bin{n+1})

proc x <- zero <- =
  x.e ;
  close x

proc x <- succ{n} <- y =
  case y ( b0 => {k} <- recv y ;
                 x.b1 ;
                 send x {k} ;
                 x <- y
         | b1 => {k} <- recv y ;
                 x.b0 ;
                 send x {k+1} ;
                 x <- succ{k} <- y
         | e =>  x.b1 ;
                 send x {0} ;
                 x.e ;
                 wait y ;
                 close x
         )

decl dealloc{n} : (y : bin{n}) |- (u : 1)
proc u <- dealloc{n} <- y =
  case y ( b0 => {k} <- recv y ;
                 u <- dealloc{k} <- y
         | b1 => {k} <- recv y ;
                 u <- dealloc{k} <- y
         | e => wait y ;
                close u )

% t : trie{n}        represents a multiset of n binary numbers
% t.ins(x)       inserts one new copy of x into the trie t
% t.del(x) = c   deletes all copies of x from the tri t, returning the multiplicity of x

type trie{n} = &{ ins : !k. bin{k} -o trie{n+1},
                  del : !k. bin{k} -o ?m. ?{m <= n}. bin{m} * trie{n-m} }


decl leaf : . |- (t : trie{0})
decl node{n1}{m}{n2} : (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2})

proc t <- leaf <- =
  case t ( ins => {k} <- recv t ;
                  x <- recv t ;
                  case x ( b0 =>
                           {k'} <- recv x ;
                           l <- leaf <- ;
                           z <- zero <- ;
                           r <- leaf <- ;
                           l.ins ;
                           send l {k'} ;
                           send l x ;
                           t <- node{1}{0}{0} <- l z r
                         | b1 =>
                           {k'} <- recv x ;
                           l <- leaf <- ;
                           z <- zero <- ;
                           r <- leaf <- ;
                           r.ins ;
                           send r {k'} ;
                           send r x ;
                           t <- node{0}{0}{1} <- l z r
                         | e =>
                           wait x ;
                           l <- leaf <- ;
                           z <- zero <- ;
                           o <- succ{0} <- z ;
                           r <- leaf <- ;
                           t <- node{0}{1}{0} <- l o r )
         | del => {k} <- recv t ;
                  x <- recv t ;
                  u <- dealloc{k} <- x ; wait u ;
                  send t {0} ;
                  z <- zero <- ;
                  send t z ;
                  t <- leaf <-
         )

proc t <- node{n1}{m}{n2} <- l c r =
  case t ( ins => {k} <- recv t ;
                  x <- recv t ;
                  case x ( b0 =>
                           {k'} <- recv x ;
                           l.ins ; send l {k'} ;
                           send l x ;
                           t <- node{n1+1}{m}{n2} <- l c r
                         | b1 =>
                           {k'} <- recv x ;
                           r.ins ; send r {k'} ;
                           send r x ;
                           t <- node{n1}{m}{n2+1} <- l c r
                         | e =>
                           wait x ;
                           c' <- succ{m} <- c ;
                           t <- node{n1}{m+1}{n2} <- l c' r )
          | del => {k} <- recv t ;
                   x <- recv t ;
                   case x ( b0 =>
                            {k'} <- recv x ;
                            l.del ;
                            send l {k'} ;
                            send l x ;
                            {m1} <- recv l ;
                            a <- recv l ;
                            send t {m1} ;
                            send t a ;
                            t <- node{n1-m1}{m}{n2} <- l c r
                          | b1 =>
                            {k'} <- recv x ;
                            r.del ;
                            send r {k'} ;
                            send r x ;
                            {m2} <- recv r ;
                            a <- recv r ;
                            send t {m2} ;
                            send t a ;
                            t <- node{n1}{m}{n2-m2} <- l c r
                          | e =>
                            wait x ;
                            send t {m} ;
                            send t c ;
                            z <- zero <- ;
                            t <- node{n1}{0}{n2} <- l z r
                          )
          )
