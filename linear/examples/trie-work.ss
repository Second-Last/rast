#test success
#options --work=send --time=none --syntax=implicit

%%% bin{n}{p} = binary numbers of value n where each bit carries potential p
%%% Leading zeros are not allowed, so that the multiset representation
%%% is correct.

type bin{n}{p} = +{ b0 : ?{n > 0}. ?k. ?{n = 2*k}. |{p}> bin{k}{p},
                    b1 : ?{n > 0}. ?k. ?{n = 2*k+1}. |{p}> bin{k}{p},
                    e : ?{n = 0}. 1 }

%%% zero, succ, and copy are not used on the trie
%%% copy is required because the input and output bits
%%% do not carry the same potential
decl zero{p} : . |{2}- (x : bin{0}{p})
decl succ{n}{p} : (y : bin{n}{p+1}) |{p+3}- (x : bin{n+1}{p})
decl copy{n}{p} : (y : bin{n}{p+1}) |{2}- (x : bin{n}{p})

proc x <- zero{p} <- =
  x.e ;
  close x

proc y <- succ{n}{p} <- x =
  case x ( b0 => {k} <- recv x ;
                 y.b1 ;
                 send y {k} ;
                 y <- copy{k}{p} <- x
         | b1 => {k} <- recv x ;
                 y.b0 ;
                 send y {k+1} ;
                 y <- succ{k}{p} <- x
         | e =>  y.b1 ;
                 send y {0} ;
                 y.e ;
                 wait x ;
                 close y
         )

proc y <- copy{n}{p} <- x =
  case x ( b0 => {k} <- recv x ;
                 y.b0 ;
                 send y {k} ;
                 y <- copy{k}{p} <- x
         | b1 => {k} <- recv x ;
                 y.b1 ;
                 send y {k} ;
                 y <- copy{k}{p} <- x
         | e =>  y.e ;
                 wait x ;
                 close y
         )

%%% drop{n}{p} deallocates a binary number of value n with potential p

decl drop{n}{p} : (x : bin{n}{p}) |{1}- (u : 1)
proc u <- drop{n}{p} <- x =
  case x ( b0 => {k} <- recv x ;
                 u <- drop{k}{p} <- x
         | b1 => {k} <- recv x ;
                 u <- drop{k}{p} <- x
         | e => wait x ;
                close u )

%%% c : ctr{n} represents binary counter value n
%%% c.inc increments c
%%% c.val "returns" value as binary number with 0 potential
%%%
%%% The potential is an overestimate, since we cannot accurately
%%% track the number of bits in the counter

type ctr{n} = &{ inc : <{3}| ctr{n+1},
                 val : <{2}| bin{n}{0} }  % potential 0 here for simplicity

decl empty         :            . |-    (c : ctr{0})
decl bit0{n|n > 0} : (d : ctr{n}) |{2}- (c : ctr{2*n})
decl bit1{n}       : (d : ctr{n}) |{3}- (c : ctr{2*n+1})

proc c <- empty <- =
  case c ( inc => c0 <- empty <- ;
                  c <- bit1{0} <- c0
         | val => c.e ; close c )

proc c <- bit0{n} <- d =
  case c ( inc => c <- bit1{n} <- d
         | val => c.b0 ; send c {n};
                  d.val ; c <- d )

proc c <- bit1{n} <- d =
  case c ( inc => d.inc ;
                  c <- bit0{n+1} <- d
         | val => c.b1 ; send c {n} ;
                  d.val ; c <- d )

%%% t : trie{n}    represents a multiset of n binary numbers
%%% t.ins(x)       inserts one new copy of x into the trie t
%%% t.del(x) = c   deletes all copies of x from the tri t, returning the multiplicity of x
%%%
%%% Each bit in the number to be stored or deleted requires constant
%%% potential, plus a constant overhead for the empty bit string e.

type trie{n} = &{ ins : <{4}| !k. bin{k}{5} -o trie{n+1},    % bin{k}{4} would be sufficient here
                  del : <{5}| !k. bin{k}{5} -o ?m. ?{m <= n}. bin{m}{0} * trie{n-m} }

%%% leaf holds no elements
%%% node{n0}{m}{n1} holds an element with multiplicity m and has subtries with
%%% n0 elements (next bit b0) and n1 elements (next bit b1).
%%% Neither leaf nor node carry potential

decl leaf : . |- (t : trie{0})
decl node{n0}{m}{n1} : (l : trie{n0}) (c : ctr{m}) (r : trie{n1}) |- (t : trie{n0+m+n1})

proc t <- leaf <- =
  case t ( ins => {k} <- recv t ;
                  x <- recv t ;
                  case x ( b0 =>
                           {k'} <- recv x ;
                           l <- leaf <- ;
                           c0 <- empty <- ;
                           r <- leaf <- ;
                           l.ins ;
                           send l {k'} ;
                           send l x ;
                           t <- node{1}{0}{0} <- l c0 r
                         | b1 =>
                           {k'} <- recv x ;
                           l <- leaf <- ;
                           c0 <- empty <- ;
                           r <- leaf <- ;
                           r.ins ;
                           send r {k'} ;
                           send r x ;
                           t <- node{0}{0}{1} <- l c0 r
                         | e =>
                           wait x ;
                           l <- leaf <- ;
                           c0 <- empty <- ;
                           c0.inc ;
                           r <- leaf <- ;
                           t <- node{0}{1}{0} <- l c0 r )
         | del => {k} <- recv t ;
                  x <- recv t ;
                  u <- drop{k}{5} <- x ; wait u ;
                  send t {0} ;
                  c0 <- empty <- ;
                  c0.val ;
                  send t c0 ;
                  t <- leaf <-
         )

proc t <- node{n0}{m}{n1} <- l c r =
  case t ( ins => {k} <- recv t ;
                  x <- recv t ;
                  case x ( b0 =>
                           {k'} <- recv x ;
                           l.ins ; send l {k'} ;
                           send l x ;
                           t <- node{n0+1}{m}{n1} <- l c r
                         | b1 =>
                           {k'} <- recv x ;
                           r.ins ; send r {k'} ;
                           send r x ;
                           t <- node{n0}{m}{n1+1} <- l c r
                         | e =>
                           wait x ;
                           c.inc ;
                           t <- node{n0}{m+1}{n1} <- l c r )
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
                            t <- node{n0-m1}{m}{n1} <- l c r
                          | b1 =>
                            {k'} <- recv x ;
                            r.del ;
                            send r {k'} ;
                            send r x ;
                            {m2} <- recv r ;
                            a <- recv r ;
                            send t {m2} ;
                            send t a ;
                            t <- node{n0}{m}{n1-m2} <- l c r
                          | e =>
                            wait x ;
                            send t {m} ;
                            c.val ; 
                            send t c ;
                            c0 <- empty <- ;
                            t <- node{n0}{0}{n1} <- l c0 r
                          )
          )
