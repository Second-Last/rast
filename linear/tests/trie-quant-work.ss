% bin{n} = binary numbers of value n
% leading 0s are allowed here, but could be
% eliminated with b0 : ?{k}. ?{n > 0 & n = 2*k}. bin{k}
%
type bin{n} = +{ b0 : ?{k | n = 2*k}. bin{k},
                 b1 : ?{k | n = 2*k+1}. bin{k},
                 e : ?{n = 0}. 1 }

decl zero : . |- (x : bin{0})
decl succ{n} : (y : bin{n}) |- (x : bin{n+1})

proc x <- zero <- =
  x.e ;
  close x

proc x <- succ{n} <- y =
  case y ( b0 =>  {k} <- recv y ;             % !n, !k ; y : ?{n = 2*k}. bin{k}   |- x : bin{n+1}
                  x.b1 ;                      % !n, !k, !{n = 2*k} ; y : bin{k}   |- x : ?{k'}. ?{n+1 = 2*k'+1}. bin{k'}
                  send x {k} ;                % k' = k
                  x <- y                      % !n, !k, !{n = 2*k}, ?_k' |- k = _k'
         | b1 =>                              % !n ; y : ?{k}. ?{n = 2*k+1}. bin{k} |- x : bin{n+1}
                 {k} <- recv y ;              % !n, !k ; ?{n = 2*k+1}. bin{k} |- x : bin{n+1}
                 x.b0 ;                       % !n, !k, !{n = 2*k+1} ; bin{k} |- x : ?{k'}, ?{n+1 = 2*k'}. bin{k'}
                 send x {k+1} ;               % k' = k+1
                 x <- succ{k} <- y            % !n, !k, n = 2*k+1, ?_k', ?{n+1 = 2*_k'} |- _k' = k+1
         | e =>                               % !n ; y : ?{n = 0}. 1 |- x : bin{n+1}
                x.b1 ;                        % !n, !{n = 0} ; y : 1 |- x : ?{k}. ?{n+1 = 2*k+1}. bin{k}
                send x {0} ;                  % k' = 0
                x.e ;                         % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1} ; y : 1 |- x : ?{_k = 0}. 1
                wait y ;                      % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1}, ?{_k = 0} ; . |- x : 1
                close x                       % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1}, ?{_k = 0} ; . |- .
         )

decl dealloc{n} : (y : bin{n}) |- (u : 1)
proc u <- dealloc{n} <- y =
  case y ( b0 => {k} <- recv y ;
                 u <- dealloc{k} <- y
         | b1 => {k} <- recv y ;
                 u <- dealloc{k} <- y
         | e => wait y ;
                close u )

type bits{w} : +{ b0 : ?{w > 0}. bits{w-1},
                  b1 : ?{w > 0}. bits{w-1},
                  e : ?{w = 0}. 1 }

% t : trie{n}        represents a multiset of n binary numbers
% t.ins(x)       inserts one new copy of x into the trie t
% t.del(x) = c   deletes all copies of x from the tri t, returning the multiplicity of x

type trie{n} = &{ ins : !{w}. bits{w} -o trie{n+1},
                  del : !{w}. bits{w} -o ?{m | 0 <= m /\ m <= n}. bin{m} * trie{n-m} }


decl leaf : . |- (t : trie{0})
decl node{n1}{m}{n2} : (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2})

proc t <- leaf <- =
  case t ( ins => {w} <- recv t ;
                  x <- recv t ;
                  case x ( b0 =>
                           l <- leaf <- ;
                           z <- zero <- ;
                           r <- leaf <- ;
                           l.ins ;
                           send l {w-1} ;
                           send l x ;
                           t <- node{1}{0}{0} <- l z r
                         | b1 =>
                           l <- leaf <- ;
                           z <- zero <- ;
                           r <- leaf <- ;
                           r.ins ;
                           send r {w-1} ;
                           send r x ;
                           t <- node{0}{0}{1} <- l z r
                         | e =>
                           wait x ;
                           l <- leaf <- ;
                           z <- zero <- ;
                           o <- succ <- z ;
                           r <- leaf <- ;
                           t <- node{0}{1}{0} <- l o r )
         | del => {w} <- recv t ;
                  x <- recv t ;
                  u <- dealloc{w} <- x ; wait u ;
                  send t {0} ;
                  z <- zero <- ;
                  send t z ;
                  t <- leaf <-
         )

proc t <- node{n1}{m}{n2} <- l c r =
  case t ( ins => {w} <- recv t ;
                  x <- recv t ;
                  case x ( b0 =>
                           l.ins ; send l {w-1}
                           send l x ;
                           t <- node{n1+1}{m}{n2} <- l c r
                         | b1 =>
                           r.ins ; send r {w-1}
                           send r x ;
                           t <- node{n1+1}{m}{n2} <- l c r
                         | e =>
                           wait x ;
                           c' <- succ <- c ;
                           t <- node{n1}{m+1}{n2} <- l c' r )
          | del => {w} <- recv t ;
                   x <- recv t ;
                   case x ( b0 =>
                            l.del ;
                            send l {w-1} ;
                            send l x ;
                            {m1} <- recv l ;
                            a <- recv l ;
                            send t {m1} ;
                            send t a ;
                            t <- node{n1-m1}{m}{n2} <- l c r
                          | b1 =>
                            r.del ;
                            send r {w-1} ;
                            send r x ;
                            {m2} <- recv r ;
                            a <- recv r ;
                            send t {m2} ; 
                            send t a ;
                            t <- node{n1-m1}{m}{n2} <- l c r
                          | e =>
                            wait x ;
                            send t {m} ;
                            send t c ;
                            z <- zero <- ;
                            t <- node{n1}{0}{n2} <- l z r
                          )
          )
