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
  assert x {0 = 0} ;
  close x

proc x <- succ{n} <- y =                         % !n ; y : bin{n} |- x : bin{n+1}
  case y ( b0 =>                              % !n ; y : ?{k}. ?{n = 2*k}. bin{k} |- x : bin{n+1}
                  {k} <- recv y ;             % !n, !k ; y : ?{n = 2*k}. bin{k}   |- x : bin{n+1}
                  assume {n = 2*k} ;          % !n, !k, !{n = 2*k} ; y : bin{k}   |- x : bin{n+1}
                  x.b1 ;                      % !n, !k, !{n = 2*k} ; y : bin{k}   |- x : ?{k'}. ?{n+1 = 2*k'+1}. bin{k'}
                  send x {_k'} ;              % !n, !k, !{n = 2*k}, ?_k' ; y : bin{k} |- x : ?{n+1 = 2*_k'+1}. bin{_k'}
                  assert x {n+1 = 2*_k'+1} ;  % !n, !k, !{n = 2*k}, ?_k', ?{n+1 = 2*_k'+1} ; y : bin{k} |- x : bin{_k'}
                  x <- y                      % !n, !k, !{n = 2*k}, ?_k' |- k = _k'
                  % to prove here:
                  % !n. !k. n = 2*k => ?_k'. n+1 = 2*_k'+2 /\ k = _k'
                  % issue here: forwarding checked with reflexivity?
         | b1 =>                              % !n ; y : ?{k}. ?{n = 2*k+1}. bin{k} |- x : bin{n+1}
                 {k} <- recv y ;              % !n, !k ; ?{n = 2*k+1}. bin{k} |- x : bin{n+1}
                 assume {n = 2*k+1} ;         % !n, !k, !{n = 2*k+1} ; bin{k} |- x : bin{n+1}
                 x.b0 ;                       % !n, !k, !{n = 2*k+1} ; bin{k} |- x : ?{k'}, ?{n+1 = 2*k'}. bin{k'}
                 send x {_k'} ;               % !n, !k, n = 2*k+1, ?_k' ; bin{k} |- x : ?{n+1 = 2*_k'}. bin{_k'}
                 assert x {n+1 = 2*_k'+1} ;   % !n, !k, n = 2*k+1, ?_k', ?{n+1 = 2*_k'} ; bin{k} |- bin{_k'}
                 x <- succ{k} <- y            % !n, !k, n = 2*k+1, ?_k', ?{n+1 = 2*_k'} |- _k' = k+1
                 % to prove here:
                 % !n. !k. n = 2*k+1 => ?_k'. n+1 = 2*_k' /\ _k' = k+1
                 % issue here: to write 'succ{k}' we need '{k} <- recv y'
         | e =>                               % !n ; y : ?{n = 0}. 1 |- x : bin{n+1}
                assume {n = 0} ;              % !n, !{n = 0} ; y : 1 |- x : bin{n+1}
                x.b1 ;                        % !n, !{n = 0} ; y : 1 |- x : ?{k}. ?{n+1 = 2*k+1}. bin{k}
                send x {_k} ;                 % !n, !{n = 0}, ?_k ; y : 1 |- x : ?{n+1 = 2*_k+1}. bin{_k}
                assert x {1 = 2*k+1} ;        % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1} ; y : 1 |- x : bin{_k}
                x.e ;                         % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1} ; y : 1 |- x : ?{_k = 0}. 1
                assert x {_k = 0} ;           % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1}, ?{_k = 0} ; y : 1 |- x : 1
                wait y ;                      % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1}, ?{_k = 0} ; . |- x : 1
                close x                       % !n, !{n = 0}, ?_k, ?{n+1 = 2*_k+1}, ?{_k = 0} ; . |- .
                % to prove here:
                % !n. n = 0 => ?_k. n+1 = 2*_k+1 /\ _k = 0
         )

decl dealloc{n} : (y : bin{n}) |- (u : 1)
proc u <- dealloc{n} <- y =
  case y ( b0 => {k} <- recv y ;
                 assume {n = 2*k} ; 
                 u <- dealloc{k} <- y
         | b1 => {k} <- recv y ;
                 assume {n = 2*k+1} ;
                 u <- dealloc{k} <- y
         | e => assume {n = 0} ;
                wait y ;
                close u )

% t : trie{n}        represents a multiset of n binary numbers
% t.ins(x)       inserts one new copy of x into the trie t
% t.del(x) = c   deletes all copies of x from the tri t, returning the multiplicity of x

type trie{n} = &{ ins : !{k}. bin{k} -o trie{n+1},
                  del : !{k}. bin{k} -o ?{m}. ?{0 <= m /\ m <= n}. bin{m} * trie{n-m} }


decl leaf : . |- (t : trie{0})
decl node{n1}{m}{n2} : (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2})

proc t <- leaf <- =
  case t ( ins => {k} <- recv t ; % !k ; . |- t : bin{k} -o trie{1}
                  x <- recv t ; % !k ; x : bin{k} |- t : trie{1}
                  case x ( b0 => % !k ; x : ?{k'}. ?{k = 2*k'}. x : bin{k'} |- t : trie{1}
                           {k'} <- recv x ;
                           assume {k = 2*k'} ; % !k, !k', !{k = 2*k'} ; x : bin{k'} |- t : trie{1}
                           l <- leaf <- ;
                           z <- zero <- ;
                           r <- leaf <- ; % !k, !k', !{k = 2*k'} ; (x : bin{k'}) (l : trie{0}) (z : bin{0}) (r : trie{0}) |- t : trie{1}
                           l.ins ;        % !k, !k', !{k = 2*k'} ; (x : bin{k'}) (l : !{k}. bin{k} -o trie{1}) (z : bin{0}) (r : trie{0}) |- t : trie{1}
                           send l {k'} ;  % !k, !k', !{k = 2*k'} ; (x : bin{k'}) (l : bin{k'} -o trie{1}) (z : bin{0}) (r : trie{0}) |- t : trie{1}
                           send l x ;     % !k, !k', !{k = 2*k'} ; (l : trie{1}) (z : bin{0}) (r : trie{0}) |- t : trie{1}
                           t <- node{1}{0}{0} <- l z r
                         | b1 => % !k ; x : ?{k'}. ?{k = 2*k'+1}. x : bin{k'} |- t : trie{1}
                           {k'} <- recv x ;
                           assume {k = 2*k'+1} ; % !k, !k', !{k = 2*k'+1} ; x : bin{k'} |- t : trie{1}
                           l <- leaf <- ;
                           z <- zero <- ;
                           r <- leaf <- ; % !k, !k', !{k = 2*k'+1} ; (x : bin{k'}) (l : trie{0}) (z : bin{0}) (r : trie{0}) |- t : trie{1}
                           r.ins ;        % !k, !k', !{k = 2*k'+1} ; (x : bin{k'}) (r : trie{0}) (z : bin{0}) (r : !{k}. bin{k} -o trie{1}) |- t : trie{1}
                           send r {k'} ;  % !k, !k', !{k = 2*k'+1} ; (x : bin{k'}) (r : trie{0}) (z : bin{0}) (r : bin{k'} -o trie{1}) |- t : trie{1}
                           send r x ;     % !k, !k', !{k = 2*k'+1} ; (l : trie{0}) (c : bool{0}) (r : trie{1}) |- t : trie{1}
                           t <- node{0}{0}{1} <- l z r
                         | e => % !k ; x : ?{k = 0}. 1 |- trie{1}
                           assume x {k = 0} ;  % !k, !{k = 0} ; x : 1 |- t : trie{1}
                           wait x ; % !k, !{k = 0} ; . |- t : trie{1}
                           l <- leaf <- ;  % !k, !{k = 0} ; l : trie{0} |- t : trie{1}
                           z <- zero <- ;  % !k, !{k = 0} ; (l : trie{0}) (z : bin{0}) |- t : trie{1}
                           o <- succ <- z ; % !k, !{k = 0} ; (l : trie{0}) (o : bin{1}) |- t : trie{1}
                           r <- leaf <- ;  % !k, !{k = 0} ; (l : trie{0}) (o : bin{1}) (r : trie{0}) |- t : trie{1}
                           t <- node{0}{1}{0} <- l o r )
         | del => {k} <- recv t ;
                  x <- recv t ;
                  u <- dealloc{k} <- x ; wait u ;
                  send t {_m} ;  % !k, !{k = 0}, ?m ; . |- t : ?{0 <= _m /\ _m <= 0}. bin{_m} * trie{0-_m}
                  assert t {0 <= _m /\ _m <= 0} ; % !k, !{k = 0}, ?m, ?{0 <= _m /\ _m <= 0} ; . |- t : bin{_m} * trie{0-_m}
                  z <- zero <- ; % !k, !{k = 0}, ?m, ?{0 <= _m /\ _m <= 0} ; z : bin{0} |- t : bin{_m} * trie{0-_m}
                  send t z ; % !k, !{k = 0}, ?m, ?{0 <= _m /\ _m <= 0}, ?{0 = _m} ; . |- t : trie{0-_m}
                  t <- leaf <- % !k, !{k = 0}, ?m, ?{0 <= _m /\ _m <= 0}, ?{0 = _m}, ?{0-m = 0}
         )

proc t <- node{n1}{m}{n2} <- l c r = % !n1, !m, !n2 ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) (x : bin{k}) |- (t : trie{n1+m+n2})
  case t ( ins => {k} <- recv t ; % !n1, !m, !n2, !k ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) (x : bin{k}) |- (t : bin{k} -o trie{n1+m+n2+1})
                  x <- recv t ;  % !n1, !m, !n2, !k ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) (x : bin{k}) |- (t : trie{n1+m+n2+1})
                  case x ( b0 =>
                           {k'} <- recv x ;
                           assume {k = 2*k'} ; % !n1, !m, !n2, !k, !k', !{k = 2*k'} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2+1})
                           l.ins ; send l {k'}
                           send l x ; % !n1, !m, !n2, !k, !k', !{k = 2*k'} ; (l : trie{n1+1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2+1})
                           t <- node{n1+1}{m}{n2} <- l c r
                         | b1 =>
                           {k'} <- recv x ;
                           assume {k = 2*k'+1} ; % !n1, !m, !n2, !k, !k', !{k = 2*k'+1} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2+1})
                           r.ins ; send r {k'}
                           send r x ; % !n1, !m, !n2, !k, !k', !{k = 2*k'+1} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2+1}) |- (t : trie{n1+m+n2+1})
                           t <- node{n1+1}{m}{n2} <- l c r
                         | e =>
                           assume x {k = 0} ;  % !n1, !m, !n2, !k, !{k = 0} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) (x : 1) |- (t : trie{n1+m+n2+1})
                           wait x ;            % !n1, !m, !n2, !k, !{k = 0} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t : trie{n1+m+n2+1})
                           c' <- succ <- c ;   % !n1, !m, !n2, !k, !{k = 0} ; (l : trie{n1}) (c' : bin{m+1}) (r : trie{n2}) |- (t : trie{n1+m+n2+1})
                           t <- node{n1}{m+1}{n2} <- l c' r )
          | del => {k} <- recv t ;
                   x <- recv t ;
                   case x ( b0 =>
                            {k'} <- recv x ;
                            assume {k = 2*k'} ; % !n1, !m, !n2, !k, !k', !{k = 2*k'} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t :resp{n1+m+n2})
                            l.del ;
                            send l {k'} ;
                            send l x ;
                            {m1} <- recv l ;
                            assume l {0 <= m1 /\ m1 <= n1} ;
                            a <- recv l ; % a : bin{m1}, l : trie{n1-m1}
                            send t {_m1} ; % _m1 = m1
                            assert t {0 <= _m1 /\ _m1 <= n1+m+n2} ;
                            send t a ;
                            t <- node{n1-m1}{m}{n2} <- l c r
                          | b1 =>
                            {k'} <- recv x ;
                            assume {k = 2*k'+1} ; % !n1, !m, !n2, !k, !k', !{k = 2*k'+1} ; (l : trie{n1}) (c : bin{m}) (r : trie{n2}) |- (t :resp{n1+m+n2})
                            r.del ;
                            send r {k'} ;
                            send r x ;
                            {m2} <- recv r ;
                            assume r {0 <= m2 /\ m2 <= n2} ;
                            a <- recv r ; % a : bin{m2}, r : trie{n2-m2}
                            send t {_m2} ; % _m2 = m2
                            assert t {0 <= _m2 /\ _m2 <= n1+m+n2} ;
                            send t a ;
                            t <- node{n1}{m}{n2-_m2} <- l c r
                          | e =>
                            assume {k = 0} ;
                            wait x ;
                            send t {_m} ; % _m = m
                            assert t {0 <= _m /\ _m <= n1+m+n2} ;
                            send t c ;
                            z <- zero <- ;
                            t <- node{n1}{0}{n2} <- l z r
                          )
          )
