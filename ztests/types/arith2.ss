#options --work=none --syntax=explicit
#test success

type bin{n} = +{ eps : ?{_:n = 0}.1,
                 b0 : ?{k:nat}. ?{p:2*k = n}. bin{k},
                 b1 : ?{k:nat}. ?{p:2*k+1 = n}. bin{k} }

proc zero : bin{0}
proc zero = R.eps; assertR {0 = 0}; closeR

proc succ{n} : bin{n} |- bin{n+1}
proc succ{n} =
  caseL ( eps => assumeL {n = 0} ; waitL ;  % . |- bin{1}
                 R.b1 ;                     % . |- ?{k:nat}. ?{p:2*k+1 = 0+1}. bin{k}
                 R.{0} ;                    % . |- ?{p:2*0+1 = 0+1}. bin{0}
                 assertR {2*0+1 = 0+1} ;    % . |- bin{0}
                 R.eps ;                    % . |- ?{p:0 = 0}. 1
                 assertR {0 = 0} ;          % . |- 1
                 closeR
        | b0 => recvL {k}.                  % k:nat; ?{p:2*k = n}. bin{k} |- bin{n+1}
                assumeL {2*k = n} ;         % k:nat, 2*k=n; bin{k} |- bin{n+1}
                R.b1 ;                      % k:nat, 2*k=n; bin{k} |- ?{l:nat}. ?{_:2*l+1 = n+1}. bin{l}
                R.{k} ;                     % k:nat, 2*k=n; bin{k} |- ?{_:2*k+1 = n+1}. bin{k}
                assertR {2*k+1 = n+1} ;     % k:nat, 2*k=n; bin{k} |- bin{k}
                <->
        | b1 => recvL {k}.                  % k:nat; ?{p:2*k+1 = n}. bin{k} |- bin{n+1}
                assumeL {2*k+1 = n} ;       % k:nat, 2*k+1=n; bin{k} |- bin{n+1}
                R.b0 ;                      % k:nat, 2*k+1=n; bin{k} |- ?{l:nat}. ?{_:2*l = n+1}. bin{l}
                R.{k+1} ;                   % k:nat, 2*k+1=n; bin{k} |- ?{_:2*(k+1) = n+1}. bin{k+1}
                assertR {2*(k+1) = n+1} ;   % k:nat, 2*k+1=n; bin{k} |- bin{k+1}
                succ{k} )

