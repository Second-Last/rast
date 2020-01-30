#test success
#options --syntax=implicit --work=send

%%% Orders, to verify comparisons
type ord{m}{n} = +{ lt : ?{m < n}. 1,
                    eq : ?{m = n}. 1,
                    gt : ?{m > n}. 1 }

%%% Unary natural numbers
%%% Indexed by their value
type nat{n}{p} = +{ zero : ?{n = 0}. |{p}> 1,
                    succ : ?{n > 0}. |{p}> nat{n-1}{p} }

decl zero_nat{p} : . |{p+2}- (x : nat{0}{p})
proc x <- zero_nat{p} = x.zero ; close x

decl succ_nat{n}{p} : (y : nat{n}{p}) |{p+1}- (x : nat{n+1}{p})
proc x <- succ_nat{n}{p} y = x.succ ; x <-> y

decl pred_nat{n|n > 0}{p} : (y : nat{n}{p}) |- (x : nat{n-1}{p})
proc x <- pred_nat{n}{p} y = case y ( succ => x <-> y )

decl plus_nat{m}{n}{p} : (y : nat{m}{p+1}) (z : nat{n}{p}) |- (x : nat{n+m}{p})
proc x <- plus_nat{m}{n}{p} y z =
  case y ( zero => wait y ; x <-> z
         | succ => x.succ ;
                   x <- plus_nat{m-1}{n}{p} y z )

decl drop_nat{n}{p} : (x : nat{n}{p}) |{1}- (u : 1)
decl dup_nat{n}{p} : (x : nat{n}{2*p+5}) |{3}- (xx : nat{n}{p} * nat{n}{p} * 1)

proc u <- drop_nat{n}{p} x =
  case x ( zero => wait x ; close u 
         | succ => u <- drop_nat{n-1}{p} x )

proc xx <- dup_nat{n}{p} x =
  case x ( zero => wait x ;
                   x1 <- zero_nat{p} ; send xx x1 ;
                   x2 <- zero_nat{p} ; send xx x2 ;
                   close xx
         | succ => yy <- dup_nat{n-1}{p} x ;
                   x <- recv yy ; y <- recv yy ; wait yy ;
                   x1 <- succ_nat{n-1}{p} x ; send xx x1 ;
                   x2 <- succ_nat{n-1}{p} y ; send xx x2 ;
                   close xx )

%%% Comparison, this time requires ord{m+1}{n+1} = ord{m}{n}
decl compare_nat{m}{n}{p} : (x : nat{m}{p}) (y : nat{n}{p}) |{3}- (o : ord{m}{n})
proc o <- compare_nat{m}{n}{p} x y =
  case x ( zero => case y ( zero => o.eq ; wait x ; wait y ;
                                    close o
                          | succ => o.lt ; wait x ;
                                    u <- drop_nat{n-1}{p} y ; wait u ;
                                    close o )
         | succ => case y ( zero => o.gt ; wait y ;
                                    u <- drop_nat{m-1}{p} x ; wait u ;
                                    close o
                          | succ => o <- compare_nat{m-1}{n-1}{p} x y ) )

decl double_nat{n}{p} : (y : nat{n}{2*p+2}) |{p+2}- (x : nat{2*n}{p})
proc x <- double_nat{n}{p} y =
  case y ( zero => wait y ; x <- zero_nat{p}
         | succ => z <- double_nat{n-1}{p} y ;
                   z' <- succ_nat{2*n-2}{p} z ;
                   x <- succ_nat{2*n-1}{p} z' )

