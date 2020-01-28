#options --syntax=explicit --terminate=equi
#test success

type nat{n} = +{zero : ?{n = 0}. 1,
                succ : ?{n > 0}. nat{n-1}}

type plus{x}{y}{z} = +{plus0 : ?{x = 0}. ?{y = z}. 1,
                       pluss : ?{x > 0}. ?{z > 0}. plus{x-1}{y}{z-1}}

proc thm{n} : nat{n} |- plus{n}{0}{n}
proc thm{n} =
   caseL ( zero => assumeL{n = 0} ; waitL ;
                   R.plus0 ; assertR{n = 0} ; assertR{0 = 0};
                   closeR
         | succ => assumeL{n > 0} ;   % nat{n-1} |- plus{n}{0}{n}
                   R.pluss ; assertR{n > 0} ; assertR{n > 0} ;
                   thm{n-1} )
