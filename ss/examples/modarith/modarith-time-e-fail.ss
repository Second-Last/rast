#options --time=free --syntax=explicit --terminate=equi
#test error

type word{w} = +{ b0 : () ?{w > 0}. word{w-1},
                  b1 : () ?{w > 0}. word{w-1},
                  e :  () ?{w = 0}. 1 }

proc zero : . |- word{4}
proc zero = R.b0 ;
            delay ;
            assertR {4 > 0} ;
            R.b0 ;
            delay ;
            assertR {4-1 > 0} ;
            R.b0 ;
            delay ;
            assertR {4-1-1 > 0} ;
            R.b0 ;
            delay ;
            assertR {4-1-1-1 > 0} ;
            R.e ;
            delay ;
            assertR {4-1-1-1-1 = 0} ;
            closeR

proc copy{w} : word{w} |- ()word{w}
proc copy{w} = caseL ( b0 => delay ;           % ?{w > 0}. word{w-1} |- word{w}
                             assumeL {w > 0} ; %           word{w-1} |- word{w}
                             R.b0 ;            %           word{w-1} |- () ?{w > 0}. word{w-1}
                             assertR {w > 0} ; % stuck here: cannot call, assert, or delay
                             copy{w-1}
                     | b1 => delay ;
                             assumeL {w > 0} ;
                             R.b1 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | e => delay ;            % ?{w = 0}. 1 |- word{w}
                            assumeL {w = 0} ;  %           1 |- word{0}
                            R.e ;              %           1 |- ()?{0 = 0}. 1          
                            waitL ;            %             |- ()?{0 = 0}. 1
                            delay ;            %             |- ?{0 = 0}. 1
                            assertR {w = 0} ;  %             |- 1
                            closeR )
