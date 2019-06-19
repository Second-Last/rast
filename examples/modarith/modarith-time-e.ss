#options --time=free --syntax=explicit --terminate=equi
#test success

type word{w} = +{ b0 : ?{w > 0}. ()word{w-1},
                  b1 : ?{w > 0}. ()word{w-1},
                  e : ?{w = 0}. ()1 }

proc zero : . |- word{4}
proc zero = R.b0 ;
            assertR {4 > 0} ;
            delay ;
            R.b0 ;
            assertR {4-1 > 0} ;
            delay ;
            R.b0 ;
            assertR {4-1-1 > 0} ;
            delay ;
            R.b0 ;
            assertR {4-1-1-1 > 0} ;
            delay ;
            R.e ;
            assertR {4-1-1-1-1 = 0} ;
            delay ;
            closeR

proc copy{w} : word{w} |- ()word{w}
proc copy{w} = caseL ( b0 => assumeL {w > 0} ; % ()word{w-1} |- ()word{w}
                             delay ;           %   word{w-1} |- word{w}
                             R.b0 ;            %   word{w-1} |- ?{w > 0}. ()word{w-1}
                             assertR {w > 0} ; %   word{w-1} |- ()word{w-1}
                             copy{w-1}
                     | b1 => assumeL {w > 0} ;
                             delay ;
                             R.b1 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | e => assumeL {w = 0} ;  %         ()1 |- ()word{0}
                            delay ;            %           1 |- word{0}
                            R.e ;              %           1 |- ?{0 = 0}. ()1          
                            waitL ;            %             |- ?{0 = 0}. ()1
                            assertR {w = 0} ;  %             |- ()1
                            delay ;            %             |- 1
                            closeR )

proc succ{w} : word{w} |- ()word{w}
proc succ{w} = caseL ( b0 => assumeL {w > 0} ;
                             delay ;
                             R.b1 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | b1 => assumeL {w > 0} ;
                             delay ;
                             R.b0 ;
                             assertR {w > 0} ;
                             succ{w-1}
                     | e => assumeL {w = 0} ;
                            delay ;
                            R.e ;
                            waitL ;
                            assertR {w = 0} ;
                            delay ;
                            closeR )

proc pred{w} : word{w} |- ()word{w}
proc pred{w} = caseL ( b0 => assumeL {w > 0} ;
                             delay ;
                             R.b1 ;
                             assertR {w > 0} ;
                             pred{w-1}
                     | b1 => assumeL {w > 0} ;
                             delay ;
                             R.b0 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | e => assumeL {w = 0} ;
                            delay ;
                            R.e ;
                            waitL ;
                            assertR {w = 0} ;
                            delay ;
                            closeR )

proc minus_one : . |- ()word{4}
proc minus_one = zero || pred{4}
exec minus_one
