#options --syntax=explicit --terminate=equi
#test success

type word{w} = +{ b0 : ?{w > 0}. word{w-1},
                  b1 : ?{w > 0}. word{w-1},
                  e : ?{w = 0}. 1 }

proc zero : . |- word{4}
proc zero = R.b0 ;
            assertR {4 > 0} ;
            R.b0 ;
            assertR {4-1 > 0} ;
            R.b0 ;
            assertR {4-1-1 > 0} ;
            R.b0 ;
            assertR {4-1-1-1 > 0} ;
            R.e ;
            assertR {4-1-1-1-1 = 0} ;
            closeR

proc copy{w} : word{w} |- word{w}
proc copy{w} = caseL ( b0 => assumeL {w > 0} ;
                             R.b0 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | b1 => assumeL {w > 0} ;
                             R.b1 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | e => assumeL {w = 0} ;
                            R.e ;
                            waitL ;
                            assertR {w = 0} ;
                            closeR )

proc succ{w} : word{w} |- word{w}
proc succ{w} = caseL ( b0 => assumeL {w > 0} ;
                             R.b1 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | b1 => assumeL {w > 0} ;
                             R.b0 ;
                             assertR {w > 0} ;
                             succ{w-1}
                     | e => assumeL {w = 0} ;
                            R.e ;
                            waitL ;
                            assertR {w = 0} ;
                            closeR )

proc pred{w} : word{w} |- word{w}
proc pred{w} = caseL ( b0 => assumeL {w > 0} ;
                             R.b1 ;
                             assertR {w > 0} ;
                             pred{w-1}
                     | b1 => assumeL {w > 0} ;
                             R.b0 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | e => assumeL {w = 0} ;
                            R.e ;
                            waitL ;
                            assertR {w = 0} ;
                            closeR )

proc minus_one : . |- word{4}
proc minus_one = zero ||
                 pred{4}
exec minus_one
