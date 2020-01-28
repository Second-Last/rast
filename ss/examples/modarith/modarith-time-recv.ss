#options --time=recv --syntax=explicit --terminate=equi
#test success

(*
type word{w} = +{ b0 : ?{w > 0}. ()word{w-1},
                  b1 : ?{w > 0}. ()word{w-1},
                  e : ?{w = 0}. ()1 }
*)

type word1{w} = +{ b0 : () ?{w > 0}. word1{w-1},
                   b1 : () ?{w > 0}. word1{w-1},
                    e : () ?{w = 0}. 1 }

type word2{w} = +{ b0 : ?{w > 0}. ()word2{w-1},
                   b1 : ?{w > 0}. ()word2{w-1},
                    e : ?{w = 0}. ()1 }

proc zero : . |- word1{4}
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

proc copy{w} : word1{w} |- ()word2{w}
proc copy{w} = caseL ( b0 => assumeL {w > 0} ; %   word1{w-1} |- word2{w}
                             R.b0 ;            %   word1{w-1} |- ?{w > 0}. ()word2{w-1}
                             assertR {w > 0} ; %   word1{w-1} |- ()word2{w-1}
                             copy{w-1}
                     | b1 => assumeL {w > 0} ;
                             R.b1 ;
                             assertR {w > 0} ;
                             copy{w-1}
                     | e => assumeL {w = 0} ;  %           1 |- word{0}
                            R.e ;              %           1 |- ?{0 = 0}. ()1          
                            assertR {w = 0} ;  %             |- ()1
                            waitL ;            %             |- 1
                            closeR )

proc succ{w} : word1{w} |- ()word2{w}
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
                            assertR {w = 0} ;
                            waitL ;
                            closeR )

proc pred{w} : word1{w} |- ()word2{w}
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
                            assertR {w = 0} ;
                            waitL ;
                            closeR )

proc minus_one : . |- ()word2{4}
proc minus_one = zero || pred{4}
exec minus_one
