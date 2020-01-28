#options --time=free --syntax=explicit --terminate=equi
#test success

(*
 * this is copied from the result of reconstruction
 * consequently, the cost model has been applied
 * and needs to be specified as 'free' here
 *)

type bin{r} = +{ b0 : () ({r}) bin{r},
                 b1 : () ({r}) bin{r},
                 e : () 1 }
type bbool{r} = +{ false : () bin{r},
                   true : () bin{r} }
type tet{s} = +{ b0 : () ({s}) tet{s},
                 b1 : () ({s}) tet{s},
                 b2 : () ({s}) tet{s},
                 b3 : () ({s}) tet{s},
                 e : () 1 }
type bool = +{ false : <>1,
               true : <>1 }
proc zero : . |- bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 3
% calls: 5, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc zero = R.e ;
            delay ;
            closeR
proc ex0 : . |- bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 
% backtracking time reconstruction succeeded
% source expression of size 1
% reconstructed exp of size 3
% calls: 3, backtracked: 1
% after reconstruction with cost model --work=none --time=recv
proc ex0 = zero
% exec ex0
proc copy : bin{1} |- () ({0}) bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 12
% reconstructed exp of size 14
% calls: 26, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc copy = caseL ( b0 => delay ;
                          R.b0 ;
                          delay ;
                          copy ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b1 ;
                          delay ;
                          copy ||
                          delay ;
                          <->
                  | e => delay ;
                         R.e ;
                         waitL ;
                         delay ;
                         closeR )
proc succ : bin{1} |- () ({0}) bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 3 2 3 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 13
% reconstructed exp of size 16
% calls: 30, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc succ = caseL ( b0 => delay ;
                          R.b1 ;
                          delay ;
                          copy ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b0 ;
                          delay ;
                          succ ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b1 ;
                         waitL ;
                         delay{2} ;
                         R.e ;
                         delay ;
                         closeR )
proc ex3 : . |- ({3}) bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 2 1 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 7
% reconstructed exp of size 9
% calls: 48, backtracked: 18
% after reconstruction with cost model --work=none --time=recv
proc ex3 = zero ||
           succ ||
           delay ;
           succ ||
           delay ;
           succ ||
           delay ;
           <->
% exec ex3
proc pred : bin{1} |- () ({0}) bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 12
% reconstructed exp of size 14
% calls: 26, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc pred = caseL ( b0 => delay ;
                          R.b1 ;
                          delay ;
                          pred ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b0 ;
                          delay ;
                          copy ||
                          delay ;
                          <->
                  | e => delay ;
                         R.e ;
                         waitL ;
                         delay ;
                         closeR )
proc ex2 : . |- ({4}) bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 4 1 2 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 4
% calls: 38, backtracked: 16
% after reconstruction with cost model --work=none --time=recv
proc ex2 = ex3 ||
           delay{3} ;
           pred ||
           delay ;
           <->
% exec ex2
proc one : . |- () bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 3
% calls: 11, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc one = zero ||
           succ ||
           delay ;
           <->
proc ex1 : . |- () bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 1
% reconstructed exp of size 3
% calls: 5, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc ex1 = one ||
           delay ;
           <->
% exec ex1
proc numbits : bin{1} |- () <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 2 4 1 1 2 4 6 1 6 1 4 4 6 1 6 1 4 
% backtracking time reconstruction succeeded
% source expression of size 14
% reconstructed exp of size 27
% calls: 53, backtracked: 10
% after reconstruction with cost model --work=none --time=recv
proc numbits = caseL ( b0 => delay{2} ;
                             numbits ||
                             delay ;
                             whenL ;
                             succ ||
                             delay ;
                             nowR ;
                             <->
                     | b1 => delay{2} ;
                             numbits ||
                             delay ;
                             whenL ;
                             succ ||
                             delay ;
                             nowR ;
                             <->
                     | e => delay ;
                            nowR ;
                            R.e ;
                            waitL ;
                            delay ;
                            closeR )
proc ex007 : . |- bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 3 3 3 3 2 
% backtracking time reconstruction succeeded
% source expression of size 7
% reconstructed exp of size 13
% calls: 25, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc ex007 = R.b1 ;
             delay{2} ;
             R.b1 ;
             delay{2} ;
             R.b1 ;
             delay{2} ;
             R.b0 ;
             delay{2} ;
             R.b0 ;
             delay{2} ;
             R.e ;
             delay ;
             closeR
% exec ex007
proc ex5 : . |- () <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 2 1 5 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 7
% calls: 16, backtracked: 5
% after reconstruction with cost model --work=none --time=recv
proc ex5 = ex007 ||
           numbits ||
           delay ;
           whenL ;
           nowR ;
           <->
% exec ex5
proc dbl : bin{1} |- () bin{1}
proc dbl1 : bin{1} |- () bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 12
% reconstructed exp of size 14
% calls: 26, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc dbl = caseL ( b0 => delay ;
                         R.b0 ;
                         delay ;
                         dbl ||
                         delay ;
                         <->
                 | b1 => delay ;
                         R.b0 ;
                         delay ;
                         dbl1 ||
                         delay ;
                         <->
                 | e => delay ;
                        R.e ;
                        waitL ;
                        delay ;
                        closeR )
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 3 2 3 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 13
% reconstructed exp of size 16
% calls: 30, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc dbl1 = caseL ( b0 => delay ;
                          R.b1 ;
                          delay ;
                          dbl ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b1 ;
                          delay ;
                          dbl1 ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b1 ;
                         waitL ;
                         delay{2} ;
                         R.e ;
                         delay ;
                         closeR )
proc stdize : bin{1} |- () <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 2 4 1 1 2 4 6 1 6 1 4 4 6 1 6 1 4 
% backtracking time reconstruction succeeded
% source expression of size 14
% reconstructed exp of size 27
% calls: 53, backtracked: 10
% after reconstruction with cost model --work=none --time=recv
proc stdize = caseL ( b0 => delay{2} ;
                            stdize ||
                            delay ;
                            whenL ;
                            dbl ||
                            delay ;
                            nowR ;
                            <->
                    | b1 => delay{2} ;
                            stdize ||
                            delay ;
                            whenL ;
                            dbl1 ||
                            delay ;
                            nowR ;
                            <->
                    | e => delay ;
                           nowR ;
                           R.e ;
                           waitL ;
                           delay ;
                           closeR )
proc width : bin{1} |- () <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 1 6 1 5 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 8
% calls: 13, backtracked: 3
% after reconstruction with cost model --work=none --time=recv
proc width = stdize ||
             delay ;
             whenL ;
             numbits ||
             delay ;
             whenL ;
             nowR ;
             <->
proc ex3b : . |- <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 4 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 6
% calls: 15, backtracked: 5
% after reconstruction with cost model --work=none --time=recv
proc ex3b = ex007 ||
            width ||
            delay ;
            whenL ;
            nowR ;
            <->
% exec ex3b
proc sq2 : bin{1} |- <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 1 1 2 2 3 1 2 1 3 2 3 1 2 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 16
% reconstructed exp of size 28
% calls: 60, backtracked: 13
% after reconstruction with cost model --work=none --time=recv
proc sq2 = caseL ( b0 => delay{2} ;
                         sq2 ||
                         whenL ;
                         dbl ||
                         delay ;
                         dbl ||
                         delay ;
                         nowR ;
                         <->
                 | b1 => delay{2} ;
                         sq2 ||
                         whenL ;
                         dbl1 ||
                         delay ;
                         nowR ;
                         <->
                 | e => delay ;
                        nowR ;
                        R.e ;
                        waitL ;
                        delay ;
                        closeR )
proc ex64 : . |- <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 5
% reconstructed exp of size 6
% calls: 25, backtracked: 9
% after reconstruction with cost model --work=none --time=recv
proc ex64 = ex007 ||
            succ ||
            delay ;
            sq2 ||
            whenL ;
            nowR ;
            <->
% exec ex64
proc Rb1 : () () bin{1} |- bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 2
% calls: 4, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc Rb1 = R.b1 ;
           delay{2} ;
           <->
proc Re : () 1 |- bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 2
% calls: 4, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc Re = R.e ;
          delay ;
          <->
proc exp2 : bin{1} |- <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 4 3 2 3 2 2 3 1 2 1 2 1 3 2 3 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 17
% reconstructed exp of size 26
% calls: 62, backtracked: 13
% after reconstruction with cost model --work=none --time=recv
proc exp2 = caseL ( b0 => delay{2} ;
                          exp2 ||
                          whenL ;
                          sq2 ||
                          whenL ;
                          nowR ;
                          <->
                  | b1 => delay{2} ;
                          exp2 ||
                          whenL ;
                          sq2 ||
                          whenL ;
                          dbl ||
                          delay ;
                          nowR ;
                          <->
                  | e => delay ;
                         nowR ;
                         R.b1 ;
                         waitL ;
                         delay{2} ;
                         R.e ;
                         delay ;
                         closeR )
proc ex32 : . |- <>bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 1 3 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 5
% calls: 15, backtracked: 5
% after reconstruction with cost model --work=none --time=recv
proc ex32 = ex5 ||
            delay ;
            whenL ;
            exp2 ||
            whenL ;
            nowR ;
            <->
% exec ex32
proc copy2 : bin{1} |- () () bin{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 4
% calls: 8, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc copy2 = copy ||
             delay ;
             copy ||
             delay ;
             <->
proc is_even : bin{1} |- () bbool{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 2 1 2 2 1 1 3 1 2 2 1 1 3 
% backtracking time reconstruction succeeded
% source expression of size 15
% reconstructed exp of size 18
% calls: 33, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc is_even = caseL ( b0 => delay ;
                             R.true ;
                             delay ;
                             R.b0 ;
                             copy2 ||
                             delay{2} ;
                             <->
                     | b1 => delay ;
                             R.false ;
                             delay ;
                             R.b1 ;
                             copy2 ||
                             delay{2} ;
                             <->
                     | e => delay ;
                            R.true ;
                            waitL ;
                            delay ;
                            R.e ;
                            delay ;
                            closeR )
proc not : bbool{1} |- () bbool{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 7
% reconstructed exp of size 7
% calls: 16, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc not = caseL ( false => delay ;
                            R.true ;
                            copy ||
                            delay ;
                            <->
                 | true => delay ;
                           R.false ;
                           copy ||
                           delay ;
                           <-> )
proc exf32 : . |- () () <>bbool{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 3 6 1 5 1 4 
% backtracking time reconstruction succeeded
% source expression of size 5
% reconstructed exp of size 12
% calls: 27, backtracked: 8
% after reconstruction with cost model --work=none --time=recv
proc exf32 = ex32 ||
             whenL ;
             is_even ||
             delay ;
             not ||
             delay ;
             nowR ;
             <->
% exec exf32
proc is_zero : bin{1} |- <>bbool{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 1 1 2 2 1 3 2 1 1 3 2 3 1 2 1 3 1 1 2 1 3 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 21
% reconstructed exp of size 28
% calls: 57, backtracked: 6
% after reconstruction with cost model --work=none --time=recv
proc is_zero = caseL ( b0 => delay{2} ;
                             is_zero ||
                             whenL ;
                             caseL ( false => delay ;
                                              nowR ;
                                              R.false ;
                                              dbl ||
                                              delay ;
                                              <->
                                   | true => delay ;
                                             nowR ;
                                             R.true ;
                                             copy ||
                                             delay ;
                                             <-> )
                     | b1 => delay ;
                             nowR ;
                             R.false ;
                             delay ;
                             R.b1 ;
                             copy2 ||
                             delay{2} ;
                             <->
                     | e => delay ;
                            nowR ;
                            R.true ;
                            waitL ;
                            delay ;
                            R.e ;
                            delay ;
                            closeR )
proc ext32 : . |- <>bbool{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 5
% reconstructed exp of size 11
% calls: 25, backtracked: 8
% after reconstruction with cost model --work=none --time=recv
proc ext32 = ex32 ||
             whenL ;
             is_zero ||
             whenL ;
             not ||
             delay ;
             nowR ;
             <->
% exec ext32
proc ext0 : . |- <>bbool{1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 3 1 3 3 2 
% backtracking time reconstruction succeeded
% source expression of size 7
% reconstructed exp of size 10
% calls: 40, backtracked: 5
% after reconstruction with cost model --work=none --time=recv
proc ext0 = (R.b0 ;
             delay{2} ;
             R.b0 ;
             delay{2} ;
             R.e ;
             delay ;
             closeR)
            [+{b0 : ()()bin{1}, b1 : ()()bin{1}, e : ()1}]
            is_zero ||
            whenL ;
            nowR ;
            <->
% exec ext0
proc copy_tet : tet{3} |- () tet{3}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 
% backtracking time reconstruction succeeded
% source expression of size 18
% reconstructed exp of size 22
% calls: 50, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc copy_tet = caseL ( b0 => delay ;
                              R.b0 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | b1 => delay ;
                              R.b1 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | b2 => delay ;
                              R.b2 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | b3 => delay ;
                              R.b3 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | e => delay ;
                             R.e ;
                             waitL ;
                             delay ;
                             closeR )
proc bin2tet : bin{1} |- ({4}) tet{3}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 7 4 5 2 2 3 3 7 4 5 5 2 2 3 1 1 5 2 3 1 1 5 2 3 3 7 4 5 2 2 3 1 1 5 2 3 1 1 5 
% backtracking time reconstruction succeeded
% source expression of size 33
% reconstructed exp of size 49
% calls: 81, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc bin2tet = caseL ( b0 => delay{2} ;
                             caseL ( b0 => delay{2} ;
                                           R.b0 ;
                                           bin2tet ||
                                           delay{4} ;
                                           <->
                                   | b1 => delay{2} ;
                                           R.b2 ;
                                           bin2tet ||
                                           delay{4} ;
                                           <->
                                   | e => delay ;
                                          waitL ;
                                          delay ;
                                          R.e ;
                                          delay ;
                                          closeR )
                     | b1 => delay{2} ;
                             caseL ( b0 => delay{2} ;
                                           R.b1 ;
                                           bin2tet ||
                                           delay{4} ;
                                           <->
                                   | b1 => delay{2} ;
                                           R.b3 ;
                                           bin2tet ||
                                           delay{4} ;
                                           <->
                                   | e => delay ;
                                          waitL ;
                                          delay ;
                                          R.b1 ;
                                          delay{4} ;
                                          R.e ;
                                          delay ;
                                          closeR )
                     | e => delay ;
                            waitL ;
                            delay{3} ;
                            R.e ;
                            delay ;
                            closeR )
proc ex7t : . |- ({4}) tet{3}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 5 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 3
% calls: 32, backtracked: 10
% after reconstruction with cost model --work=none --time=recv
proc ex7t = ex007 ||
            bin2tet ||
            delay{4} ;
            <->
% exec ex7t
proc succ_tet : tet{3} |- () tet{3}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 7 4 5 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 
% backtracking time reconstruction succeeded
% source expression of size 19
% reconstructed exp of size 24
% calls: 56, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc succ_tet = caseL ( b0 => delay ;
                              R.b1 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | b1 => delay ;
                              R.b2 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | b2 => delay ;
                              R.b3 ;
                              delay{3} ;
                              copy_tet ||
                              delay ;
                              <->
                      | b3 => delay ;
                              R.b0 ;
                              delay{3} ;
                              succ_tet ||
                              delay ;
                              <->
                      | e => delay ;
                             R.b1 ;
                             waitL ;
                             delay{4} ;
                             R.e ;
                             delay ;
                             closeR )
proc checksum : tet{3} |- ({8}) tet{7}
proc checksum_c : tet{3} |- ({8}) tet{7}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 7 15 8 9 2 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 
% backtracking time reconstruction succeeded
% source expression of size 86
% reconstructed exp of size 143
% calls: 301, backtracked: 16
% after reconstruction with cost model --work=none --time=recv
proc checksum = caseL ( b0 => delay{4} ;
                              caseL ( b0 => delay{4} ;
                                            R.b0 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b1 => delay{4} ;
                                            R.b1 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b2 => delay{4} ;
                                            R.b2 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b3 => delay{4} ;
                                            R.b3 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{3} ;
                                           R.b0 ;
                                           delay{8} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | b1 => delay{4} ;
                              caseL ( b0 => delay{4} ;
                                            R.b1 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b1 => delay{4} ;
                                            R.b2 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b2 => delay{4} ;
                                            R.b3 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b3 => delay{4} ;
                                            R.b0 ;
                                            checksum_c ||
                                            delay{8} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{3} ;
                                           R.b1 ;
                                           delay{8} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | b2 => delay{4} ;
                              caseL ( b0 => delay{4} ;
                                            R.b2 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b1 => delay{4} ;
                                            R.b3 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b2 => delay{4} ;
                                            R.b0 ;
                                            checksum_c ||
                                            delay{8} ;
                                            <->
                                    | b3 => delay{4} ;
                                            R.b1 ;
                                            checksum_c ||
                                            delay{8} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{3} ;
                                           R.b2 ;
                                           delay{8} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | b3 => delay{4} ;
                              caseL ( b0 => delay{4} ;
                                            R.b3 ;
                                            checksum ||
                                            delay{8} ;
                                            <->
                                    | b1 => delay{4} ;
                                            R.b0 ;
                                            checksum_c ||
                                            delay{8} ;
                                            <->
                                    | b2 => delay{4} ;
                                            R.b1 ;
                                            checksum_c ||
                                            delay{8} ;
                                            <->
                                    | b3 => delay{4} ;
                                            R.b2 ;
                                            checksum_c ||
                                            delay{8} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{3} ;
                                           R.b3 ;
                                           delay{8} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | e => delay ;
                             waitL ;
                             delay{7} ;
                             R.e ;
                             delay ;
                             closeR )
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 7 15 8 9 2 4 5 7 15 8 9 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 
% backtracking time reconstruction succeeded
% source expression of size 87
% reconstructed exp of size 145
% calls: 311, backtracked: 16
% after reconstruction with cost model --work=none --time=recv
proc checksum_c = caseL ( b0 => delay{4} ;
                                caseL ( b0 => delay{4} ;
                                              R.b1 ;
                                              checksum ||
                                              delay{8} ;
                                              <->
                                      | b1 => delay{4} ;
                                              R.b2 ;
                                              checksum ||
                                              delay{8} ;
                                              <->
                                      | b2 => delay{4} ;
                                              R.b3 ;
                                              checksum ||
                                              delay{8} ;
                                              <->
                                      | b3 => delay{4} ;
                                              R.b0 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{3} ;
                                             R.b1 ;
                                             delay{8} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | b1 => delay{4} ;
                                caseL ( b0 => delay{4} ;
                                              R.b2 ;
                                              checksum ||
                                              delay{8} ;
                                              <->
                                      | b1 => delay{4} ;
                                              R.b3 ;
                                              checksum ||
                                              delay{8} ;
                                              <->
                                      | b2 => delay{4} ;
                                              R.b0 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | b3 => delay{4} ;
                                              R.b1 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{3} ;
                                             R.b2 ;
                                             delay{8} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | b2 => delay{4} ;
                                caseL ( b0 => delay{4} ;
                                              R.b3 ;
                                              checksum ||
                                              delay{8} ;
                                              <->
                                      | b1 => delay{4} ;
                                              R.b0 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | b2 => delay{4} ;
                                              R.b1 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | b3 => delay{4} ;
                                              R.b2 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{3} ;
                                             R.b3 ;
                                             delay{8} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | b3 => delay{4} ;
                                caseL ( b0 => delay{4} ;
                                              R.b0 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | b1 => delay{4} ;
                                              R.b1 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | b2 => delay{4} ;
                                              R.b2 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | b3 => delay{4} ;
                                              R.b3 ;
                                              checksum_c ||
                                              delay{8} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{3} ;
                                             R.b0 ;
                                             delay{8} ;
                                             R.b1 ;
                                             delay{8} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | e => delay ;
                               waitL ;
                               delay{7} ;
                               R.e ;
                               delay ;
                               closeR )
proc ex4t : . |- ({12}) tet{7}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 5 1 9 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 4
% calls: 170, backtracked: 64
% after reconstruction with cost model --work=none --time=recv
proc ex4t = ex7t ||
            delay{4} ;
            checksum ||
            delay{8} ;
            <->
% exec ex4t
proc t4p0 : tet{7} |- () tet{7}
proc t4p1 : tet{7} |- () tet{7}
proc t4p2 : tet{7} |- () tet{7}
proc t4p3 : tet{7} |- () tet{7}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 
% backtracking time reconstruction succeeded
% source expression of size 18
% reconstructed exp of size 22
% calls: 66, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc t4p0 = caseL ( b0 => delay ;
                          R.b0 ;
                          delay{7} ;
                          t4p0 ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b0 ;
                          delay{7} ;
                          t4p1 ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b0 ;
                          delay{7} ;
                          t4p2 ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b0 ;
                          delay{7} ;
                          t4p3 ||
                          delay ;
                          <->
                  | e => delay ;
                         R.e ;
                         waitL ;
                         delay ;
                         closeR )
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 15 8 9 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 
% backtracking time reconstruction succeeded
% source expression of size 19
% reconstructed exp of size 24
% calls: 76, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc t4p1 = caseL ( b0 => delay ;
                          R.b1 ;
                          delay{7} ;
                          t4p0 ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b1 ;
                          delay{7} ;
                          t4p1 ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b1 ;
                          delay{7} ;
                          t4p2 ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b1 ;
                          delay{7} ;
                          t4p3 ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b1 ;
                         waitL ;
                         delay{8} ;
                         R.e ;
                         delay ;
                         closeR )
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 15 8 9 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 
% backtracking time reconstruction succeeded
% source expression of size 19
% reconstructed exp of size 24
% calls: 76, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc t4p2 = caseL ( b0 => delay ;
                          R.b2 ;
                          delay{7} ;
                          t4p0 ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b2 ;
                          delay{7} ;
                          t4p1 ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b2 ;
                          delay{7} ;
                          t4p2 ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b2 ;
                          delay{7} ;
                          t4p3 ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b2 ;
                         waitL ;
                         delay{8} ;
                         R.e ;
                         delay ;
                         closeR )
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 15 8 9 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 
% backtracking time reconstruction succeeded
% source expression of size 19
% reconstructed exp of size 24
% calls: 76, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc t4p3 = caseL ( b0 => delay ;
                          R.b3 ;
                          delay{7} ;
                          t4p0 ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b3 ;
                          delay{7} ;
                          t4p1 ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b3 ;
                          delay{7} ;
                          t4p2 ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b3 ;
                          delay{7} ;
                          t4p3 ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b3 ;
                         waitL ;
                         delay{8} ;
                         R.e ;
                         delay ;
                         closeR )
proc is_tet_digit : tet{7} |- ({16}) +{ false : () () tet{7},
          true : () () tet{7} }
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 15 31 16 17 3 2 8 9 15 31 16 17 3 9 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 15 31 16 17 3 9 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 15 31 16 17 3 9 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 15 31 16 17 3 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 122
% reconstructed exp of size 151
% calls: 463, backtracked: 32
% after reconstruction with cost model --work=none --time=recv
proc is_tet_digit = caseL ( b0 => delay{8} ;
                                  caseL ( b0 => delay{8} ;
                                                R.false ;
                                                t4p0 ||
                                                delay ;
                                                t4p0 ||
                                                delay ;
                                                <->
                                        | b1 => delay{8} ;
                                                R.false ;
                                                t4p1 ||
                                                delay ;
                                                t4p0 ||
                                                delay ;
                                                <->
                                        | b2 => delay{8} ;
                                                R.false ;
                                                t4p2 ||
                                                delay ;
                                                t4p0 ||
                                                delay ;
                                                <->
                                        | b3 => delay{8} ;
                                                R.false ;
                                                t4p3 ||
                                                delay ;
                                                t4p0 ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{7} ;
                                               R.true ;
                                               delay{2} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | b1 => delay{8} ;
                                  caseL ( b0 => delay{8} ;
                                                R.false ;
                                                t4p0 ||
                                                delay ;
                                                t4p1 ||
                                                delay ;
                                                <->
                                        | b1 => delay{8} ;
                                                R.false ;
                                                t4p1 ||
                                                delay ;
                                                t4p1 ||
                                                delay ;
                                                <->
                                        | b2 => delay{8} ;
                                                R.false ;
                                                t4p2 ||
                                                delay ;
                                                t4p1 ||
                                                delay ;
                                                <->
                                        | b3 => delay{8} ;
                                                R.false ;
                                                t4p3 ||
                                                delay ;
                                                t4p1 ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{7} ;
                                               R.true ;
                                               delay{2} ;
                                               R.b1 ;
                                               delay{8} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | b2 => delay{8} ;
                                  caseL ( b0 => delay{8} ;
                                                R.false ;
                                                t4p0 ||
                                                delay ;
                                                t4p2 ||
                                                delay ;
                                                <->
                                        | b1 => delay{8} ;
                                                R.false ;
                                                t4p1 ||
                                                delay ;
                                                t4p2 ||
                                                delay ;
                                                <->
                                        | b2 => delay{8} ;
                                                R.false ;
                                                t4p2 ||
                                                delay ;
                                                t4p2 ||
                                                delay ;
                                                <->
                                        | b3 => delay{8} ;
                                                R.false ;
                                                t4p3 ||
                                                delay ;
                                                t4p2 ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{7} ;
                                               R.true ;
                                               delay{2} ;
                                               R.b2 ;
                                               delay{8} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | b3 => delay{8} ;
                                  caseL ( b0 => delay{8} ;
                                                R.false ;
                                                t4p0 ||
                                                delay ;
                                                t4p3 ||
                                                delay ;
                                                <->
                                        | b1 => delay{8} ;
                                                R.false ;
                                                t4p1 ||
                                                delay ;
                                                t4p3 ||
                                                delay ;
                                                <->
                                        | b2 => delay{8} ;
                                                R.false ;
                                                t4p2 ||
                                                delay ;
                                                t4p3 ||
                                                delay ;
                                                <->
                                        | b3 => delay{8} ;
                                                R.false ;
                                                t4p3 ||
                                                delay ;
                                                t4p3 ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{7} ;
                                               R.true ;
                                               delay{2} ;
                                               R.b3 ;
                                               delay{8} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | e => delay ;
                                 waitL ;
                                 delay{15} ;
                                 R.true ;
                                 delay{2} ;
                                 R.e ;
                                 delay ;
                                 closeR )
proc consume_tet : tet{7} |- <>1
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 2 8 9 1 3 8 9 1 3 8 9 1 3 8 9 1 3 
% backtracking time reconstruction succeeded
% source expression of size 13
% reconstructed exp of size 14
% calls: 69, backtracked: 8
% after reconstruction with cost model --work=none --time=recv
proc consume_tet = caseL ( b0 => delay{8} ;
                                 consume_tet ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | b1 => delay{8} ;
                                 consume_tet ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | b2 => delay{8} ;
                                 consume_tet ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | b3 => delay{8} ;
                                 consume_tet ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | e => delay ;
                                waitL ;
                                delay ;
                                nowR ;
                                closeR )
exec ex0
exec ex3
exec ex2
exec ex1
exec ex007
exec ex5
exec ex3b
exec ex64
exec ex32
exec exf32
exec ext32
exec ext0
exec ex7t
exec ex4t

