#options --time=free --syntax=explicit
#test success

(*
 * this is copied from the result of reconstruction
 * consequently, the cost model has been applied
 * and needs to be specified as 'free' here
 *)

(* 
 * this is the generalized version, parameterized
 * over rates as much as possible.  By hand.
 *)

type bin{r} = +{ b0 : ({r+1}) bin{r},
                 b1 : ({r+1}) bin{r},
                 e : () 1 }
type bbool{r} = +{ false : () bin{r},
                   true : () bin{r} }
type tet{s} = +{ b0 : ({s+1}) tet{s},
                 b1 : ({s+1}) tet{s},
                 b2 : ({s+1}) tet{s},
                 b3 : ({s+1}) tet{s},
                 e : () 1 }
type bool = +{ false : <>1,
               true : <>1 }

proc zero{r} : . |- bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 3
% calls: 5, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc zero{r} = R.e ;
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
proc ex0 = zero{1}
exec ex0

proc copy{r} : bin{r} |- () bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 12
% reconstructed exp of size 14
% calls: 26, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc copy{r} = caseL ( b0 => delay ;  % (r)bin{r} |- bin{r}
                       R.b0 ;         % (r)bin{r} |- (r+1)bin{r}
                       delay{r} ;     % bin{r} |- ()bin{r}
                       copy{r} ||     % bin{r} |- ()bin{r} || ()bin{r} |- ()bin{r}
                       delay ;
                       <->
                     | b1 => delay ;
                       R.b1 ;
                       delay{r} ;
                       copy{r} ||
                       delay ;
                       <->
                  | e => delay ;
                       R.e ;
                       waitL ;
                       delay ;
                       closeR )

proc succ{r} : bin{r} |- () bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 3 2 3 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 13
% reconstructed exp of size 16
% calls: 30, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc succ{r} = caseL ( b0 => delay ;
                          R.b1 ;
                          delay{r} ;
                          copy{r}
                  | b1 => delay ;
                          R.b0 ;
                          delay{r} ;
                          succ{r}
                  | e => delay ;
                         R.b1 ;
                         waitL ;
                         delay ;
                         delay{r} ;
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
proc ex3 = zero{1} ||
           succ{1} ||
           delay ;
           succ{1} ||
           delay ;
           succ{1} ||
           delay ;
           <->
exec ex3

proc pred{r} : bin{r} |- () bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 12
% reconstructed exp of size 14
% calls: 26, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc pred{r} = caseL ( b0 => delay ;
                          R.b1 ;
                          delay{r} ;
                          pred{r}
                  | b1 => delay ;
                          R.b0 ;
                          delay{r} ;
                          copy{r}
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
           pred{1} ||
           delay ;
           <->
exec ex2

proc one{r} : . |- () bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 3
% calls: 11, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc one{r} = zero{r} ||
           succ{r} ||
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
proc ex1 = one{1} ||
           delay ;
           <->
exec ex1

proc numbits{r} : bin{r} |- () <>bin{r}

% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 2 4 1 1 2 4 6 1 6 1 4 4 6 1 6 1 4 
% backtracking time reconstruction succeeded
% source expression of size 14
% reconstructed exp of size 27
% calls: 53, backtracked: 10
% after reconstruction with cost model --work=none --time=recv
proc numbits{r} = caseL ( b0 => delay ;
                             delay{r} ;
                             numbits{r} ||
                             delay ;
                             whenL ;
                             succ{r} ||
                             delay ;
                             nowR ;
                             <->
                     | b1 => delay ; delay{r} ;
                             numbits{r} ||
                             delay ;
                             whenL ;
                             succ{r} ||
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
exec ex007

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
           numbits{1} ||
           delay ;
           whenL ;
           nowR ;
           <->
exec ex5

proc dbl{r} : bin{r} |- () bin{r}
proc dbl1{r} : bin{r} |- () bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 2 1 2 1 2 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 12
% reconstructed exp of size 14
% calls: 26, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc dbl{r} = caseL ( b0 => delay ;
                         R.b0 ;
                         delay{r} ;
                         dbl{r} ||
                         delay ;
                         <->
                 | b1 => delay ;
                         R.b0 ;
                         delay{r} ;
                         dbl1{r} ||
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
proc dbl1{r} = caseL ( b0 => delay ;
                          R.b1 ;
                          delay{r} ;
                          dbl{r}
                  | b1 => delay ;
                          R.b1 ;
                          delay{r} ;
                          dbl1{r}
                  | e => delay ;
                         R.b1 ;
                         waitL ;
                         delay ;
                         delay{r} ;
                         R.e ;
                         delay ;
                         closeR )

proc stdize{r} : bin{r} |- () <>bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 2 4 1 1 2 4 6 1 6 1 4 4 6 1 6 1 4 
% backtracking time reconstruction succeeded
% source expression of size 14
% reconstructed exp of size 27
% calls: 53, backtracked: 10
% after reconstruction with cost model --work=none --time=recv
proc stdize{r} = caseL ( b0 => delay ; delay{r} ;
                            stdize{r} ||
                            delay ;
                            whenL ;
                            dbl{r} ||
                            delay ;
                            nowR ;
                            <->
                    | b1 => delay ; delay{r} ;
                            stdize{r} ||
                            delay ;
                            whenL ;
                            dbl1{r} ||
                            delay ;
                            nowR ;
                            <->
                    | e => delay ;
                           nowR ;
                           R.e ;
                           waitL ;
                           delay ;
                           closeR )

proc width{r} : bin{r} |- () <>bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 2 1 6 1 5 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 8
% calls: 13, backtracked: 3
% after reconstruction with cost model --work=none --time=recv
proc width{r} = stdize{r} ||
             delay ;
             whenL ;
             numbits{r} ||
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
            width{1} ||
            delay ;
            whenL ;
            nowR ;
            <->
exec ex3b

proc sq2{r} : bin{r} |- <>bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 1 1 2 2 3 1 2 1 3 2 3 1 2 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 16
% reconstructed exp of size 28
% calls: 60, backtracked: 13
% after reconstruction with cost model --work=none --time=recv
proc sq2{r} = caseL ( b0 => delay ; delay{r} ;
                         sq2{r} ||
                         whenL ;
                         dbl{r} ||
                         delay ;
                         dbl{r} ||
                         delay ;
                         nowR ;
                         <->
                 | b1 => delay ; delay{r} ;
                         sq2{r} ||
                         whenL ;
                         dbl1{r} ||
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
            succ{1} ||
            delay ;
            sq2{1} ||
            whenL ;
            nowR ;
            <->
exec ex64

proc Rb0{r} : ({r+1})bin{r} |- bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 2
% calls: 4, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc Rb0{r} = R.b0 ; delay ; delay{r} ; <->

proc Rb1{r} : ({r+1})bin{r} |- bin{r}

% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 2
% calls: 4, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc Rb1{r} = R.b1 ; delay ; delay{r} ; <->

proc Re{r} : ()1 |- bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 2
% reconstructed exp of size 2
% calls: 4, backtracked: 0
% after reconstruction with cost model --work=none --time=recv
proc Re{r} = R.e ; delay ; <->

proc exp2{r} : bin{r} |- <>bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 4 3 2 3 2 2 3 1 2 1 2 1 3 2 3 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 17
% reconstructed exp of size 26
% calls: 62, backtracked: 13
% after reconstruction with cost model --work=none --time=recv
proc exp2{r} = caseL ( b0 => delay ; delay{r} ;
                          exp2{r} ||
                          whenL ;
                          sq2{r} ||
                          whenL ;
                          nowR ;
                          <->
                  | b1 => delay ; delay{r} ;
                          exp2{r} ||
                          whenL ;
                          sq2{r} ||
                          whenL ;
                          dbl{r} ||
                          delay ;
                          nowR ;
                          <->
                  | e => delay ;
                         nowR ;
                         R.b1 ;
                         waitL ;
                         delay ; delay{r} ;
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
            exp2{1} ||
            whenL ;
            nowR ;
            <->
exec ex32

% TODO: fix this with ()()bin{r} instead of ({2}) bin{r}
proc copy2{r} : bin{r} |- ({2}) bin{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 3
% reconstructed exp of size 4
% calls: 8, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc copy2{r} = copy{r} ||
             delay ;
             copy{r} ||
             delay ;
             <->

proc is_even{p} : bin{p+1} |- () bbool{p+1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 2 1 2 2 1 1 3 1 2 2 1 1 3 
% backtracking time reconstruction succeeded
% source expression of size 15
% reconstructed exp of size 18
% calls: 33, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc is_even{p} = caseL ( b0 => delay ;  % (p+1) bin{p+1} |- bool{p+1}
                             R.true ;    % (p+1) bin{p+1} |- (1) bin{p+1}
                             delay{1} ;  % (p) bin{p+1} |- bin{p+1}
                             R.b0 ;      % (p) bin{p+1} |- (p+2)bin{p+1}
                             delay{p} ;  % bin{p+1} |- (2)bin{p+1}
                             copy2{p+1}
                     | b1 => delay ;
                             R.false ;
                             delay{1} ;
                             R.b1 ;
                             delay{p} ;
                             copy2{p+1}
                     | e => delay ;
                            R.true ;
                            waitL ;
                            delay ;
                            R.e ;
                            delay ;
                            closeR )

proc not{r} : bbool{r} |- () bbool{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 7
% reconstructed exp of size 7
% calls: 16, backtracked: 2
% after reconstruction with cost model --work=none --time=recv
proc not{r} = caseL ( false => delay ;
                            R.true ;
                            copy{r} ||
                            delay ;
                            <->
                 | true => delay ;
                           R.false ;
                           copy{r} ||
                           delay ;
                           <-> )

proc ex8 : bin{2}
proc ex8 = R.b0 ; delay{3} ; R.b0 ; delay{3} ; R.b0 ; delay{3} ; R.b1 ; delay{3} ; R.e ; delay ; closeR

proc exf8 : . |- ()()<>bbool{2}

% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 3 6 1 5 1 4 
% backtracking time reconstruction succeeded
% source expression of size 5
% reconstructed exp of size 12
% calls: 27, backtracked: 8
% after reconstruction with cost model --work=none --time=recv
proc exf8 = ex8 ||
             is_even{1} ||
             delay ;
             not{2} ||
             delay ;
             nowR ;
             <->
exec exf8

proc is_zero{p} : bin{p+1} |- <>bbool{p+1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 1 1 2 2 1 3 2 1 1 3 2 3 1 2 1 3 1 1 2 1 3 1 1 2 
% backtracking time reconstruction succeeded
% source expression of size 21
% reconstructed exp of size 28
% calls: 57, backtracked: 6
% after reconstruction with cost model --work=none --time=recv
proc is_zero{p} = caseL ( b0 => delay ; delay{p+1} ;
                             is_zero{p} ||
                             whenL ;
                             caseL ( false => delay ;
                                              nowR ;
                                              R.false ;
                                              dbl{p+1} ||
                                              delay ;
                                              <->
                                   | true => delay ;
                                             nowR ;
                                             R.true ;
                                             copy{p+1} ||
                                             delay ;
                                             <-> )
                     | b1 => delay ;
                             nowR ;
                             R.false ;
                             delay ;
                             R.b1 ;
                             delay{p} ;
                             copy2{p+1}
                     | e => delay ;
                            nowR ;
                            R.true ;
                            waitL ;
                            delay ;
                            R.e ;
                            delay ;
                            closeR )


proc ext8 : . |- <>bbool{2}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 2 1 2 1 3 
% backtracking time reconstruction succeeded
% source expression of size 5
% reconstructed exp of size 11
% calls: 25, backtracked: 8
% after reconstruction with cost model --work=none --time=recv
proc ext8 = ex8 ||
             is_zero{1} ||
             whenL ;
             not{2} ||
             delay ;
             nowR ;
             <->
exec ext8

proc ext0 : . |- <>bbool{2}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 1 3 1 3 3 2 
% backtracking time reconstruction succeeded
% source expression of size 7
% reconstructed exp of size 10
% calls: 40, backtracked: 5
% after reconstruction with cost model --work=none --time=recv
proc ext0 = (R.b0 ;
             delay{3} ;
             R.b0 ;
             delay{3} ;
             R.e ;
             delay ;
             closeR)
            [bin{2}]
            is_zero{1} ||
            whenL ;
            nowR ;
            <->
exec ext0

proc copy_tet{r} : tet{r} |- ()tet{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 
% backtracking time reconstruction succeeded
% source expression of size 18
% reconstructed exp of size 22
% calls: 50, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc copy_tet{r} = caseL ( b0 => delay ;
                              R.b0 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | b1 => delay ;
                              R.b1 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | b2 => delay ;
                              R.b2 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | b3 => delay ;
                              R.b3 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | e => delay ;
                             R.e ;
                             waitL ;
                             delay ;
                             closeR )

proc bin2tet{r} : bin{r} |- ({2*r+2}) tet{2*r+1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 3 7 4 5 2 2 3 3 7 4 5 5 2 2 3 1 1 5 2 3 1 1 5 2 3 3 7 4 5 2 2 3 1 1 5 2 3 1 1 5 
% backtracking time reconstruction succeeded
% source expression of size 33
% reconstructed exp of size 49
% calls: 81, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc bin2tet{r} = caseL ( b0 => delay{r+1} ;
                             caseL ( b0 => delay{r+1} ;
                                           R.b0 ;
                                           bin2tet{r} ||
                                           delay{2*r+2} ;
                                           <->
                                   | b1 => delay{r+1} ;
                                           R.b2 ;
                                           bin2tet{r} ||
                                           delay{2*r+1} ;
                                           <->
                                   | e => delay ;
                                          waitL ;
                                          delay{r} ;
                                          R.e ;
                                          delay ;
                                          closeR )
                     | b1 => delay{r+1} ;
                             caseL ( b0 => delay{r+1} ;
                                           R.b1 ;
                                           bin2tet{r} ||
                                           delay{2*r+1} ;
                                           <->
                                   | b1 => delay{r+1} ;
                                           R.b3 ;
                                           bin2tet{r} ||
                                           delay{2*r+1} ;
                                           <->
                                   | e => delay ;
                                          waitL ;
                                          delay{r} ;
                                          R.b1 ;
                                          delay{2*r+2} ;
                                          R.e ;
                                          delay ;
                                          closeR )
                     | e => delay ;
                            waitL ;
                            delay{2*r+1} ;
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
            bin2tet{1} ||
            delay{4} ;
            <->
exec ex7t

proc succ_tet{r} : tet{r} |- () tet{r}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 3 7 4 5 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 1 2 4 1 2 
% backtracking time reconstruction succeeded
% source expression of size 19
% reconstructed exp of size 24
% calls: 56, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc succ_tet{r} = caseL ( b0 => delay ;
                              R.b1 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | b1 => delay ;
                              R.b2 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | b2 => delay ;
                              R.b3 ;
                              delay{r} ;
                              copy_tet{r} ||
                              delay ;
                              <->
                      | b3 => delay ;
                              R.b0 ;
                              delay{r} ;
                              succ_tet{r} ||
                              delay ;
                              <->
                      | e => delay ;
                             R.b1 ;
                             waitL ;
                             delay ;
                             delay{r} ;
                             R.e ;
                             delay ;
                             closeR )

proc checksum{r} : tet{r} |- ({2*r+2}) tet{2*r+1}
proc checksum_c{r} : tet{r} |- ({2*r+2}) tet{2*r+1}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 7 15 8 9 2 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 7 15 8 9 9 2 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 4 5 1 1 9 
% backtracking time reconstruction succeeded
% source expression of size 86
% reconstructed exp of size 143
% calls: 301, backtracked: 16
% after reconstruction with cost model --work=none --time=recv
proc checksum{r} = caseL ( b0 => delay{r+1} ;
                              caseL ( b0 => delay{r+1} ;
                                            R.b0 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b1 => delay{r+1} ;
                                            R.b1 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b2 => delay{r+1} ;
                                            R.b2 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b3 => delay{r+1} ;
                                            R.b3 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{r} ;
                                           R.b0 ;
                                           delay{2*r+2} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | b1 => delay{r+1} ;
                              caseL ( b0 => delay{r+1} ;
                                            R.b1 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b1 => delay{r+1} ;
                                            R.b2 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b2 => delay{r+1} ;
                                            R.b3 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b3 => delay{r+1} ;
                                            R.b0 ;
                                            checksum_c{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{r} ;
                                           R.b1 ;
                                           delay{2*r+2} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | b2 => delay{r+1} ;
                              caseL ( b0 => delay{r+1} ;
                                            R.b2 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b1 => delay{r+1} ;
                                            R.b3 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b2 => delay{r+1} ;
                                            R.b0 ;
                                            checksum_c{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b3 => delay{r+1} ;
                                            R.b1 ;
                                            checksum_c{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{r} ;
                                           R.b2 ;
                                           delay{2*r+2} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | b3 => delay{r+1} ;
                              caseL ( b0 => delay{r+1} ;
                                            R.b3 ;
                                            checksum{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b1 => delay{r+1} ;
                                            R.b0 ;
                                            checksum_c{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b2 => delay{r+1} ;
                                            R.b1 ;
                                            checksum_c{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | b3 => delay{r+1} ;
                                            R.b2 ;
                                            checksum_c{r} ||
                                            delay{2*r+2} ;
                                            <->
                                    | e => delay ;
                                           waitL ;
                                           delay{r} ;
                                           R.b3 ;
                                           delay{2*r+2} ;
                                           R.e ;
                                           delay ;
                                           closeR )
                      | e => delay ;
                             waitL ;
                             delay{2*r+1} ;
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
proc checksum_c{r} = caseL ( b0 => delay{r+1} ;
                                caseL ( b0 => delay{r+1} ;
                                              R.b1 ;
                                              checksum{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b1 => delay{r+1} ;
                                              R.b2 ;
                                              checksum{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b2 => delay{r+1} ;
                                              R.b3 ;
                                              checksum{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b3 => delay{r+1} ;
                                              R.b0 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{r} ;
                                             R.b1 ;
                                             delay{2*r+2} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | b1 => delay{r+1} ;
                                caseL ( b0 => delay{r+1} ;
                                              R.b2 ;
                                              checksum{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b1 => delay{r+1} ;
                                              R.b3 ;
                                              checksum{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b2 => delay{r+1} ;
                                              R.b0 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b3 => delay{r+1} ;
                                              R.b1 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{r} ;
                                             R.b2 ;
                                             delay{2*r+2} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | b2 => delay{r+1} ;
                                caseL ( b0 => delay{r+1} ;
                                              R.b3 ;
                                              checksum{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b1 => delay{r+1} ;
                                              R.b0 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b2 => delay{r+1} ;
                                              R.b1 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b3 => delay{r+1} ;
                                              R.b2 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{r} ;
                                             R.b3 ;
                                             delay{2*r+2} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | b3 => delay{r+1} ;
                                caseL ( b0 => delay{r+1} ;
                                              R.b0 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b1 => delay{r+1} ;
                                              R.b1 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b2 => delay{r+1} ;
                                              R.b2 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | b3 => delay{r+1} ;
                                              R.b3 ;
                                              checksum_c{r} ||
                                              delay{2*r+2} ;
                                              <->
                                      | e => delay ;
                                             waitL ;
                                             delay{r} ;
                                             R.b0 ;
                                             delay{2*r+2} ;
                                             R.b1 ;
                                             delay{2*r+2} ;
                                             R.e ;
                                             delay ;
                                             closeR )
                        | e => delay ;
                               waitL ;
                               delay{2*r+1} ;
                               R.b1 ;
                               delay{2*r+2} ;
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
            checksum{3} ||
            delay{8} ;
            <->
exec ex4t

proc t4p0{s} : tet{s} |- () tet{s}
proc t4p1{s} : tet{s} |- () tet{s}
proc t4p2{s} : tet{s} |- () tet{s}
proc t4p3{s} : tet{s} |- () tet{s}
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 1 2 8 1 2 
% backtracking time reconstruction succeeded
% source expression of size 18
% reconstructed exp of size 22
% calls: 66, backtracked: 4
% after reconstruction with cost model --work=none --time=recv
proc t4p0{s} = caseL ( b0 => delay ;
                          R.b0 ;
                          delay{s} ;
                          t4p0{s} ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b0 ;
                          delay{s} ;
                          t4p1{s} ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b0 ;
                          delay{s} ;
                          t4p2{s} ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b0 ;
                          delay{s} ;
                          t4p3{s} ||
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
proc t4p1{s} = caseL ( b0 => delay ;
                          R.b1 ;
                          delay{s} ;
                          t4p0{s} ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b1 ;
                          delay{s} ;
                          t4p1{s} ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b1 ;
                          delay{s} ;
                          t4p2{s} ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b1 ;
                          delay{s} ;
                          t4p3{s} ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b1 ;
                         waitL ;
                         delay{s+1} ;
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
proc t4p2{s} = caseL ( b0 => delay ;
                          R.b2 ;
                          delay{s} ;
                          t4p0{s} ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b2 ;
                          delay{s} ;
                          t4p1{s} ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b2 ;
                          delay{s} ;
                          t4p2{s} ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b2 ;
                          delay{s} ;
                          t4p3{s} ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b2 ;
                         waitL ;
                         delay{s+1} ;
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
proc t4p3{s} = caseL ( b0 => delay ;
                          R.b3 ;
                          delay{s} ;
                          t4p0{s} ||
                          delay ;
                          <->
                  | b1 => delay ;
                          R.b3 ;
                          delay{s} ;
                          t4p1{s} ||
                          delay ;
                          <->
                  | b2 => delay ;
                          R.b3 ;
                          delay{s} ;
                          t4p2{s} ||
                          delay ;
                          <->
                  | b3 => delay ;
                          R.b3 ;
                          delay{s} ;
                          t4p3{s} ||
                          delay ;
                          <->
                  | e => delay ;
                         R.b3 ;
                         waitL ;
                         delay{s+1} ;
                         R.e ;
                         delay ;
                         closeR )

proc is_tet_digit{s} : tet{s} |- ({2*s+2}) +{ false : () () tet{s},
                                               true : () () tet{s} }
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 15 31 16 17 3 2 8 9 15 31 16 17 3 9 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 15 31 16 17 3 9 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 15 31 16 17 3 9 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 15 31 16 17 3 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 8 9 1 1 2 1 2 
% backtracking time reconstruction succeeded
% source expression of size 122
% reconstructed exp of size 151
% calls: 463, backtracked: 32
% after reconstruction with cost model --work=none --time=recv
proc is_tet_digit{s} = caseL ( b0 => delay{s+1} ;
                                  caseL ( b0 => delay{s+1} ;
                                                R.false ;
                                                t4p0{s} ||
                                                delay ;
                                                t4p0{s} ||
                                                delay ;
                                                <->
                                        | b1 => delay{s+1} ;
                                                R.false ;
                                                t4p1{s} ||
                                                delay ;
                                                t4p0{s} ||
                                                delay ;
                                                <->
                                        | b2 => delay{s+1} ;
                                                R.false ;
                                                t4p2{s} ||
                                                delay ;
                                                t4p0{s} ||
                                                delay ;
                                                <->
                                        | b3 => delay{s+1} ;
                                                R.false ;
                                                t4p3{s} ||
                                                delay ;
                                                t4p0{s} ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{s} ;
                                               R.true ;
                                               delay{2} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | b1 => delay{s+1} ;
                                  caseL ( b0 => delay{s+1} ;
                                                R.false ;
                                                t4p0{s} ||
                                                delay ;
                                                t4p1{s} ||
                                                delay ;
                                                <->
                                        | b1 => delay{s+1} ;
                                                R.false ;
                                                t4p1{s} ||
                                                delay ;
                                                t4p1{s} ||
                                                delay ;
                                                <->
                                        | b2 => delay{s+1} ;
                                                R.false ;
                                                t4p2{s} ||
                                                delay ;
                                                t4p1{s} ||
                                                delay ;
                                                <->
                                        | b3 => delay{s+1} ;
                                                R.false ;
                                                t4p3{s} ||
                                                delay ;
                                                t4p1{s} ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{s} ;
                                               R.true ;
                                               delay{2} ;
                                               R.b1 ;
                                               delay{s+1} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | b2 => delay{s+1} ;
                                  caseL ( b0 => delay{s+1} ;
                                                R.false ;
                                                t4p0{s} ||
                                                delay ;
                                                t4p2{s} ||
                                                delay ;
                                                <->
                                        | b1 => delay{s+1} ;
                                                R.false ;
                                                t4p1{s} ||
                                                delay ;
                                                t4p2{s} ||
                                                delay ;
                                                <->
                                        | b2 => delay{s+1} ;
                                                R.false ;
                                                t4p2{s} ||
                                                delay ;
                                                t4p2{s} ||
                                                delay ;
                                                <->
                                        | b3 => delay{s+1} ;
                                                R.false ;
                                                t4p3{s} ||
                                                delay ;
                                                t4p2{s} ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{s} ;
                                               R.true ;
                                               delay{2} ;
                                               R.b2 ;
                                               delay{s+1} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | b3 => delay{s+1} ;
                                  caseL ( b0 => delay{s+1} ;
                                                R.false ;
                                                t4p0{s} ||
                                                delay ;
                                                t4p3{s} ||
                                                delay ;
                                                <->
                                        | b1 => delay{s+1} ;
                                                R.false ;
                                                t4p1{s} ||
                                                delay ;
                                                t4p3{s} ||
                                                delay ;
                                                <->
                                        | b2 => delay{s+1} ;
                                                R.false ;
                                                t4p2{s} ||
                                                delay ;
                                                t4p3{s} ||
                                                delay ;
                                                <->
                                        | b3 => delay{s+1} ;
                                                R.false ;
                                                t4p3{s} ||
                                                delay ;
                                                t4p3{s} ||
                                                delay ;
                                                <->
                                        | e => delay ;
                                               waitL ;
                                               delay{s} ;
                                               R.true ;
                                               delay{2} ;
                                               R.b3 ;
                                               delay{s+1} ;
                                               R.e ;
                                               delay ;
                                               closeR )
                          | e => delay ;
                                 waitL ;
                                 delay{2*s+1} ;
                                 R.true ;
                                 delay{2} ;
                                 R.e ;
                                 delay ;
                                 closeR )

proc consume_tet{s} : tet{s} |- <>1
% temporal synthesis statistics: number of possible typings for each subexpression
% top level first
% 1 1 1 2 1 2 8 9 1 3 8 9 1 3 8 9 1 3 8 9 1 3 
% backtracking time reconstruction succeeded
% source expression of size 13
% reconstructed exp of size 14
% calls: 69, backtracked: 8
% after reconstruction with cost model --work=none --time=recv
proc consume_tet{s} = caseL ( b0 => delay{s+1} ;
                                 consume_tet{s} ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | b1 => delay{s+1} ;
                                 consume_tet{s} ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | b2 => delay{s+1} ;
                                 consume_tet{s} ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | b3 => delay{s+1} ;
                                 consume_tet{s} ||
                                 whenL ;
                                 nowR ;
                                 <->
                         | e => delay ;
                                waitL ;
                                delay ;
                                nowR ;
                                closeR )

(* hand-written, because reconstruction with only constant
 * delays is insufficient
 *)
proc is_div3{r} : tet{r} |- <>bool
proc is_div3{r} = checksum{r}               % (2*r+2) tet{2*r+1} |- <>bool
               || delay{2*r+2} ;            %         tet{2*r+1} |- <>bool
                  is_tet_digit{2*r+1}       % (2*(2*r+1)+2) +{false : ()()tet{2*r+1}, true: ()()tet{2*r+1} |- <>bool
                  || delay{2*(2*r+1)+2} ;   %               +{false : ()()tet{2*r+1}, true: ()()tet{2*r+1} |- <>bool
                     caseL ( false => delay{2} ;         % tet{2*r+1} |- <>bool
                                      is_div3{2*r+1}
                           | true => delay{2} ;          % tet{2*r+1} |- <>bool
                                     caseL ( b0 => delay{2*r+2} ;     % tet{2*r+1} |- <>bool
                                                   nowR ; R.false ;   % tet{2*r+1} |- <>1
                                                   consume_tet{2*r+1}
                                           | b1 => delay{2*r+2} ;
                                                   nowR ; R.false ;
                                                   consume_tet{2*r+1}
                                           | b2 => delay{2*r+2} ;
                                                   nowR ; R.false ;
                                                   consume_tet{2*r+1}
                                           | b3 => delay{2*r+2} ;
                                                   nowR ; R.true ;
                                                   consume_tet{2*r+1}
                                           | e  => delay ;           % 1 |- <>bool
                                                   waitL ;
                                                   nowR ; R.true ;
                                                   nowR ; closeR ) )


proc ex7div3 : <>bool
proc ex7div3 = (R.b1 ; delay ; R.b1 ; delay ; R.b1 ; delay ; R.e ; delay ; closeR)
               [bin{0}] bin2tet{0} || delay{2} ; is_div3{1}
exec ex7div3  % false

proc ex8div3 : <>bool
proc ex8div3 = (R.b1 ; delay ; R.b0 ; delay ; R.b0 ; delay ; R.b0 ; delay ; R.e ; delay ; closeR)
               [bin{0}] bin2tet{0} || delay{2} ; is_div3{1}
exec ex8div3  % false

proc ex9div3 : <>bool
proc ex9div3 = (R.b1 ; delay ; R.b0 ; delay ; R.b0 ; delay ; R.b1 ; delay ; R.e ; delay ; closeR)
               [bin{0}] bin2tet{0} || delay{2} ; is_div3{1}
exec ex9div3  % true

proc ex10div3 : <>bool
proc ex10div3 = (R.b1 ; delay ; R.b0 ; delay ; R.b1 ; delay ; R.b0 ; delay ; R.e ; delay ; closeR)
               [bin{0}] bin2tet{0} || delay{2} ; is_div3{1}
exec ex10div3  % false

(* Not sure how to temporally annotate the counter in this form *)
(* For another form, see icfp18/sec3i.ss *)

(*
type ctr = &{ inc : ctr,
              val : bin }

proc counter : bin |- ctr
proc counter =
     caseR ( inc => succ || counter
           | val => <-> )

proc ex221 : dec
proc ex221 = ex217 || counter || (L.inc ; L.inc ; L.inc ; L.inc ; L.val ; <->) [bin] bin2dec
exec ex221
*)
