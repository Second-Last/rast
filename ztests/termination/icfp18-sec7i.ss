#options --time=recvsend --syntax=implicit --terminate=equi

% interesting: this type also seems to work for the same
% implicit program!
(*
type stack = &{push : `&{b0 : `stack, b1 : `stack},
               pop : `+{none : `1, some : `+{b0 : `stack, b1 : `stack}}}
*)
type stack = &{push : `&{b0 : `[]stack, b1 : `[]stack},
               pop : `+{none : `1, some : `+{b0 : `[]stack, b1 : `[]stack}}}

proc elem0 : []stack |- []stack
proc elem1 : []stack |- []stack
proc empty :       . |- []stack

proc elem0 = caseR ( push => caseR ( b0 => elem0 || elem0
                                   | b1 => elem0 || elem1 )
                   | pop => R.some ; R.b0 ; <-> )
proc elem1 = caseR ( push => caseR ( b0 => elem1 || elem0
                                   | b1 => elem1 || elem1 )
                   | pop => R.some ; R.b1 ; <-> )
proc empty = caseR ( push => caseR ( b0 => empty || elem0
                                   | b1 => empty || elem1 )
                   | pop => R.none ; closeR )

type queue = &{enq : `&{b0 : `()()[]queue, b1 : `()()[]queue},
               deq : `+{none : `1, some : `+{b0 : `[]queue, b1 : `[]queue}}}

proc qelem0 : ()()[]queue |- []queue
proc qelem1 : ()()[]queue |- []queue
proc qempty :           . |- []queue

proc qelem0 = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; qelem0
                                   | b1 => L.enq ; L.b1 ; qelem0 )
                    | deq => R.some ; R.b0 ; <-> )
proc qelem1 = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; qelem1
                                   | b1 => L.enq ; L.b1 ; qelem1 )
                    | deq => R.some ; R.b1 ; <-> )
proc qempty = caseR ( enq => caseR ( b0 => qempty || qelem0
                                   | b1 => qempty || qelem1 )
                    | deq => R.none ; closeR )

% The type of append is parametric in the length of a list
% and therefore it doesn't seem expressible in ss so far

% The type of alternate requires two input lists to alternate
% between and therefore isn't in the subsingleton fragment

% Similarly for trees and fold
