#options --time=none --work=none --syntax=explicit --terminate=iso
#test error

type nat = +{mu_nat : +{z : 1, s : nat}}

type stream = &{nu_stream : &{hd : list, tl : stream}}
type list = +{mu_list : +{nil : nat, cons : stream}}

proc C : list |- stream
proc C = caseR (nu_stream => caseR ( hd => P
                                   | tl => P || C ))

proc P : list |- list
proc P = R.mu_list ; R.cons ; C
% termination failure (3) in previous line

% proc empty : list
% proc empty = R.mu ; R.nil ; R.mu ; R.z ; closeR

% proc inf : stream |- 1
% proc inf = L.nu ; L.tl ; inf

% % this should loop
% proc test : 1
% proc test = empty || C || inf
% % exec test

% % ----------------------------------------------------------------------

% proc D : list |- stream
% proc D = caseR (nu => caseR ( hd => Q | tl => Q || D ))

% proc Q : list |- list
% proc Q = R.mu ; R.cons ; caseR (nu => caseR (hd => Q | tl => D))

% proc interact : stream |- 1
% proc interact = L.nu ; L.hd ; caseL (mu => caseL (nil => interact2 | cons => interact))
% proc interact2 : nat |- 1
% proc interact2 = caseL (mu => caseL (z => waitL ; closeR
%                                     |s => interact2))

% % this should also loop!
% proc test2 : 1
% proc test2 = empty || D || interact
% % exec test2

% % ----------------------------------------------------------------------
% proc E : list |- stream
% proc U : list |- list
% proc S : nat |- list
% proc T : stream |- stream

% proc E = caseR (nu => caseR ( hd => U | tl => U || E ))
% proc U = caseL (mu => caseL (nil => S | cons => R.mu ; R.cons ; T))
% proc S = caseL (mu => caseL (z => R.mu ; R.nil ; R.mu ; R.z ; waitL ; closeR
%                             |s => S))
% proc T = caseR (nu => caseR (hd => L.nu ; L.hd ; U
%                             |tl => L.nu ; L.tl ; T))

% proc test3 : 1
% proc test3 = empty || E || interact
% exec test3
% % ----------------------------------------------------------------------
% proc F : list |- stream
% proc F = caseR (nu => caseR ( hd => V
%                             | tl => F ))
% proc V : list |- list
% proc V = R.mu ; R.cons ; F

% % loops
% proc test4 : 1
% proc test4 = empty || F || interact
% % exec test4
