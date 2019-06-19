#options --time=none --work=none --syntax=explicit --terminate=iso
#test error

type nat = +{mu_nat : +{z : 1, s : nat}}

type stream = &{nu_stream : &{hd : list, tl : stream}}
type list = +{mu_list : +{nil : nat, cons : stream}}

proc C : list |- stream
proc C = P

proc P : list |- stream
proc P = C
