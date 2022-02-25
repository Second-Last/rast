#options --syntax=explicit --terminate=iso
#test error

type ack=+{mu_ack: +{ack:astream}}
type astream=&{nu_astream: &{head:ack, tail:astream}}
type nat=+{mu_nat:+{z:1, s:nat}}


proc Ping_Pong: nat |- nat
proc Ping_Pong= Ping [astream] Pong
proc Ping: nat |- astream
proc Ping= caseR(nu_astream => caseR (head=> R.mu_ack;R.ack;Ping
	                              | tail=> Ping ))
proc Pong: astream |- nat
proc Pong= L.nu_astream; L.head; caseL(mu_ack => caseL (ack=> R.mu_nat;R.s;Pong ))


