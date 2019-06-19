#options --syntax=explicit --terminate=iso
#test success



type tree= &{nu_tree: &{left:nodeinfo, right:nodeinfo, label:nat}}
type nodeinfo=  +{mu_nodeinfo: +{zero:nodeinfo, one:nodeinfo, node:tree}}
type nat=+{mu_nat:+{s:nat, z:1}}


proc Build: nodeinfo |- tree
proc Build= caseR (nu_tree=> caseR ( left=> R.mu_nodeinfo; R.zero; Buildn
	                                 |right=>R.mu_nodeinfo;R.one;Buildn
	                                 |label=>Extract))
proc Buildn:nodeinfo|-nodeinfo
proc Buildn=R.mu_nodeinfo;R.node; Build

proc Extract: nodeinfo|-nat
proc Extract=caseL(mu_nodeinfo=> caseL(zero=> R.mu_nat;R.s; Extract
	                                   | one=> R.mu_nat;R.s;R.mu_nat;R.s;Extract
	                                   | node=>treetonat))
proc treetonat: tree|- nat
proc treetonat= L.nu_tree;L.label;<->