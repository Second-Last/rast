#options --syntax=explicit --terminate=iso
#test success

type tree= &{nu_tree: &{left:nodeinfo, right:nodeinfo, label:nat}}
type nodeinfo=  +{mu_nodeinfo: +{zero:nodeinfo, one:nodeinfo, node:tree}}
type nat=+{mu_nat:+{s:nat, z:1}}

proc P: nat |- nodeinfo
proc P= caseL(mu_nat=>caseL(s=> R.mu_nodeinfo; R.one; P
                           |z=>R.mu_nodeinfo; R.node; caseR(nu_tree=>caseR(left=>(R.mu_nat;R.z;<->)[nat]P
                                                                           |right=>(R.mu_nat;R.z;<->)[nat]P
                                                                           |label=>R.mu_nat;R.z;<->))))

proc Q: nodeinfo |- nat
proc Q= caseL (mu_nodeinfo=> caseL(zero=>Q
	                              |one=>R.mu_nat; R.s; Q
	                              |node=>L.nu_tree;L.label;<->))