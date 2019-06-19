#options --syntax=explicit --terminate=iso
#test success


(*How priorities work - exchanging tree and nodeinfo order makes the program nonterminating*)

(*A valid Cut*)

type tree= &{nu_tree: &{left:nodeinfo, right:nodeinfo, label:nat}}
type nodeinfo=  +{mu_nodeinfo: +{zero:nodeinfo, one:nodeinfo, node:tree}}
type nat=+{mu_nat:+{s:nat, z:1}}


proc Builde: . |- tree
proc Builde= caseR (nu_tree=> caseR (left=>R.mu_nodeinfo;R.one;R.mu_nodeinfo; R.node;Builde
	                                 |right=>R.mu_nodeinfo;R.zero;R.mu_nodeinfo;R.node;Builde
	                                 |label=>R.mu_nat;R.z;closeR))

proc childtopar: tree |-tree
proc childtopar= caseR(nu_tree=>caseR(left=> R.mu_nodeinfo;R.one; R.mu_nodeinfo;R.node;<->
	                                   |right=> R.mu_nodeinfo;R.zero; R.mu_nodeinfo;R.node;  <->
	                                   |label=> L.nu_tree;L.label; R.mu_nat; R.s; <->))

proc Buildl: nat |- tree
proc Buildl= caseR (nu_tree=> caseR (left=>(R.mu_nat;R.s;<->) [nat] (R.mu_nodeinfo;R.one;R.mu_nodeinfo; R.node;  Buildl)
	                                 |right=>(R.mu_nat;R.s;<->) [nat] (R.mu_nodeinfo;R.zero;R.mu_nodeinfo;R.node;Buildl)
	                                 |label=><->))
