#options --syntax=explicit --terminate=iso
#test success

type tree= &{nu_tree: &{left:nodeinfo, right:nodeinfo, label:nat}}
type nodeinfo=  +{mu_nodeinfo: +{zero:nodeinfo, one:nodeinfo, node:tree}}
type nat=+{mu_nat:+{s:nat, z:nodeinfo}}

proc P: nat |- nodeinfo
proc P= caseL(mu_nat=>caseL(s=> R.mu_nodeinfo; R.zero; P
                           |z=> <->))
