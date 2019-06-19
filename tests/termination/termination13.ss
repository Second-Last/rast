#options --syntax=explicit --terminate=iso
#test success

type tree= &{nu_tree: &{left:nodeinfo, right:nodeinfo, label:natstr}}
type nodeinfo=  +{mu_nodeinfo: +{zero:nodeinfo, one:nodeinfo, node:tree}}
type natstr=+{mu_natstr:+{s:natstr, z:stream}}
type stream=&{nu_stream: &{hd:natstr, tl:stream}}

proc P: natstr |- nodeinfo
proc P= caseL(mu_natstr=>caseL(s=> R.mu_nodeinfo; R.one; P
                           |z=>R.mu_nodeinfo; R.node; caseR(nu_tree=>caseR(left=>(R.mu_natstr;R.z;<->)[natstr]P
                                                                           |right=>(R.mu_natstr;R.z;<->)[natstr]P
                                                                           |label=>R.mu_natstr;R.z;<->))))

proc Q: nodeinfo |- natstr
proc Q= caseL (mu_nodeinfo=> caseL(zero=>Q
	                              |one=>R.mu_natstr; R.s; Q
	                              |node=>L.nu_tree;L.label;<->))

proc S: natstr|-stream
proc S= caseL(mu_natstr=> caseL(s=> S
	                         |z=> L.nu_stream; L.hd; S))


proc T: natstr|-stream
proc T= P [nodeinfo] Q [natstr] S
