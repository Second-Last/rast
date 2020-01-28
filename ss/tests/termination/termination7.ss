#options --syntax=explicit --terminate=iso
#test success

(*mutually recursive functions*)
type tree= &{nu_tree: &{left:tree, right:tree, label:list}}
type list=  +{mu_list: +{nil:1, next:tree}}

proc convert: list |- tree
proc X: 1|- tree
proc convert= caseL (mu_list => caseL (nil=> X
	                                   |next=>caseR(nu_tree=> caseR (left=> L.nu_tree;L.left; <->
	                                   	                            |right=> L.nu_tree;L.right; <->
	                                   	                            |label=>R.mu_list;R.next;L.nu_tree;L.label;convert))))


proc X= caseR (nu_tree=> caseR(left=>X
	                           |right=>X
	                           |label=>R.mu_list;R.nil;	<->))