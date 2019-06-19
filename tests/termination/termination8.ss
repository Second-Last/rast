#options --syntax=explicit --terminate=iso
#test success

type list=  +{mu_list: +{nil:1, next:tree}}
type tree= &{nu_tree: &{left:tree, right:tree, label:list}}


proc convert: list |- list

proc convert= caseL (mu_list => caseL (nil=> R.mu_list;R.nil; <->
	                                   |next=>R.mu_list;R.next; caseR(nu_tree=>caseR(left=> <->
	                                                                                 |right=> <->
	                                                                                 |label=> L.nu_tree; L. label; convert))))

