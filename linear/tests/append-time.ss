#test success
#options --time=recvsend --syntax=explicit

type list{n}{r} = +{cons : `?{n > 0}. ({r+2}) list{n-1}{r}, nil : `?{n = 0}. 1}

decl append{n}{k}{r} : (l1 : list{n}{r}) (l2 : [] list{k}{r}) |- (l : ()() list{n+k}{r})

proc l <- append{n}{k}{r} l1 l2 =
  case l1 (
    cons => assume l1 {n > 0} ;
            delay ;
            l.cons ;
            assert l {n+k > 0} ;
            delay {r} ;
            l <- append{n-1}{k}{r} l1 l2
  | nil => assume l1 {n = 0} ;
           wait l1 ;
           now l2 ;
           l <-> l2
  )