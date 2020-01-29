#test success
#options --time=recvsend --syntax=explicit

type A = [] 1
type list{n}{k} = +{cons : `?{n > 0}. A * `({k+4}) list{n-1}{k}, nil : `?{n = 0}. 1}
type B = 1
type C = ({5}) 1

type folderAB{k} = &{next : `A -o `B -o `({k}) C * `()() folderAB{k},
                  done : `1}

decl fold{n}{k} : (l : list{n}{k}) (f : ()() folderAB{k}) (b : ({4}) B) |- (r : <>B)

proc r <- fold{n}{k} l f b =
  case l (
    cons => assume l {n > 0} ;
            x <- recv l ;
            f.next ;
            send f x ;
            send f b ;
            delay {k} ;
            b <- recv f ;
            r <- fold{n-1}{k} l f b
  | nil => assume l {n = 0} ;
           wait l ;
           f.done ;
           wait f ;
           now r ;
           r <-> b
  )