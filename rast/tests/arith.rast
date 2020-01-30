type bin = +{ b0 : bin,
              b1 : bin,
              e : 1 }

decl zero : . |- (x : bin)
decl succ : (y : bin) |- (x : bin)

proc x <- zero = x.e ; close x
proc x <- succ y =
  case y ( b0 => x.b1 ; x <-> y
         | b1 => x.b0 ; x <- succ y
         | e => x.b1 ; x.e ; wait y ; close x )

decl plus : (y : bin) (z : bin) |- (x : bin)
proc x <- plus y z =
  case y ( b0 => case z ( b0 => x.b0 ; x <- plus y z
                        | b1 => x.b1 ; x <- plus y z
                        | e => x.b0 ; wait z ; x <-> y )
         | b1 => case z ( b0 => x.b1 ; x <- plus y z
                        | b1 => x.b0 ; w <- plus y z ;
                                       x <- succ w
                        | e => x.b1 ; wait z ; x <-> y )
         | e => wait y ; x <-> z )

decl drop : (y : bin) |- (u : 1)
proc u <- drop y =
  case y ( b0 => u <- drop y
         | b1 => u <- drop y
         | e => wait y; close u )

decl dbl0 : (y : bin) |- (x : bin)
decl dbl1 : (y : bin) |- (x : bin)

(* make sure no leading 0s are produced *)
proc x <- dbl0 y =
  case y ( b0 => x.b0 ; x.b0 ; x <-> y
         | b1 => x.b0 ; x.b1 ; x <-> y
         | e => x.e ; wait y ; close x )

proc x <- dbl1 y = x.b1 ; x <-> y

decl dup : (y : bin) |- (yy : bin * bin)
proc yy <- dup y =
  case y ( b0 => yy' <- dup y ;
                 y1' <- recv yy' ;
                 y1 <- dbl0 y1' ;
                 send yy y1 ;
                 y2 <- dbl0 yy' ;
                 yy <-> y2
         | b1 => yy' <- dup y ;
                 y1' <- recv yy' ;
                 y1 <- dbl1 y1' ;
                 send yy y1 ;
                 y2 <- dbl1 yy' ;
                 yy <-> y2
         | e => wait y ;
                y1 <- zero ;
                send yy y1 ;
                yy <- zero)

decl dup1 : (y : bin) |- (yy : bin * bin * 1)
proc yy <- dup1 y =
  case y ( b0 => yy' <- dup1 y ;
                 y1' <- recv yy' ;
                 y2' <- recv yy' ; wait yy' ;
                 y1 <- dbl0 y1' ; send yy y1 ; 
                 y2 <- dbl0 y2' ; send yy y2 ;
                 close yy
         | b1 => yy' <- dup1 y ;
                 y1' <- recv yy' ;
                 y2' <- recv yy' ; wait yy' ;
                 y1 <- dbl1 y1' ; send yy y1 ;
                 y2 <- dbl1 y2' ; send yy y2 ;
                 close yy
         | e => wait y ;
                y1 <- zero ; send yy y1 ;
                y2 <- zero ; send yy y2 ;
                close yy )

decl times : (y : bin) (z : bin) |- (x : bin)
proc x <- times y z =
  case y ( b0 => x.b0 ; x <- times y z  % (2*y)*z = 2*(y*z)
         | b1 => zz <- dup z ;
                 z1 <- recv zz ;
                 w1 <- times y z1 ; % (2*y+1)*z = 2*y*z + z
                 w2 <- dbl0 w1 ;
                 x <- plus w2 zz
         | e => wait y;               % 0*z = 0
                u <- drop z; wait u;
                x <- zero )

decl inc : (y : bin) |- (x : bin)
proc x <- inc y =
  case y ( b0 => x.b1 ; x <-> y
         | b1 => x.b0 ; x <- inc y
         | e => wait y ; x.b1 ; x.e ; close x )

type bool = +{true : 1, false : 1}
decl true : . |- (x : bool)
decl false : . |- (x : bool)
proc x <- true = x.true ; close x
proc x <- false = x.false ; close x

decl dec : (y : bin) |- (x : bin)
proc x <- dec y =
  case y ( b0 => x.b1 ; x <- dec y
         | b1 => x <- dbl0 y
         | e => x.e ; wait y ; close x )

decl decr : (y : bin) |- (x : bool * bin)
proc x <- decr y =
  case y ( b0 => f <- false ; send x f ; x.b1 ; x <- dec y
         | b1 => f <- false ; send x f ; x <- dbl0 y
         | e => t <- true; send x t ; x.e ; wait y ; close x )

type stream = +{prime : stream, composite : stream}

decl filter : (t : stream) (c : bin) |- (s : stream)
% to be implemented

decl head : (t : stream) (c : bin) |- (s : stream)
proc s <- head t c =
  case t ( prime => cc <- dup1 c ;
                    c1 <- recv cc ; c2 <- recv cc ; wait cc ;
                    r <- filter t c2 ;
                    s.prime ;
                    c1' <- inc c1 ;
                    s <- head r c1'
         | composite => s.composite ;
                    c' <- inc c;
                    s <- head t c' )
