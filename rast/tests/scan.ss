#test success
#options --work=none --time=none --syntax=implicit

type bit = +{b0 : 1, b1 : 1}

decl b0 : . |- (b : bit)
decl b1 : . |- (b : bit)
proc b <- b0 = b.b0 ; close b
proc b <- b1 = b.b1 ; close b

type seq{n} = +{ cons : ?{n > 0}. bit * seq{n-1},
                 nil : ?{n = 0}. 1 }

decl scan{n} : (x : seq{n}) |- (y : seq{n+1})
decl scan_xor{n} : (b : bit) (x : seq{n}) |- (y : seq{n+1})

proc y <- scan_xor{n} b x =  % b = prefix 'sum' so far
  case b ( b0 => wait b ; y.cons ; b' <- b0 ; send y b' ;
           case x ( cons => c <- recv x ;
                            case c ( b0 => wait c ; b' <- b0 ;
                                           y <- scan_xor{n-1} b' x
                                   | b1 => wait c ; b' <- b1 ;
                                           y <- scan_xor{n-1} b' x )
                  | nil => wait x ; y.nil ; close y )
         | b1 => wait b ; y.cons ; b' <- b1 ; send y b' ;
           case x ( cons => c <- recv x ;
                            case c ( b0 => wait c ; b' <- b1 ;
                                           y <- scan_xor{n-1} b' x
                                   | b1 => wait c ; b' <- b1 ;
                                           y <- scan_xor{n-1} b' x )
                  | nil => wait x ; y.nil ; close y ) )

proc y <- scan{n} x =
  b <- b0 ;   % b0 is neutral element of xor
  y <- scan_xor{n} b x
