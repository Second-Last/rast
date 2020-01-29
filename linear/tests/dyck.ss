#options --syntax=implicit
#test success

%%% Parsing a Dyck language of matching parentheses
%%% and a related program to serialize and deserialize a tree

type dyck0{n} = +{ lparen : dyck0{n+1},
                   rparen : ?{n > 0}. dyck0{n-1},
                   end : ?{n = 0}. 1 }

type sexp = +{ nil : 1,
               cons : sexp * sexp }

%%% Parse (() () ()) into cons (nil, cons (nil, cons (nil, nil)))

type stack{n} = &{ push : stack{n+1},
                   pop : +{ none : ?{n = 0}. 1,
                            some : ?{n > 0}. stack{n-1} } }

decl parse : (w : dyck0{0}) |- (r : 1)
decl pda{n} : (w : dyck0{n}) (s : stack{n}) |- (r : 1)

proc r <- pda{n} w s =
  case w ( lparen => s.push ;
                     r <- pda{n+1} w s
         | rparen => s.pop ;  % must succeed!
                     case s ( some => r <- pda{n-1} w s )
         | end => wait w ;
                  s.pop ; case s ( none => wait s ;
                                           close r ) )


