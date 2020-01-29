#options --syntax=implicit

type cell = +{ b0 : 1, b1 : 1, bb : 1}

type tape = &{ next : cell * tape }

decl triv : . |- (u : 1)
proc u <- triv = close u

decl b0 : (u : 1) |- (c : cell)
decl b1 : (u : 1) |- (c : cell)
decl bb : (u : 1) |- (c : cell)

proc c <- b0 u = c.b0 ; c <-> u
proc c <- b1 u = c.b1 ; c <-> u
proc c <- bb u = c.bb ; c <-> u

decl write : (c : cell) (s : tape) |- (t : tape)
proc t <- write c s =
   case t ( next => send t c ; t <-> s )

decl writeB0 : (u : 1) (t : tape) |- (s : tape)
decl writeB1 : (u : 1) (t : tape) |- (s : tape)
decl writeBB : (u : 1) (t : tape) |- (s : tape)

proc t <- writeB1 x t' = x' <- b0 x ; t <- write x' t'
proc t <- writeB0 x t' = x' <- b1 x ; t <- write x' t'
proc t <- writeBB x t' = x' <- bb x ; t <- write x' t'

decl empty : . |- (t : tape)
proc t <- empty =
  case t ( next => u <- triv ;
                   c <- bb u ;
                   send t c ;
                   t <- empty )

%% No need to distinguish between accept and reject
%% just halt (1) providing the tapes to the left and
%% right of the read/write head.
type answer = tape * tape * 1

decl inc0 : (l : tape) (x : cell) (r : tape) |- (a : answer)
decl inc1 : (l : tape) (x : cell) (r : tape) |- (a : answer)

proc a <- inc0 l x r =
  case x ( b0 => r' <- writeB1 x r ;  % write B1
                 l.next ; y <- recv l ;  % move left
                 a <- inc0 l y r'     % go to state 1
         | b1 => l' <- writeB0 x l ;  % write B0
                 r.next ; y <- recv r ;  % move right
                 a <- inc1 l' y r     % to to state 1
         | bb => r' <- writeB1 x r ;  % write B1
                 l.next ; y <- recv l ;  % move left
                 a <- inc1 l y r'     % go to state 1
         )

proc a <- inc1 l x r =
  case x ( b0 => r' <- writeB0 x r ;  % write B0
                 l.next ; y <- recv l ;  % move left
                 a <- inc1 l y r'     % go to state 1
         | b1 => r' <- writeB1 x r ;  % write B1
                 l.next ; y <- recv l ;  % move left
                 a <- inc1 l y r'     % to to state 1
         | bb => wait x ;
                 send a l ;
                 send a r ;
                 close a
         )
