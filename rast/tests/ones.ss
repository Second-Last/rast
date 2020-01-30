#test success
#options --syntax=implicit

type ones{i} = !j. !{j < i}. 1 * ones{j}

decl copy{i} : (x : ones{i}) |- (y : ones{i})
proc y <- copy{i} x =
  {j} <- recv y ;
  send x {j} ;
  z <- recv x ;
  send y z ;
  y <- copy{j} x

decl copy'{i} : (x : ones{i}) |- (y : ones{i})
proc y <- copy'{i} x = y <- copy'{i} x
