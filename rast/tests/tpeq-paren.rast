#test error

type A = 1

type ctr{x}{y} = +{lt : ?{x < y}. (A -o A) * |{y-x}> ctr{x+1}{y},
				   ge : ?{x >= y}. 1}

type ctr'{x}{y} = +{lt : ?{x < y}. A -o A * |{y-x}> ctr{x+1}{y},
				   ge : ?{x >= y}. 1}

eqtype ctr{x}{y} = ctr'{x+1}{y+1}