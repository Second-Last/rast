#options --syntax=implicit
#test error

type list1 = +{cons : |> list1,
               nil : 1}

type list0 = +{cons : |> list0,
               nil : 1}

proc pos_mon : list1 |- list0

proc pos_mon =
  caseL ( cons => work ; R.cons ; pos_mon
        | nil => waitL ; R.nil ; closeR )