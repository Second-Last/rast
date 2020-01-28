#options --syntax=implicit --time=free --work=free
#test success

% Finite state transducers

% Cost model is free which means we insert by hand:
%
% delay after recv
% work before send
%
% this allows us to check multiple variations of the
% same program

type stream = +{a : stream, b : stream}

proc copy : stream |- stream
proc copy = caseL ( a => R.a ; copy
                  | b => R.b ; copy )

proc ex_aaba : stream |- stream
proc ex_aaba = R.a ; R.a ; R.b ; R.a ; <->
exec ex_aaba

type stream_t = +{a : ()stream_t, b : ()stream_t}
proc copy_t : stream_t |- () stream_t
proc copy_t = caseL ( a => tick ; R.a ; copy_t
                    | b => tick ; R.b ; copy_t )

type stream_w = +{a : |>stream_w, b : |>stream_w}
proc copy_w : stream_w |- stream
proc copy_w = caseL ( a => work ; R.a ; copy_w
                    | b => work ; R.b ; copy_w )

% if mixed, work has to come "outside" type
type stream_wt = +{a : |>()stream_wt, b : |>()stream_wt}
proc copy_wt : stream_wt |- ()stream_t
proc copy_wt = caseL ( a => tick ; work ; R.a ; copy_wt
                     | b => tick ; work ; R.b ; copy_wt )
