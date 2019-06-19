#options --time=recv --syntax=explicit

type in{w} = +{ e : ()?{w = 0}. 1 }
type out{w} = +{ e : ?{w = 0}. ()1}

proc copy{w} : in{w} |- ()out{w}
proc copy{w} = caseL ( e =>                    % ()?{w = 0}. 1 |- ()out{w}
                            % tick ;           %   ?{w = 0}. 1 |- out{w}
                            assumeL{w = 0} ;   %             1 |- out{w}
                            R.e  ;             %             1 |- ?{w = 0}. ()1
                            assertR{w = 0} ;   %             1 |- ()1
                            waitL ;            %             . |- ()1
                            % tick ;           %             . |- 1
                            closeR )
