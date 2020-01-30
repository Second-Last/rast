RM	= rm
MLTON = mlton -default-ann "redundantMatch error" -verbose 0

rast: *.mlb *.sml
	$(MLTON) -output rast sources-go.mlb

rast-test: *.mlb *.sml
	$(MLTON) -output rast-test sources-test.mlb

all: rast rast-test

.PHONY: clean
clean:
	$(RM) -rf .cm/
	$(RM) -f rast
	$(RM) -f rast-test
