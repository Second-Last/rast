RM	= rm
MLTON = mlton -default-ann "redundantMatch error" -verbose 0

lin: *.mlb *.sml
	$(MLTON) -output lin sources-go.mlb

lin-test: *.mlb *.sml
	$(MLTON) -output lin-test sources-test.mlb

all: lin lin-test

.PHONY: clean
clean:
	$(RM) -rf .cm/
	$(RM) -f lin
	$(RM) -f lin-test
