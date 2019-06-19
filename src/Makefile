RM	= rm
MLTON = mlton -default-ann "redundantMatch error" -verbose 0

ss: *.mlb *.sml
	$(MLTON) -output ss sources-go.mlb

ss-test: *.mlb *.sml
	$(MLTON) -output ss-test sources-test.mlb

all: ss ss-test

.PHONY: clean
clean:
	$(RM) -rf .cm/
	$(RM) -f ss
	$(RM) -f ss-test
