props :=

targets := results/nicomachus.json results/reverse.json results/rotate.json

include ../Makefile.common

HIPSPEC_BASE_FLAGS = --smt-data-types -u

results/nicomachus.json: results
	hipspec Nicomachus --auto $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

results/reverse.json: results
	hipspec Reverse --auto $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

results/rotate.json: results
	hipspec Rotate --auto $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

