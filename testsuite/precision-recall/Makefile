
props :=

targets := results/fold.json results/map.json results/nat.json results/length.json

include ../Makefile.common

HIPSPEC_BASE_FLAGS = --smt-data-types -e

results/fold.json: results
	hipspec --extra-trans=++,foldl,foldr --auto PrecisionRecall $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

results/map.json: results
	hipspec --extra-trans=++,map,reverse --auto PrecisionRecall $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

results/nat.json: results
	hipspec --extra-trans=+,* --auto PrecisionRecall $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

results/length.json: results
	hipspec --extra-trans=length,reverse,++ --auto PrecisionRecall $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$@

