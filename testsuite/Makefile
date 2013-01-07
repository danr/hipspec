#
# Settings:
#   * theorem prover
#   * assoc important
#   * interesting candidates
#   * swap representatives
#   * prepend pruned
#   * induction variables
#   * induction depth
#   * timeout
#   * processes
#
# Always use -l --isolate

GHC       = ghc
GHC_FLAGS = -threaded -O2 --make
N         = -N 2
# REDIRECT  = >
REDIRECT = | tee

# The files to test
files = Nat Reverse


# The different flags to test, separate flags with underscore
base_flags =    \
	-i_-a_-s    \
	-i_-a       \
	-i_-s       \
	-a_-s       \
	-s          \
	-a          \
	-i          \
	-p_-i_-a_-s \
	-p_-i_-a    \
	-p_-i_-s    \
	-p_-a_-s    \
	-p_-s       \
	-p_-a       \
	-p_-i       \
	-p

flags :=

# Make flags from base flags times theorem prover to use
$(foreach flag,$(base_flags),$(eval \
	flags += $(flag)_-p_e \
			 $(flag)_-p_f \
			 $(flag)_-p_z \
			 $(flag)_-p_x \
			 $(flag)_-p_v))

# # Times timeout, try 1 and 2 seconds
# $(foreach flag,$(base_flags),$(eval \
# 	flags += $(flag)_-t_1 \
# 			 $(flag)_-t_2 \
# 			 $(flag)_-t_3))

# Different induction settings
$(foreach flag,$(base_flags),$(eval \
	flags += $(flag)_-D_1 \
			 $(flag)_-D_2))
$(foreach flag,$(base_flags),$(eval \
	flags += $(flag)_-S_1 \
   		     $(flag)_-S_2 \
			 $(flag)_-S_3))

# Flag delimiter
delim:= _
empty:=
space:= $(empty) $(empty)

# All targets
all_targets :=

# First argument is binary, then an underscore-separated list of flags
define flag_rule
$(1)$(2): $(1)
	./$(1) -l $(subst $(delim),$(space),$(2)) $(N) $(REDIRECT) $$@
all_targets += $(1)$(2)
endef

# Generate rules for a given file
define file_rule
$(1): $(1).hs
	$$(GHC) $$(GHC_FLAGS) $$(arg1) -o $$@

$(foreach flag,$(flags),$(eval $(call flag_rule,$(file),$(flag))))
endef

# Generate all rules
$(foreach file,$(files),$(eval $(call file_rule,$(file))))

# Make all targets
all: $(all_targets)

# Remove all targets
clean:
	rm -f $(all_targets)
	rm -f $(files)

.PHONY: all clean

# Shortcut variables for indexing prerequisites of rules:
arg1 = $(word 1,$+)
arg2 = $(word 2,$+)
arg3 = $(word 3,$+)
