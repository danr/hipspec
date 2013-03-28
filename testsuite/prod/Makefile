props := $(filter-out 35,$(filter-out 34,$(filter-out 33,$(shell seq -w 1 50))))
expensive_props = 33 34 35

prop_prefix = prop_T

targets :=

HIPSPEC_FLAGS = --cg -luU
HIPSPEC_EXPENSIVE_FLAGS = --pvars --size 7

define make_expensive_target
results/$(1).json:
	hipspec Properties --auto --only=$(prop_prefix)$(1) $(HIPSPEC_EXPENSIVE_FLAGS) $(HIPSPEC_BASE_FLAGS) $(HIPSPEC_FLAGS) --json=$$@
targets += results/$(1).json
endef

$(foreach prop,$(expensive_props),$(eval $(call make_expensive_target,$(prop))))

include ../Makefile.common

