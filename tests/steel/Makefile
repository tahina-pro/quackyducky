TARGETS := unit
TARGETS += fold

all: $(TARGETS)

$(TARGETS): %:
	+$(MAKE) -C $@

.PHONY: all $(TARGETS)
