all: verify

EVERPARSE_HOME = $(realpath ../../..)
LOWPARSE_HOME = $(EVERPARSE_HOME)/lib/everparse/lowparse

INCLUDE_PATHS += $(LOWPARSE_HOME) $(realpath ..)

ALREADY_CACHED := *,-ASN1.Pulse,
FSTAR_OPTIONS += --ext optimize_let_vc

include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

# Custard direct-to-C extraction (no KaRaMeL)
C_OUTPUT_DIR := _output
CUSTARD_C_FLAGS := --codegen C --custard_monomorphize_types true

$(C_OUTPUT_DIR)/%.c: %.fst.checked
	mkdir -p $(C_OUTPUT_DIR)
	$(FSTAR) $(CUSTARD_C_FLAGS) --custard_entry_module $* $*.fst -o $@

# C tests: run each extracted validator against its difftest vectors.
# `test` uses the committed vectors and their expected verdicts; `test-oracle`
# also runs the generated mutations, with the pure F* spec runner's verdicts
# (built by ../difftest) as the oracle.
CC ?= cc
# -Wno-type-limits: the extracted length decoder keeps range checks that are
# tautologies on unsigned C types
TEST_CFLAGS := -std=c11 -Wall -Wextra -Werror -Wno-type-limits -O1
DIFFTEST_DIR := ../difftest
DIFFTEST_OUT := $(DIFFTEST_DIR)/out

# For each test module ASN1.Pulse.DiffTest.<T>: vectors file, ASN.1 type, entry point
C_TESTS := Smoke
Smoke.vectors := smoke.json
Smoke.type := DiffSmoke.Smoke
Smoke.entry := validate_smoke

$(C_OUTPUT_DIR)/test_%.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.DiffTest.%.c test/driver.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) \
	  -DHEADER='"ASN1.Pulse.DiffTest.$*.h"' \
	  -DVALIDATE=ASN1_Pulse_DiffTest_$*_$($*.entry) \
	  -o $@ $< test/driver.c

test-%: $(C_OUTPUT_DIR)/test_%.exe
	python3 test/vectors.py --type $($*.type) $(DIFFTEST_DIR)/vectors/$($*.vectors) | $<

test-oracle-%: $(C_OUTPUT_DIR)/test_%.exe
	$(MAKE) -C $(DIFFTEST_DIR) out/ours.jsonl
	python3 test/vectors.py --type $($*.type) --oracle $(DIFFTEST_OUT)/ours.jsonl \
	  $(DIFFTEST_DIR)/vectors/$($*.vectors) $(DIFFTEST_OUT)/gen/mutations.json | $<

test: $(addprefix test-,$(C_TESTS))
test-oracle: $(addprefix test-oracle-,$(C_TESTS))

.PRECIOUS: $(C_OUTPUT_DIR)/%.c $(C_OUTPUT_DIR)/%.h $(C_OUTPUT_DIR)/test_%.exe
.PHONY: test test-oracle
