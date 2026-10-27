# ASN.1 DER differential tests: ours vs asn1tools vs rasn vs asn1-rs.
# See README.md. Run from src/ASN1 via `make test` (target difftest).
#
#   make check        run every enabled implementation, then gate (default)
#   make rebaseline   rewrite triage/known.json from the current results
#   make clean        remove out/, .venv/ and the Rust target/
#
# Opt-outs: ASN1_DIFFTEST_PY=0 skips asn1tools (no Python venv);
# ASN1_DIFFTEST_RUST=0 skips rasn and asn1-rs. ASN1_DIFFTEST_RUST defaults
# to 1 if a recent enough `cargo` is on PATH, 0 (with a warning) otherwise.

ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(CURDIR))
else
  local_curdir := $(CURDIR)
endif

OURS ?= $(local_curdir)/../evaluation/ASN1_Parser.exe
OUT := $(local_curdir)/out
MANIFEST := $(OUT)/manifest.json
REPORT := $(OUT)/report.md
SCHEMAS := $(local_curdir)/schemas
VECTORS := $(wildcard vectors/*.json)

PYTHON ?= python3
VENV_DIR := $(local_curdir)/.venv
ifeq ($(OS),Windows_NT)
VENV_PYTHON := $(VENV_DIR)/Scripts/python.exe
else
VENV_PYTHON := $(VENV_DIR)/bin/python
endif
ASN1_DIFFTEST_PY ?= 1

# The crates pinned in harness/rust/Cargo.lock need Rust >= 1.$(RUST_MIN_MINOR)
CARGO ?= cargo
RUST_MIN_MINOR := 89
ifeq (,$(ASN1_DIFFTEST_RUST))
cargo_minor := $(shell $(CARGO) --version 2>/dev/null | sed -n 's/^cargo 1\.\([0-9]*\).*/\1/p')
ifeq (,$(cargo_minor))
ASN1_DIFFTEST_RUST := 0
$(warning difftest: $(CARGO) not found, skipping the rasn and asn1-rs runners)
else ifeq (,$(shell test $(cargo_minor) -ge $(RUST_MIN_MINOR) && echo ok))
ASN1_DIFFTEST_RUST := 0
$(warning difftest: $(CARGO) is 1.$(cargo_minor) < 1.$(RUST_MIN_MINOR), skipping the rasn and asn1-rs runners)
else
ASN1_DIFFTEST_RUST := 1
endif
endif
RUST_DIR := $(local_curdir)/harness/rust
RUST_BIN := $(RUST_DIR)/target/release

RESULTS := $(OUT)/ours.jsonl
DISABLED :=
ifeq (1,$(ASN1_DIFFTEST_PY))
RESULTS += $(OUT)/asn1tools.jsonl
else
DISABLED += $(OUT)/asn1tools.jsonl
endif
ifeq (1,$(ASN1_DIFFTEST_RUST))
RESULTS += $(OUT)/rasn.jsonl $(OUT)/asn1-rs.jsonl
else
DISABLED += $(OUT)/rasn.jsonl $(OUT)/asn1-rs.jsonl
endif

REPORT_ARGS = --manifest $(MANIFEST) --capabilities capabilities \
  --known triage/known.json --results $(OUT)

all: check

GEN := $(OUT)/gen

$(MANIFEST): $(VECTORS) features.json report.py gen/mutate.py
	mkdir -p $(GEN)
	$(PYTHON) gen/mutate.py vectors $(GEN)/mutations.json
	$(PYTHON) report.py manifest vectors features.json $@ --gen $(GEN)

$(OUT)/ours.jsonl: $(MANIFEST) $(OURS)
	$(OURS) DIFFTEST $(MANIFEST) $@

# The stamp is only written once the pinned requirements are installed
# (the venv python itself may be a symlink to the system interpreter).
VENV_STAMP := $(VENV_DIR)/.installed
$(VENV_STAMP): harness/asn1tools/requirements.txt
	rm -rf $(VENV_DIR)
	$(PYTHON) -m venv $(VENV_DIR)
	$(VENV_PYTHON) -m pip install --quiet --disable-pip-version-check -r $<
	touch $@

venv: $(VENV_STAMP)

$(OUT)/asn1tools.jsonl: $(MANIFEST) $(VENV_STAMP) harness/asn1tools/runner.py $(wildcard schemas/*.asn)
	$(VENV_PYTHON) harness/asn1tools/runner.py $(SCHEMAS) $(MANIFEST) $@

# cargo does its own dependency tracking, so always ask it.
build-rust:
	cd $(RUST_DIR) && $(CARGO) build --release --locked --quiet

$(OUT)/rasn.jsonl: $(MANIFEST) build-rust
	$(RUST_BIN)/rasn-runner $(MANIFEST) $@

$(OUT)/asn1-rs.jsonl: $(MANIFEST) build-rust
	$(RUST_BIN)/asn1rs-runner $(MANIFEST) $@

run: $(RESULTS)
	rm -f $(DISABLED)

check: run
	$(PYTHON) report.py check $(REPORT_ARGS) --report $(REPORT)

rebaseline: run
	$(PYTHON) report.py rebaseline $(REPORT_ARGS)

clean:
	rm -rf $(OUT) $(VENV_DIR)
	-cd $(RUST_DIR) && $(CARGO) clean

.PHONY: all venv build-rust run check rebaseline clean
