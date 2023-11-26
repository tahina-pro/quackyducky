# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify-all

ifndef EVERPARSE_HOME
  EVERPARSE_HOME=$(realpath ../../..)
endif

ifndef FSTAR_HOME
  FSTAR_EXE:=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=$(realpath $(EVERPARSE_HOME)/../FStar)
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE:=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KRML_HOME
  KRMLLIB:=$(shell ocamlfind query karamel)
  ifneq ($(.SHELLSTATUS),0)
    KRML_HOME=$(realpath $(EVERPARSE_HOME)/../karamel)
  endif
endif
ifdef KRML_HOME
  KRMLLIB:=$(KRML_HOME)/krmllib
endif
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

ifndef STEEL_HOME
  STEEL_HOME=$(realpath $(EVERPARSE_HOME)/../steel)
endif
INCLUDE_STEEL=$(STEEL_HOME)/lib/steel $(STEEL_HOME)/lib/steel/pulse $(STEEL_HOME)/share/steel/examples/pulse/lib $(STEEL_HOME)/share/steel/examples/pulse/_output/cache
FSTAR_STEEL_OPTIONS=$(addprefix --include , $(INCLUDE_STEEL)) --load_cmxs steel

INCLUDE_PATHS += ..
ALREADY_CACHED = --already_cached *,-LowParse.Pulse
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) $(FSTAR_STEEL_OPTIONS)

LOWPARSE_FILES=$(wildcard *.fst) $(wildcard *.fsti)

clean:
	rm -rf *.checked *.source .depend*

.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@.tmp
	mv $@.tmp $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in fstar-test
