all: verify-all

ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME:=$(realpath ../../..)
endif

ifndef FSTAR_HOME
  FSTAR_HOME=$(realpath $(EVERPARSE_HOME)/../FStar)
endif
FSTAR_EXE:=$(FSTAR_HOME)/bin/fstar.exe

ifeq (,$(KRML_HOME))
  KRML_HOME:=$(realpath $(EVERPARSE_HOME)/../karamel)
endif
KRMLLIB:=$(KRML_HOME)/krmllib
LOWPARSE_HOME:=../../lowparse
INCLUDE_KRML:=--include $(KRMLLIB) --include $(KRMLLIB)/obj

INCLUDE_PATHS:=$(LOWPARSE_HOME) ..

ALREADY_CACHED := --already_cached *,-CBOR
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --cmi

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

CBOR_FILES:=$(wildcard *.fst *.fsti)

clean:
	rm -rf *.checked *.source .depend .depend.tmp out *.krml *.o

.depend: $(CBOR_FILES)
	$(FSTAR) --dep full $(CBOR_FILES) --extract 'krml:*,-FStar.Tactics' > $@.tmp
	mv $@.tmp $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

%.krml:
	$(FSTAR) --codegen krml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

KRML := $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -skip-linking \
	 $(KRML_OPTS) \
	 -warn-error '@2@4@15'

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
