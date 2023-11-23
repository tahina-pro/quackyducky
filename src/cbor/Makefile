all: impl
.PHONY: all

ifndef FSTAR_HOME
  FSTAR_EXE:=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=$(realpath ../../../FStar)
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE:=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KRML_HOME
  KRMLLIB:=$(shell ocamlfind query karamel)
  ifneq ($(.SHELLSTATUS),0)
    KRML_HOME=$(realpath ../../../karamel)
  endif
endif
ifdef KRML_HOME
  KRMLLIB:=$(KRML_HOME)/krmllib
endif
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

ALREADY_CACHED = --already_cached *,-CBOR
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --cmi

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

CBOR_FILES=$(wildcard *.fst *.fsti)

.PHONY: clean
clean:
	rm -rf *.checked *.source .depend .depend.tmp out *.krml *.o

.depend: $(CBOR_FILES)
	$(FSTAR) --dep full $(CBOR_FILES) --extract 'krml:*,-FStar.Tactics' > $@.tmp
	mv $@.tmp $@

include .depend

.PHONY: verify-all
verify-all: $(ALL_CHECKED_FILES)

.PHONY: impl
impl: verify-all
	+$(MAKE) -C $@

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: %.fst-in %.fsti-in
%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
