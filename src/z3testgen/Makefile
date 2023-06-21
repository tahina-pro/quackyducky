ROOT=Z3TestGen.fst

EVERPARSE_HOME=$(realpath ../..)

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    # fstar.exe not found in PATH, assuming Everest source tree
    FSTAR_HOME=$(realpath $(EVERPARSE_HOME)/../FStar)
  else
    # fstar.exe found in PATH, assuming directory ending with /bin
    FSTAR_HOME=$(realpath $(dir $(FSTAR_EXE))/..)
  endif
endif
export FSTAR_HOME

FSTAR_OPTIONS=--already_cached 'Prims FStar' $(OTHERFLAGS)

FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS)

all: test

EVERPARSE_Z3TESTGEN_ROOT=Z3TestGen.exe
EVERPARSE_Z3TESTGEN=$(EVERPARSE_HOME)/bin/$(EVERPARSE_Z3TESTGEN_ROOT)

.PHONY: all test build clean

.depend: $(wildcard *.fst *.fsti)
	$(FSTAR) --odir ocaml/generated --dep full $(ROOT) --extract '* -Prims -FStar' > $@.tmp
	mv $@.tmp $@

include .depend

$(EVERPARSE_Z3TESTGEN): $(ALL_ML_FILES) $(filter-out %~,$(wildcard ocaml/*.ml*))
	+$(MAKE) -C ocaml
	cp ocaml/_build/default/$(EVERPARSE_Z3TESTGEN_ROOT) $@
	chmod +w $@ # because dune produces read-only executables. A cleaner alternative would be `dune install`, but that requires declaring a public_name for the executable, which in turn requires creating a package.opam file for recent dune versions

build: $(EVERPARSE_Z3TESTGEN)

test: build
	$(EVERPARSE_Z3TESTGEN)

%.checked:
	$(FSTAR) $< --cache_checked_modules
	touch $@

%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir ocaml/generated

clean:
	+$(MAKE) -C ocaml clean
	rm -rf *.checked *~ .depend* $(EVERPARSE_Z3TESTGEN)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
