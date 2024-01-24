ROOT=Hashing.Hash.fst

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

INCLUDE_PATHS=
OTHERFLAGS?=
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS) $(EVERPARSE_HOME)/src/3d/prelude) --already_cached '*,'

all: extract-hashchk

.PHONY: all extract-hashchk

OUTPUT_DIR=hashchk/generated

%.fs:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen FSharp --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir $(OUTPUT_DIR)

hashchk.depend: $(wildcard *.fst *.fsti) Version.fst
	$(FSTAR) --odir $(OUTPUT_DIR) --dep full $(ROOT) --extract '* -Prims -FStar' --output_deps_to $@

include hashchk.depend

extract-hashchk: $(ALL_FS_FILES)
