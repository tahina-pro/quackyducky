all: FStar.do karamel.do pulse.do submodules

export ADMIT=1

export EVERPARSE_OPT_PATH=$(realpath .)

export FSTAR_EXE  := $(EVERPARSE_OPT_PATH)/FStar/bin/fstar.exe
export KRML_HOME  := $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
export HACL_HOME := $(EVERPARSE_OPT_PATH)/hacl-star
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

include env.Makefile

submodules.tmp:
	git submodule init
	git submodule update
	touch $@

submodules: submodules.tmp z3 karamel pulse everest hacl-star
	touch $@

everest:
	rm -rf $@ $@.tmp
	git clone https://github.com/project-everest/$@.git $@.tmp
	mv $@.tmp $@

hacl-star:
	rm -rf $@ $@.tmp
	git clone https://github.com/hacl-star/$@.git $@.tmp
	mv $@.tmp $@

FStar.do: submodules.tmp
	+$(MAKE) -C $(basename $@) 1 ADMIT=1

z3: submodules.tmp
	rm -rf $@ $@.tmp
	mkdir -p $@.tmp
	FStar/.scripts/get_fstar_z3.sh $(realpath .)/$@.tmp
	mv $@.tmp $@

karamel:
	rm -rf $@ $@.tmp
	git clone https://github.com/FStarLang/$@.git $@.tmp
	mv $@.tmp $@

karamel.do: FStar.do karamel z3
	+$(MAKE) -C $(basename $@)

pulse:
	rm -rf $@ $@.tmp
	git clone https://github.com/FStarLang/$@.git $@.tmp
	mv $@.tmp $@

pulse.do: FStar.do pulse z3
	+$(MAKE) -C $(basename $@) ADMIT=1

.PHONY: all %.do
