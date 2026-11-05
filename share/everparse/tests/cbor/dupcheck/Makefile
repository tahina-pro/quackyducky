# Unverified prototypes of duplicate-map-key checks for nondet CBOR, with
# differential tests against the verified EverCBOR nondet validator and
# benchmarks. See results.md.
#
#   make test        correctness (differential + random), no-malloc check
#   make test-asan   same, with -fsanitize=address,undefined
#   make bench       benchmarks -> bench.csv, then fit.py -> bench_fit.md

EVERPARSE_HOME ?= $(realpath ../../../../..)
NONDET_C ?= $(EVERPARSE_HOME)/src/cbor/pulse/nondet/c

CC ?= cc
OPT ?= -O2
WARN = -Wall -Wextra -Wvla -Werror
CFLAGS_DUP = $(OPT) $(WARN) -std=c11
CFLAGS_VER = $(OPT) -I $(NONDET_C) -I $(EVERPARSE_HOME)/include \
             -I $(EVERPARSE_HOME)/include/everparse -I .
# Any call to the allocator during a check aborts (see test_dupcheck.c).
WRAP = -Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc,--wrap=free

DUP_SRC = canon.c dupcheck_sort.c dupcheck_hash.c siphash.c
DUP_HDR = dupcheck.h dupcheck_internal.h

all: test bench

.PHONY: all test test-asan bench clean stack-usage

out/%.o: %.c $(DUP_HDR)
	@mkdir -p out
	$(CC) $(CFLAGS_DUP) $(EXTRA) -c -o $@ $<

out/verified_wrap.o: verified_wrap.c verified_wrap.h
	@mkdir -p out
	$(CC) $(CFLAGS_VER) $(EXTRA) -w -c -o $@ $<

DUP_OBJ = $(patsubst %.c,out/%.o,$(DUP_SRC))

out/test_dupcheck.exe: test_dupcheck.c gen.h $(DUP_OBJ) out/verified_wrap.o
	$(CC) $(CFLAGS_DUP) $(EXTRA) -Wno-unused-function -o $@ $< $(DUP_OBJ) out/verified_wrap.o $(WRAP)

out/bench_dupcheck.exe: bench_dupcheck.c gen.h $(DUP_OBJ) out/verified_wrap.o
	$(CC) $(CFLAGS_DUP) $(EXTRA) -Wno-unused-function -o $@ $< $(DUP_OBJ) out/verified_wrap.o -lm

test: out/test_dupcheck.exe
	./out/test_dupcheck.exe

test-asan:
	$(MAKE) clean
	$(MAKE) test OPT="-O1 -g" EXTRA="-fsanitize=address,undefined -fno-sanitize-recover=all"
	$(MAKE) clean

bench: out/bench_dupcheck.exe
	./out/bench_dupcheck.exe > bench.csv
	python3 fit.py bench.csv > bench_fit.md

stack-usage:
	@mkdir -p out
	$(CC) $(CFLAGS_DUP) -fstack-usage -c -o out/su.o canon.c
	$(CC) $(CFLAGS_DUP) -fstack-usage -c -o out/su2.o dupcheck_hash.c
	cat out/su.su out/su2.su; rm -f out/su*

clean:
	rm -rf out
