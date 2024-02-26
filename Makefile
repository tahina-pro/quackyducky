all: quackyducky lowparse 3d

lowparse:
	+$(MAKE) -C src/lowparse

3d: lowparse
	+$(MAKE) -C src/3d

quackyducky:
	+$(MAKE) -C src/qd

gen-test: quackyducky
	-rm tests/unit/*.fst tests/unit/*.fsti || true
	bin/qd.exe -odir tests/unit tests/unittests.rfc
	bin/qd.exe -low -odir tests/unit tests/bitcoin.rfc

lowparse-unit-test: lowparse
	+$(MAKE) -C tests/lowparse

3d-unit-test: 3d
	+$(MAKE) -C src/3d test

3d-doc-test: 3d
	+$(MAKE) -C doc 3d

3d-test: 3d-unit-test 3d-doc-test

lowparse-bitfields-test: lowparse
	+$(MAKE) -C tests/bitfields

.PHONY: steel
steel: lowparse
	+$(MAKE) -C src/lowparse/steel

steel-unit-test: steel
	+$(MAKE) -C tests/steel

cbor: lowparse
	+$(MAKE) -C src/cbor

.PHONY: steel-test
steel-test: steel-unit-test cbor

lowparse-test: lowparse-unit-test lowparse-bitfields-test

quackyducky-unit-test: gen-test lowparse
	+$(MAKE) -C tests/unit

quackyducky-sample-test: quackyducky lowparse
	+$(MAKE) -C tests/sample

quackyducky-sample-low-test: quackyducky lowparse
	+$(MAKE) -C tests/sample_low

quackyducky-sample0-test: quackyducky lowparse
	+$(MAKE) -C tests/sample0

quackyducky-test: quackyducky-unit-test quackyducky-sample-test quackyducky-sample0-test quackyducky-sample-low-test

test: all lowparse-test quackyducky-test 3d-test steel-test

ci: test

clean-3d:
	+$(MAKE) -C src/3d clean

clean-lowparse:
	+$(MAKE) -C src/lowparse clean

clean-quackyducky:
	+$(MAKE) -C src/qd clean

clean: clean-3d clean-lowparse clean-quackyducky
	rm -rf bin

.PHONY: all gen verify test gen-test clean quackyducky lowparse lowparse-test quackyducky-test lowparse-fstar-test quackyducky-sample-test quackyducky-sample0-test quackyducky-unit-test package 3d 3d-test lowparse-unit-test lowparse-bitfields-test steel-unit-test release everparse 3d-unit-test 3d-doc-test 3d-doc-ci 3d-ci ci clean-3d clean-lowparse clean-quackyducky

release:
	+src/package/release.sh

# Windows binary package
package:
	+src/package/package.sh -zip

# Windows binary package
package-noversion:
	+src/package/package.sh -zip-noversion

everparse:
	+src/package/package.sh -make

# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

lowparse-fstar-test:
	+$(MAKE) -C src/lowparse fstar-test
