GHC ?= ghc
GHCFLAGS ?= -O1 -Wall -isrc -outputdir build/o

all: build/rhoref build/rhoref-test

build/rhoref: app/Main.hs src/Rho/*.hs
	@mkdir -p build
	$(GHC) $(GHCFLAGS) $(LDFLAGS) -iapp app/Main.hs -o $@

build/rhoref-test: test/Test.hs src/Rho/*.hs
	@mkdir -p build
	$(GHC) $(GHCFLAGS) $(LDFLAGS) -outputdir build/t -itest test/Test.hs -o $@

test: build/rhoref-test
	./build/rhoref-test

clean:
	rm -rf build

.PHONY: all test clean
