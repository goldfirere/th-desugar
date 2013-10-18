WITHGHC = --with-ghc=$(HOME)/ghc-$(GHC)-build/bin/ghc
CABAL = cabal $(WITHGHC)

all: install

.PHONY: init build test install ghc-head ghc-7.6.3

init:
	$(CABAL) install --only-dependencies --enable-tests
	$(CABAL) configure $(WITHGHC) --enable-tests

build:
	$(CABAL) build

test: build
	$(CABAL) test

install: build test
	$(CABAL) install

ghc-head:
	wget --quiet -O ghc-head.tar.bz2 https://www.dropbox.com/sh/l24540a7ndwte01/u5QOAwG7DF/dist/ghc-HEAD-x86_64-unknown-linux.tar.bz2
	tar xjf ghc-head.tar.bz2
	mkdir $(HOME)/ghc-head-build
	cd ghc-7.7.* && ./configure --prefix=$(HOME)/ghc-head-build
	cd ghc-7.7.* && make install
	$(HOME)/ghc-head-build/bin/ghc --version

ghc-7.6.3:
	wget --quiet -O ghc-7.6.3.tar.bz2 https://www.dropbox.com/sh/l24540a7ndwte01/X11weT9-6q/ghc-7.6.3-x86_64-unknown-linux.tar.bz2
	tar xjf ghc-7.6.3.tar.bz2
	mkdir $(HOME)/ghc-7.6.3-build
	cd ghc-7.6.3 && ./configure --prefix=$(HOME)/ghc-7.6.3-build
	cd ghc-7.6.3 && make install
	$(HOME)/ghc-7.6.3-build/bin/ghc --version
