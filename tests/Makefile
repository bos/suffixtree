ghc := ghc
ghcflags := $(shell awk -F: '/ghc-options/{print $$2}' ../suffixtree.cabal)

tests:
	runhaskell SuffixCheck

inplace:
	cd .. && $(ghc) $(ghcflags) --make Data/*.hs
