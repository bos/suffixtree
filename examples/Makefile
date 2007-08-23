example-objs := \
	tiny \
	UniqueMatch.o

ghc := ghc

examples: inplace $(example-objs)

inplace:
	$(MAKE) -C .. inplace

tiny: Tiny.hs
	$(ghc) --make -o $@ $<

%.o: %.hs
	$(ghc) -c -o $@ $<

clean:
	-rm -f $(example-objs) *.hi *.o
