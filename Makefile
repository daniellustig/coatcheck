.PHONY: all clean doc debug profile web

all:
	-rm src/PipeGraph
	-$(MAKE) -C src
	cd src && ln -s . PipeGraph

clean:
	$(MAKE) -C src clean

doc:
	$(MAKE) -C src doc

debug:
	$(MAKE) -C src debug

profile:
	$(MAKE) -C src profile

web:
	$(MAKE) -C src web
