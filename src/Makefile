# Thanks to: http://adam.chlipala.net/cpdt/html/Large.html

MODULES := Debug Util StringUtil Instruction Graph \
  GraphvizCompressed PipeGraph FOL FOLPredicate
VS      := $(MODULES:%=%.v)
DOCS    := $(MODULES:%=../doc/PipeGraph.%.html)

.PHONY: all coq doc clean debug web

all: coq doc pipecheck

debug: Main.d.byte

profile: Main.p.native

pipecheck: Main.native
	cp Main.native pipecheck

Main.native: Main.ml PipeGraph.ml HerdGraph.ml coq BackendLinux.ml PipeGraphLinux.ml
	ocamlbuild $@

Main.p.native: Main.ml PipeGraph.ml HerdGraph.ml coq BackendLinux.ml PipeGraphLinux.ml
	ocamlbuild $@

Main.d.byte: Main.ml PipeGraph.ml HerdGraph.ml coq BackendLinux.ml PipeGraphLinux.ml
	ocamlbuild $@

PipeGraphLinux.ml: PipeGraph.ml
	rm -f PipeGraphJS.ml
	$(MAKE) -f Makefile.coq -B PipeGraph.vo
	cp PipeGraph.ml PipeGraphLinux.ml

PipeGraph.ml: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: coq $(VS)
	mkdir -p ../doc
	coqdoc --html -R . PipeGraph -d ../doc $(VS)

Makefile.coq: Makefile $(VS)
	coq_makefile -R . PipeGraph $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ocamlbuild -clean Main.native
	-rm -f pipecheck
	-rm -f PipeGraph.ml
	-rm -f PipeGraph.mli
	-rm -f Makefile.coq
	-rm -f $(DOCS)
	-rm -f ../doc/index.html
	-rm -f ../doc/coqdoc.css

web: ../html/pipecheck.js

PipeGraphJS.ml: PipeGraph.ml
	rm -f PipeGraphLinux.ml
	sed "s/BackendLinux./BackendJS./g" PipeGraph.ml > PipeGraphJS.ml
	cp PipeGraphJS.ml PipeGraph.ml

../html/pipecheck.js: BackendJS.ml PipeGraph.ml PipeGraphJS.ml
	ocamlbuild -use-ocamlfind -pkgs js_of_ocaml,js_of_ocaml.syntax -syntax camlp4o WebMain.byte
	js_of_ocaml --noinline WebMain.byte
	cp WebMain.js ../html/pipecheck.js

web-debug: ../html/pipecheck.js
	ocamlbuild -use-ocamlfind -pkgs js_of_ocaml,js_of_ocaml.syntax -syntax camlp4o WebMain.d.byte
	js_of_ocaml --pretty --noinline WebMain.d.byte
	cp WebMain.d.js ../html/pipecheck.js

