include Makefile.coq


.PHONY: test test.byte

test: lrrule.opt
	OCAMLRUNPARAM=bt ./lrrule.opt 3 2 1 - 2 1 0 - 2 1 0
	OCAMLRUNPARAM=bt ./lrrule.opt 5 4 1 - 3 1 0 - 3 2 1 0
	OCAMLRUNPARAM=bt ./lrrule.opt 5 4 3 2 - 3 3 1 0 - 4 2 1 0
	time ./lrrule.opt 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 0 0 0 - 7 6 5 5 4 3 2 1 0
	# 268484

test.byte: lrrule.byte
	time ./lrrule.byte 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 0 0 0 - 7 6 5 5 4 3 2 1 0

OCAMLLIB= why3__BuiltIn__BuiltIn.ml \
 int__Int.ml \
 why3__Prelude__Prelude.ml \
 ref__Ref.ml \
 ref__Refint.ml \
 array__Array.ml

OPAM:=~/.opam/$(shell opam switch show)/lib
LIBDIR:=$(shell why3 --print-libdir)/why3
WHY3EXTRACT=-I $(OPAM)/zarith zarith.cmxa -I $(LIBDIR)

lrrule.opt: lrrule__LRrule.ml debug.ml test_lrrule.ml
	ocamlopt -o $@ -g -annot $(WHY3EXTRACT) why3extract.cmxa $(OCAMLLIB) debug.ml lrrule__LRrule.ml test_lrrule.ml

lrrule.byte: lrrule__LRrule.ml debug.ml test_lrrule.ml
	ocamlc -o $@ -g -annot $(WHY3EXTRACT) why3extract.cma $(OCAMLLIB) debug.ml $(EXTRACT) test_lrrule.ml

lrrule_ocaml.opt: lrrule_ocaml.ml
	ocamlopt -o $@ $^

lrrule__LRrule.ml: lrrule.mlw
	why3 extract -D ocaml64 -L . -T lrrule.LRrule -o .

lrrule_unsafe.opt: lrrule.mlw test_lrrule_unsafe.ml
	why3 extract -D ocaml-unsafe-int -L . -T lrrule.LRrule -o .
	ocamlopt -o $@ $(OCAMLLIB) lrrule__LRrule.ml test_lrrule_unsafe.ml

OCAMLLIB64= mach__int__Refint63.ml

lrrule64.opt: lrrule64__LRrule.ml test_lrrule64.ml
	ocamlopt -o $@ $(WHY3EXTRACT) why3extract.cmxa $(OCAMLLIB64) lrrule64__LRrule.ml test_lrrule64.ml

lrrule64__LRrule.ml: lrrule64.mlw
	why3 extract -D ocaml64 -L . -T lrrule64.LRrule -o .

# proof of equivalence
Spec.v: lrrule.mlw
	why3 realize -D coq-ssreflect -L . -T lrrule.Spec -o .

clean::
	rm -f *~ *.cm* *.o *.annot
	rm -f *.bak test_lrrule test_lrrule.byte lrrule__LRrule.ml
	rm -f why3__*.ml
	rm -f array__*.ml int__*.ml map__*.ml ref__*.ml
