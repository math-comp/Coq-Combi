include Makefile.coq


.PHONY: test test.byte

test: test_lrrule
	OCAMLRUNPARAM=bt ./test_lrrule 3 2 1 - 2 1 0 - 2 1 0
	OCAMLRUNPARAM=bt ./test_lrrule 5 4 1 - 3 1 0 - 3 2 1 0
	OCAMLRUNPARAM=bt ./test_lrrule 5 4 3 2 - 3 3 1 0 - 4 2 1 0
	time ./test_lrrule 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 0 0 0 - 7 6 5 5 4 3 2 1 0
	# 268484

test.byte: test_lrrule.byte
	./test_lrrule.byte 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 0 0 0 - 7 6 5 5 4 3 2 1

OCAMLLIB= why3__BuiltIn__BuiltIn.ml \
 int__Int.ml \
 why3__Prelude__Prelude.ml \
 ref__Ref.ml \
 ref__Refint.ml \
 array__Array.ml

EXTRACT=lrrule__LRrule.ml

OPAM:=~/.opam/$(shell opam switch show)/lib
LIBDIR:=$(shell why3 --print-libdir)/why3

test_lrrule: $(EXTRACT) debug.ml test_lrrule.ml
	ocamlopt -o $@ -g -annot -I $(OPAM)/zarith zarith.cmxa -I $(LIBDIR) why3extract.cmxa $(OCAMLLIB) debug.ml $(EXTRACT) test_lrrule.ml

test_lrrule.byte: $(EXTRACT) debug.ml test_lrrule.ml
	ocamlc -o $@ -g -annot -I $(OPAM)/zarith zarith.cma -I $(LIBDIR) why3extract.cma $(OCAMLLIB) debug.ml $(EXTRACT) test_lrrule.ml

$(EXTRACT): lrrule.mlw
	why3 extract -D ocaml64 -L . -T lrrule.LRrule -o .

# proof of equivalence
Spec.v: lrrule.mlw
	why3 realize -D coq-ssreflect -L . -T lrrule.Spec -o .
	sed -e "s/2%Z/2%:Z/g" -i Spec.v

clean:
	rm -f *~ *.cm* *.o *.annot
	rm -f *.bak test_lrrule test_lrrule.byte lrrule__LRrule.ml
	rm -f why3__*.ml
	rm -f array__*.ml int__*.ml map__*.ml ref__*.ml
