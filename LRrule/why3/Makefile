OCAMLLIB= why3__BuiltIn__BuiltIn.ml \
 int__Int.ml \
 why3__Prelude__Prelude.ml \
 ref__Ref.ml \
 ref__Refint.ml \
 array__Array.ml

EXTRACT=lrrule__LRrule.ml

OPAM:=~/.opam/$(shell opam switch show)/lib

test_lrrule: $(EXTRACT) test_lrrule.ml
	ocamlopt -o $@ -g -annot -I $(OPAM)/zarith -I ~/why3/lib/why3 zarith.cmxa why3extract.cmxa $(OCAMLLIB) $(EXTRACT) test_lrrule.ml

$(EXTRACT):
	why3 extract -D ocaml64 -L . -T lrrule.LRrule -o .

clean:
	rm -f *~ *.cm* *.o *.annot
	rm -f *.bak test_lrrule
	rm -f why3__*.ml
	rm -f array__*.ml int__*.ml map__*.ml ref__*.ml
