#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.4pl5     ##
#############################################################################

#
# This Makefile was generated by the command line :
# coq_makefile -R theories Combi theories/**/*.v
#

.DEFAULT_GOAL := all

# 
# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

COQLIBS?= -R theories Combi -R 3rdparty/ALEA ALEA
COQDOCLIBS?=-R theories Combi -R 3rdparty/ALEA ALEA
COQEXTLIBS:=--external http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/ MathComp \
            --external http://ssr.msr-inria.inria.fr/doc/ssreflect-1.5/ Ssreflect

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8 --lib-subtitles --no-lib-name
COQC?="$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:= theories/Basic/combclass.v\
  theories/Basic/congr.v\
  theories/Basic/ordcast.v\
  theories/Basic/ordtype.v\
  theories/Combi/partition.v\
  theories/Combi/permuted.v\
  theories/Combi/shape.v\
  theories/Combi/skewtab.v\
  theories/Combi/stdtab.v\
  theories/Combi/std.v\
  theories/Combi/subseq.v\
  theories/Combi/tableau.v\
  theories/Combi/vectNK.v\
  theories/Combi/Yamanouchi.v\
  theories/SSRcomplements/bigallpairs.v\
  theories/SSRcomplements/rat_coerce.v\
  theories/SSRcomplements/sorted.v\
  theories/SSRcomplements/tools.v\
  theories/Erdos_Szekeres/Erdos_Szekeres.v\
  theories/HookFormula/Qmeasure.v\
  theories/HookFormula/RSident.v\
  theories/HookFormula/distr.v\
  theories/HookFormula/hook.v\
  theories/HookFormula/recyama.v\
  theories/MPoly/antisym.v\
  theories/MPoly/sympoly.v\
  theories/MPoly/Schur_basis.v\
  theories/LRrule/extract.v\
  theories/LRrule/Greene_inv.v\
  theories/LRrule/Greene.v\
  theories/LRrule/implem.v\
  theories/LRrule/plactic.v\
  theories/LRrule/Schensted.v\
  theories/LRrule/freeSchur.v\
  theories/LRrule/shuffle.v\
  theories/LRrule/stdplact.v\
  theories/LRrule/therule.v\
  theories/LRrule/Yam_plact.v\
  theories/Poset/poset.v
  theories/SymGroup/symgroup.v\
  3rdparty/ALEA/Ccpo.v\
  3rdparty/ALEA/Misc.v\

-include $(addsuffix .d,$(VFILES))
.SECONDARY: $(addsuffix .d,$(VFILES))

VOFILES:=$(VFILES:.v=.vo)
VOFILES1=$(patsubst theories/%,%,$(filter theories/%,$(VOFILES)))
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) 

spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(COQEXTLIBS) $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES) depend.dot
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(COQEXTLIBS) $(VFILES)
	dot -Tpng -o html/depend.png -Tcmapx -o html/depend.map depend.dot
	dot -Tsvg -o html/depend.svg depend.dot
	rm -f html/index_lib.html
	mv html/index.html html/index_lib.html
	cat scripts/header.html html/depend.map scripts/footer.html > html/index.html


all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all opt byte archclean clean install userinstall depend html validate html gallinahtml

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install:
	cd "theories"; for i in $(VOFILES1); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Combi/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Combi/$$i; \
	done

install-doc:
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/Combi/html
	for i in html/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/Combi/$$i;\
	done

clean:
	rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf depend depend.dot depend.pdf html scripts/ocamldot scripts/ocamldot.ml scripts/ocamldot.cmi scripts/ocamldot.cmo mlihtml

archclean:
	rm -f *.cmx *.o

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

###################
#                 #
# Implicit rules. #
#                 #
###################

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*


#COQDEFS := --language=none -r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Notation\|Proposition\|Module[[:space:]]+Import\|Module\)[[:space:]]+\([[:alnum:]'\''_]+\)/\2/'
#TAGS: $(VFILES)
#	etags $(COQDEFS) $(VFILES)
TAGS: $(VFILES)
	coqtags $(VFILES)

depend.d: $(VFILES:.v=.v.d)
	rm -f depend
	cat $(VFILES:.v=.v.d) | sed -e 's/[^ ]*glob//g' | sed -e 's/[^ ]*beautified//g' > depend.d

scripts/ocamldot: scripts/ocamldot.mll
	ocamllex scripts/ocamldot.mll
	ocamlc -o $@ scripts/ocamldot.ml

depend.dot: depend.d scripts/ocamldot
	rm -f depend.dot
	scripts/ocamldot depend.d > depend.dot
	sed -i -e "s/Theories/Combi/g" -e "s/\//./g" depend.dot

depend.pdf: depend.dot
	rm -f depend.pdf
	dot -Tpdf depend.dot > depend.pdf
