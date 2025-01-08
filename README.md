Coq-Combi
=========

Formalisation of (algebraic) combinatorics in Coq/MathComp.

[![Nix CI for coq8.18-mc2.3.0](https://github.com/math-comp/Coq-Combi/actions/workflows/nix-action-coq8.18-mc2.3.0.yml/badge.svg)](https://github.com/math-comp/Coq-Combi/actions/workflows/nix-action-coq8.18-mc2.3.0.yml) [![Nix CI for coq8.19-mc2.3.0](https://github.com/math-comp/Coq-Combi/actions/workflows/nix-action-coq8.19-mc2.3.0.yml/badge.svg)](https://github.com/math-comp/Coq-Combi/actions/workflows/nix-action-coq8.19-mc2.3.0.yml) [![Nix CI for coq8.20-mc2.3.0](https://github.com/math-comp/Coq-Combi/actions/workflows/nix-action-coq8.20-mc2.3.0.yml/badge.svg)](https://github.com/math-comp/Coq-Combi/actions/workflows/nix-action-coq8.20-mc2.3.0.yml)

Authors
========================================================================

Florent Hivert <Florent.Hivert@lisn.fr>

Contributors:

- Thibaut Benjamin (representation theory of the symmetric groups)
- Jean Christophe Filliâtre (Why3 implementation)
- Christine Paulin (SSreflect binding for ALEA + hook length formula)
- Olivier Stietel (hook length formula)
- Cyril Cohen (MathComp compatibility + nix)

This library was supported by additional discussions with:

- Kazuhiko Sakaguchi (port on MathComp2 / Hierarchy Builder)
- Georges Gonthier
- Assia Mahoubi
- Pierre Yves Strub
- the SSReflect mailing list

The project was transferred to mathcomp on 2021-10-20.

Contents
========================================================================


* basic **theory of symmetric functions** including

  - *Schur function* and *Kostka numbers* and the equivalence of the
    combinatorial and algebraic (Jacobi) definition of Schur polynomials

  - the classical bases, *Newton formulas* and various basis changes

  - the scalar product and the *Cauchy formula*

* the **Littlewood-Richardson** rule using Schützenberger approach, it includes

  - the *Robinson-Schensted* correspondence

  - the construction of the *plactic monoïd* using *Greene invariants*

  - the *Littlewood-Richardson* and *Pieri* rules using the combinatorial
    (tableau) definition of Schur polynomials.

  After A. Lascoux, B. Leclerc and J.-Y. Thibon, "The Plactic Monoid" in
  Lothaire, M. (2011), Algebraic combinatorics on words, Cambridge University
  Press With variant described in G. Duchamp, F. Hivert, and J.-Y. Thibon,
  Noncommutative symmetric functions VI. Free quasi-symmetric functions and
  related algebras. Internat. J. Algebra Comput. 12 (2002), 671–717.

* the **Murnaghan-Nakayama** rule for converting power sum to Schur function,
  it includes

  - two recursive implementations building the tableau upward or downward

  - a skew version multiplying a Schur function by a power sum expanding the
    result on Schur functions.

* the **character theory of the symmetric Groups**. We do not use
  representations but rather goes as fast as possible to Frobenius
  isomorphism and then uses computations with symmetric polynomials. It includes

  - *cycle types* for permutations (together with Thibaut Benjamin)

  - The tower structure and the *restriction and induction formulas* for class
    indicator (together with Thibaut Benjamin)

  - the structure of the *centralizer* of a permutation

  - Young character and *Young Rule*

  - the theory of Frobenius characteristic and *Frobenius character formula*

  - the *Murnaghan-Nakayama* rule for evaluating irreducible characters

  - the *Littlewood-Richardson* rule for inducing irreducible characters

* the **Hook-Length Formula** for standard Young tableaux
  (together with Christine Paulin and Olivier Stietel). We follow closely

   Greene, C., Nijenhuis, A. and Wilf, H. S. (1979) A probabilistic proof of a
   formula for the number of Young tableaux of a given shape. Adv. in
   Math. 31, 104–109.

* the **Erdös Szekeres theorem** about increassing and decreassing subsequences

   from Greene's invariants theorem.

* various **Combinatorial objects** including

  - integer partitions and compositions, together with Young's and dominance
    lattices
  - skew partition, horizontal, vertical and ribbon border strip
  - tableaux, standard tableaux, skew tableaux
  - subsequences, integer vectors
  - standard words, permutations and the standardization map
  - Yamanouchi word
  - binary trees, Dyck words and Catalan numbers
  - set partition and refinement order

* the **Coxeter presentation of the symmetric group**.

  We formalize:

  - presentation of the symmetric group generated by elementary
    transpositions
  - Matsumoto theorem saying that two reduced words give the same permutation
    iff they are equivalent under braid relations
  - the Coxeter length and the inversion set
  - the dual Lehmer code of a permutation
  - the weak permutohedron lattice

* the **factorization** of the Vandermonde determinant as the product
  of differences.

* the **Tamari lattice** on binary trees.

* the formula for **Catalan numbers** counting binary trees and Dyck words.

  I use a bijective proof using rotations. There is a generating function
  proof available in https://github.com/hivert/FormalPowerSeries which I plan
  to merge here at some points.

Documentation
========================================================================

* The [documentation](https://math-comp.github.io/combi/1.0.0/toc.html) is now
  complete ! with the 
  [dependancy graph](https://math-comp.github.io/combi/1.0.0/index.html).

* A
  [presentation](https://github.com/math-comp/Coq-Combi/raw/master/doc/Talk-CRM/CRM.pdf)
  given at "[Algebra and combinatorics at LaCIM](http://www.crm.umontreal.ca/2018/Algebre18/index_e.php), a conference
  for the 50th anniversary of the CRM", September 24-28, 2018, Montreal,
  Quebec, Canada. This presentation is targeted at combinatorialist.

* Another
  [presentation](https://github.com/math-comp/Coq-Combi/raw/master/doc/Talk/INRIA.pdf)
  given at [Specfun](https://specfun.inria.fr/seminar/) Inria seminar, march
  2015. This presentation is targeted at proof-assistant specialist.

Various unstable/unfinished experiments:
========================================

* a **Why3 certified implementation** of the LR-Rule
  (together with Jean Christophe Filliâtre).
  See the [Why3 branch on Github](https://github.com/math-comp/Coq-Combi/tree/Why3).

* Poset.
  See the [posets branch on Github](https://github.com/math-comp/Coq-Combi/tree/posets).

Installation
========================================================================

This library is based on

* [SSReflect/MathComp 2](https://github.com/math-comp/math-comp)
  Library version 2.3.0 or more recent.

* For MathComp 2.2.0, use the [MathComp-2.2.0 branch](https://github.com/math-comp/Coq-Combi/tree/MathComp-2.2.0)

Here are the Opam packages I'm using
```
coq-hierarchy-builder        1.8.0
coq-mathcomp-ssreflect       2.3.0
coq-mathcomp-algebra         2.3.0
coq-mathcomp-field           2.3.0
coq-mathcomp-fingroup        2.3.0
coq-mathcomp-character       2.3.0
coq-mathcomp-multinomials    2.3.0
```
