Coq-Combi
=========

Formalisation of (algebraic) combinatorics in Coq.

Authors
========================================================================

Florent Hivert <Florent.Hivert@lri.fr>

Contributors:

- Jean Christophe Filliâtre (Why3 implementation)
- Christine Paulin (ALEA + hook length formula)
- Olivier Stietel (hook length formula)

This library was supported by additional discussions with:

- Assia Mahoubi
- Pierre Yves Strub
- the SSReflect mailing list

Contents
========================================================================

* the **Littlewood-Richardson** rule using Schützeberger approach, it includes

  - the *Robinson-Schensted* correspondance

  - the construction of the *plactic monoïd*

  - the equivalence of the combinatorial and algebraic (Jacobi) definition of
    *Schur functions*

  - the *Littlewood-Richardson* and *Pieri* rules

  After A. Lascoux, B. Leclerc and J.-Y. Thibon, "The Plactic Monoid" in
  Lothaire, M. (2011), Algebraic combinatorics on words, Cambridge University
  Press With variant described in G. Duchamp, F. Hivert, and J.-Y. Thibon,
  Noncommutative symmetric functions VI. Free quasi-symmetric functions and
  related algebras. Internat. J. Algebra Comput. 12 (2002), 671–717.

* the **Hook-Length Formula** for standard Young tableaux
  (toghether with Christine Paulin and Olivier Stietel)

  After Greene–Nijenhuis–Wilf proof, Discrete Math. 51 (1984), 101–108.

* the **Erdös Szekeres theorem** about increassing and decreassing subsequences

* various **Combinatorial objects** including

  - totally and partially ordered types,
  - partitions,
  - tableaux, standard tableaux, skew tableaux,
  - subsequences, integer vectors,
  - standard words and permutations,
  - Yamanouchi words

*  the **Coxeter presentation of the symmetric group**.

*  the **factorization** of the Vandermonde determinant as the product of differences.

*  bijection m-trees <-> m-dyck words.
   See the [trees branch on Github](https://github.com/hivert/Coq-Combi/tree/trees).

In progress:

*  a **Why3 certified implementation** of the LR-Rule
   (together with Jean Christophe Filliâtre).
   See the [Why3 branch on Github](https://github.com/hivert/Coq-Combi/tree/Why3).

More unstable stuff:

*  Poset.
   See the [posets branch on Github](https://github.com/hivert/Coq-Combi/tree/posets).

*  Formal Power series. See the series branch on Github.
   See the [series branch on Github](https://github.com/hivert/Coq-Combi/tree/series).

* Set-partitions 
  See the [SetPartition branch on Github](https://github.com/hivert/Coq-Combi/tree/SetPartition).

Documentation
========================================================================

The [documentation](http://hivert.github.io/Coq-Combi/) is currently in progress.

Installation
========================================================================

This library is based on SSReflect/MathComp Library version 1.5.

It needs an [extended version](https://github.com/hivert/multinomials-ssr)
of Pierre-Yves Strub [Multinomials](https://github.com/strub/multinomials-ssr)
library.


Note: A standalone version of the proof of the Littlewood-Richardson rule not
using [Multinomials] is available in the [Legacy
branch](https://github.com/hivert/Coq-Combi/tree/Legacy). It only includes a
bare proof of the LR-rule without formalizing anything on multivariate
polynomials. The proofs given here would be valid for any elements in any
commutative rings.

