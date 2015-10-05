Coq-Combi
=========

Formalisation of (algebraic) combinatorics in Coq.

Authors
========================================================================

Florent Hivert <Florent.Hivert@lri.fr>

Contributors: 

- Jean Christophe Filliâtre
- Christine Paulin 
- Olivier Stietel.

This library was supported by additional discussions with:

- Assia Mahoubi
- Pierre Yves Strub

Contents
========================================================================

* the Littlewood-Richardson rule using Schützeberger approach, it includes
  - the Robinson-Schensted correspondance
  - the construction of the plactic monoïd

  After A. Lascoux, B. Leclerc and J.-Y. Thibon, "The Plactic Monoid" in Lothaire, M. (2011), Algebraic combinatorics on words, Cambridge University Press
  With variant described in  G. Duchamp, F. Hivert, and J.-Y. Thibon, Noncommutative symmetric functions VI. Free quasi-symmetric functions and related algebras. Internat. J. Algebra Comput. 12 (2002), 671–717.


* Hook-Length Formula (toghether with Christine Paulin and Olivier Stietel)
  
  After Greene–Nijenhuis–Wilf proof, Discrete Math. 51 (1984), 101–108.

* bijection m-trees <-> m-dyck words
* the Erdös Szekeres theorem about increassing and decreassing subsequences

In progress:

* a Why3 certified implementation of the LR-Rule (together with Jean Christophe Filliâtre).

More unstable stuff:

* Poset
* Formal Power series
