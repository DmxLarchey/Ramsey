## Ramsey's theorem in Type Theory

### Copyright

```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*                                                            *)
(*                 [*] Affiliation LORIA -- CNRS              *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)
```

### What is this repository for? 

* This repository contains a constructive Coq implementation of
  the [direct and abstract proof of Ramsey's 
  theorem](http://www.cse.chalmers.se/~coquand/ramsey2.pdf)
  by T. Coquand. The corresponding file is [src/ramsey_paper.v]
  and it show the following result is the distributive
  lattice `(Σ,⊑,⊔,⊓,⊥,⊤)` with an operator 
  `op : X -> Σ -> Σ` such that `op x` is a lattice
  morphism for any `x`
 
```coq

Inductive US a : Prop :=
  | in_US_0 : (∀x, a⋅x ≡ a)  -> US a
  | in_US_1 : (∀x, US (a⋅x)) -> US a.

Inductive UF a : Prop := 
  | in_UF_0 : a ≡ ⊤           -> UF a
  | in_UF_1 : (∀x, UF (a[x])) -> UF a.

```

### Bibliography

* The draft paper [A direct proof of Ramsey’s Theorem](http://www.cse.chalmers.se/~coquand/ramsey2.pdf) by Thierry Coquand.
* The paper [An intuitionistic version of Ramsey's Theorem and its use in Program 
Termination](https://doi.org/10.1016/j.apal.2015.08.002) by Stefano Berardi and Silvia Steila.

### What does it contains

### How do I set it up? ###

* This should compile with Coq 8.6+ with `cd src; make af.vo hwf.vo`.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)

