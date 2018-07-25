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
  by T. Coquand. The corresponding file is 
  [ramsey_paper.v](src/ramsey_paper.v)
  and it show the following result is the distributive
  lattice `(Σ,⊑,⊔,⊓,⊥,⊤)` with an operator 
  `op : X -> Σ -> Σ` such that `op x` is a lattice
  morphism for any `x`. We denote `op x a` by `a⋅x` as in
  the paper.

* This repository also contains applications of the abstract
  Ramsey theorem to finitary and binary relations, both
  for [*almost full relations*]((https://doi.org/10.1.1.225.3021) (`af`) and 
  for [*homogeneous well-founded relations*](https://doi.org/10.1016/j.apal.2015.08.002)
  (`hwf`).
  It contains two definitions of binary `hwf` relations: 

    * one by direct induction similar to the inductive definition of
      the `af` predicate. `R` is binary relation of type
      `R : X -> X -> Prop`.

```coq
Inductive hwf R : Prop :=
  | in_hwf_0 : (forall a b, ~ R a b) -> hwf R
  | in_hwf_1 : (forall x, hwf (R↓x)) -> hwf R
where "R ↓ x" := (fun a b => R a b /\ R b x).
```
    * one corresponding to the original definition of Berardi as
      *list extension is well-founded on `R`-homogenous lists*.
 
``coq
Inductive homogeneous : list X -> Prop :=
  | in_homogeneous_0 : homogeneous R nil
  | in_homogeneous_1 : ∀ x l, homogeneous R l -> Forall (R x) l -> homogeneous R (x::l).

Definition extends {X} (l m : list X) := exists x, l = x::m.

Definition Hwf R := well_founded (extends⬇(homogeneous R)).
```

* We show `hwf ⊆ Hwf` and also `Hwf R -> hwf R` when `R` is logically
  decidable. 

### Some more

* The following code succinctly describes the abstract
  Ramsey theorem in Coq formalism.
 
```coq
Inductive US (a : Σ) : Prop :=
  | in_US_0 : (∀x, a⋅x ≡ a)    -> US a
  | in_US_1 : (∀x, US (a⋅x))   -> US a.

Inductive UF (a : Σ) : Prop :=
  | in_UF_0 : a ≡ ⊤            -> UF a
  | in_UF_1 : (∀x, UF (a⊔a⋅x)) -> UF a.

Theorem Ramsey_lattice r s : US r -> US s -> UF r -> UF s -> UF (r⊓s).
```

  `US` stands for *ultimately stable* and means that repeated 
  applications of `op x` always leads to a fixpoint.

  `UF` stands for *ultimately full* and means that repeated
  applications of `a ↦ a⊔a⋅x` always leads to `⊤` (i.e. the full
  element of the lattice).

### Bibliography

* The draft paper [A direct proof of Ramsey’s Theorem](http://www.cse.chalmers.se/~coquand/ramsey2.pdf) by Thierry Coquand.

* The paper 
 [An intuitionistic version of Ramsey's Theorem and its use in Program Termination](https://doi.org/10.1016/j.apal.2015.08.002) 
  by Stefano Berardi and Silvia Steila.

* The paper [Stop when you are Almost-Full](https://doi.org/10.1.1.225.3021) 
  by Dimitrios Vytiniotis, Thierry Coquand and David Wahlstedt.

### What does it contains

### How do I set it up? ###

* This should compile with Coq 8.6+ with `cd src; make af.vo hwf.vo`.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)


