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

## What is this repository for? 

* This repository contains a constructive Coq implementation of
  the [direct and abstract proof of Ramsey's 
  theorem](http://www.cse.chalmers.se/~coquand/ramsey2.pdf)
  by T. Coquand. The corresponding file is 
  [ramsey_paper.v](src/ramsey_paper.v).
  It also contains some of the definitions and result of the
  [intuitionistic version of Ramsey's Theorem](https://doi.org/10.1016/j.apal.2015.08.002) 
  by S. Berardi and S. Steila.

* We apply the theorem to finitary and binary 
  [*almost full relations*](https://doi.org/10.1.1.225.3021), 
  and to finitary and binary 
  [*homogeneous well-founded relations*](https://doi.org/10.1016/j.apal.2015.08.002).
  We establish the link between the direct inductive definition of
  homogeneous well-founded and Berardi and Steila's characterization
  using the `well_founded` predicate.

* We leave some open questions regarding the generalization of
  the abstract proof to poset-indexed families of relations
  and to the proof of the *indexed Higman's theorem* leading
  to as shorter proof of *Kruskal's tree theorem* following an
  unpublished draft by T. Coquand.

### The direct and abstract proof of Ramsey's theorem

* We show the following result is a distributive
  lattice `(Σ,⊑,⊔,⊓,⊥,⊤)` with an operator 
  `op : X -> Σ -> Σ` such that `op x` is a lattice
  morphism for any `x`. We denote `op x a` by `a⋅x` as in
  the paper.

```coq
Inductive US (a : Σ) : Prop :=
  | in_US_0 : (∀x, a⋅x ≡ a)    -> US a
  | in_US_1 : (∀x, US (a⋅x))   -> US a.

Inductive UF (a : Σ) : Prop :=
  | in_UF_0 : a ≡ ⊤            -> UF a
  | in_UF_1 : (∀x, UF (a⊔a⋅x)) -> UF a.

Theorem Ramsey_lattice r s : US r -> US s -> UF r -> UF s -> UF (r⊓s).
```

* `US` stands for *ultimately stable* and means that repeated 
  applications of `op x` always leads to a fixpoint.

* `UF` stands for *ultimately full* and means that repeated
  applications of `a ↦ a⊔a⋅x` always leads to `⊤` (i.e. the full
  element of the lattice).

### Applications to finitary and binary Almost Full relations

* This repository also contains applications of the abstract
  Ramsey theorem to finitary and binary relations, both
  for  (`af`) and

### Applications to finitary and binary Homogeneous Well-founded relations

*  for 
  (`hwf`).

* It contains two definitions of binary `hwf` relations: 
  
    * one by direct induction similar to the *inductive definition* of
      the `af R` predicate where `R` is binary relation of type
      `R : X -> X -> Prop`.

    * one corresponding to the original definition of Berardi as
      *list extension is well-founded on `R`-homogenous lists*.
 
* We show the equivalence of those two definitions under the assumption
  of the logical decidability of `R`.

```coq

Inductive hwf R : Prop :=
  | in_hwf_0 : (∀ a b, ~ R a b) -> hwf R
  | in_hwf_1 : (∀ x, hwf (R↓x)) -> hwf R
where "R ↓ x" := (fun a b => R a b /\ R b x).

Theorem hwf_Ramsey R S : hwf R -> hwf S -> hwf (R∪S)
where "R ∪ S" := (fun x y => R x y \/ S x y).

Inductive homogeneous : list X -> Prop :=
  | in_homogeneous_0 : homogeneous R nil
  | in_homogeneous_1 : ∀ x l, homogeneous R l -> Forall (R x) l -> homogeneous R (x::l).

Definition extends {X} (l m : list X) := exists x, l = x::m.

Definition Hwf R := well_founded (extends⬇(homogeneous R))
where "R ⬇ P" := (fun x y => R (proj1_sig x) (proj1_sig y)).

Theorem hwf_Hwf R : hwf R -> Hwf R.

Theorem Hwf_hwf R : (∀ x y, R x y \/ ~ R x y) -> Hwf R -> hwf R.
```

### Some more


## Bibliography

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


