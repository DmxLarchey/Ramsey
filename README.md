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
  by T. Coquand. 
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

### The direct and abstract proof of Ramsey's theorem (see [ramsey_paper.v](src/ramsey_paper.v))

* We show the following `Ramsey_lattice` result below. Given:
  * a bounded distributive lattice `(Σ,⊑,⊔,⊓,⊥,⊤)`
  * an operator `op : X -> Σ -> Σ` s.t. `op x` is a lattice
    morphism for any `x`. 
  * `Σ` represents a lattice of relations and
    `⊤` represents the full relation. 
  * we denote `op x a` by `a⋅x` as in the paper
    and `x ≡ y` denotes `x ⊑ y /\ y ⊑ x`.

* We follow very carefully the proof arguments of T. Coquand
  but because the theorem is applied more widely, we substitute
  `US` for `Ar` (arity) and `UF` for  `AF` (almost full):
  * `US` stands for *ultimately stable*: repeated 
     applications of `op x` always leads to a fixpoint.
  * `UF` stands for *ultimately full*: repeated
    applications of `a ↦ a⊔a⋅x` always leads to `⊤`.

```coq
Inductive US (a : Σ) : Prop :=
  | in_US_0 : (∀x, a⋅x ≡ a)   -> US a
  | in_US_1 : (∀x, US (a⋅x))  -> US a
where "a⋅x" := (op x a).

Inductive UF (a : Σ) : Prop :=
  | in_UF_0 : a ≡ ⊤           -> UF a
  | in_UF_1 : (∀x, UF (a[x])) -> UF a
where "a[x]" := (a⊔a⋅x).

Theorem Ramsey_lattice r s : US r -> US s -> UF r -> UF s -> UF (r⊓s).
```
### Applications to finitary and binary Almost Full relations

* The following results can be found in the files
  [AF.v](src/AF.v)

```coq
Variable X : Type.
Implicit Types (R S P : list X -> Prop) (l :list X).

Inductive sublist : list X -> list X -> Prop :=
  | in_sl_0 : ∀ ll, nil ≼ ll
  | in_sl_1 : ∀ a ll mm, ll ≼ mm -> a::ll ≼ a::mm
  | in_sl_2 : ∀ a ll mm, ll ≼ mm -> ll ≼ a::mm
where "x≼y" := (sublist x y).

Inductive bar P l : Prop :=
  | in_bar_0 : P l                 -> bar P l
  | in_bar_1 : (∀ x, bar P (x::l)) -> bar P l.

Inductive AF (R : list X -> Prop) : Prop := 
  | in_AF_0 : (∀x, R x)      -> AF R
  | in_AF_1 : (∀x, AF (R↑x)) -> AF R
where "R↑x" := (fun l => R (x::l)).

Definition GOOD R l := ∀m, ∃k, k ≼ l /\ R (rev k++m).

Theorem AF_bar_lift_eq R l : AF (R⇑l) <-> bar (GOOD R) l
where "R⇑[x1;...xn]" := (R↑xn...↑x1)


```
 

This repository also contains applications of the abstract
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


