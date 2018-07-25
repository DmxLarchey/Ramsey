# Ramsey's theorem in Type Theory and applications

## Copyright

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
  homogeneous well-founded and of Berardi and Steila's characterization
  using the `well_founded` predicate.

* We leave some open questions regarding the generalization of
  the abstract proof to poset-indexed families of relations
  and to the proof of the *indexed Higman's theorem* leading
  to a shorter proof of *Kruskal's tree theorem* (following an
  unpublished draft by T. Coquand).

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

* The following results for finitary almost full relations
  can be found in the file [AF.v](src/AF.v)

```coq
Variable X : Type.
Implicit Type (R S P : list X -> Prop) (l :list X).

Inductive bar P l : Prop :=
  | in_bar_0 : P l                 -> bar P l
  | in_bar_1 : (∀ x, bar P (x::l)) -> bar P l.

Inductive Ar R : Prop :=
  | in_Ar_0 : (∀ x l, R (x::l) <-> R l) -> Ar R
  | in_Ar_1 : (∀ x, Ar (R⋅x))           -> Ar R
where "R⋅x" := (fun l => R (x::l)).
    
Inductive AF (R : list X -> Prop) : Prop := 
  | in_AF_0 : (∀x, R x)      -> AF R
  | in_AF_1 : (∀x, AF (R↑x)) -> AF R
where "R↑x" := (fun l => R l \/ R (x::l)).

Theorem AF_Ramsey R S : Ar R -> Ar S -> AF R -> AF S -> AF (R∩S)
where "R∩S" := (fun l => R l /\ S l).

Inductive sublist : list X -> list X -> Prop :=
  | in_sl_0 : ∀ ll, nil ≼ ll
  | in_sl_1 : ∀ a ll mm, ll ≼ mm -> a::ll ≼ a::mm
  | in_sl_2 : ∀ a ll mm, ll ≼ mm -> ll ≼ a::mm
where "x≼y" := (sublist x y).

Definition GOOD R l := ∀m, ∃k, k ≼ l /\ R (rev k++m).

Theorem AF_bar_lift_eq R l : AF (R⇑l) <-> bar (GOOD R) l
where "R⇑[x1;...xn]" := (R↑xn...↑x1).
```

* The following results for binary almost full relations
  can be found in the file [af.v](src/af.v)

```coq

Variable (X : Type).
Implicit Type (R S : X -> X -> Prop).

Inductive af R : Prop :=
  | in_af_0 : (∀ a b, R a b) -> af R
  | in_af_1 : (∀x, af (R↑x)) -> af R
where "R↑x" := (fun a b => R a b \/ R x a).

Theorem af_ramsey R S : af R -> af S -> af (R∩S)
where "R∩S" := (fun a b => R a b /\ S a b).

Inductive good R : list X -> Prop := 
  | in_good_0 : ∀ ll a b, In b ll -> R b a -> good R (a::ll)
  | in_good_1 : ∀ ll a, good R ll -> good R (a::ll).

Theorem af_bar_lift_eq R l : af (R⇑l) <-> bar (good R) l
where "R⇑[x1;...xn]" := (R↑xn...↑x1).
```

### Applications to finitary and binary Homogeneous Well-founded relations

* The following results for finitary homogeneous well-founded relations
  can be found in the file [HWF.v](src/HWF.v).

```coq
Variable X : Type.
Implicit Type (R S P : list X -> Prop) (l :list X).

Inductive HWF R : Prop := 
  | in_HWF_0 : (∀x, ~ R x)     -> HWF R
  | in_HWF_1 : (∀x, HWF (R↓x)) -> HWF R
where "R↓x" := (fun l => R l /\ R (l++x::nil)).

Definition Ar_tail R := Ar (fun l => R (rev l)).

Theorem HWF_Ramsey R S : Ar_tail R -> Ar_tail S -> HWF R -> HWF S -> HWF (R∪S)
where "R∪S" := (fun l => R l \/ S l).
```

* The following results for binary homogeneous well-founded relations
  can be found in the file [hwf.v](src/hwf.v). We propose 
  two definitions of binary HWF relations: 
  * one by direct induction similar to the *inductive definition* of
    the previous `af R` predicate. 
  * one corresponding to the definition of Berardi and Stelia 
    as *list extension is well-founded on homogeneous lists*.
* We show the equivalence of those two definitions under the assumption
  of the logical decidability of `R`.

```coq
Variable (X : Type).
Implicit Type (R S : X -> X -> Prop).

Inductive hwf R : Prop :=
  | in_hwf_0 : (∀ a b, ~ R a b) -> hwf R
  | in_hwf_1 : (∀ x, hwf (R↓x)) -> hwf R
where "R↓x" := (fun a b => R a b /\ R b x).

Theorem hwf_Ramsey R S : hwf R -> hwf S -> hwf (R∪S)
where "R∪S" := (fun x y => R x y \/ S x y).

Inductive homogeneous : list X -> Prop :=
  | in_homogeneous_0 : homogeneous R nil
  | in_homogeneous_1 : ∀ x l, homogeneous R l -> Forall (R x) l -> homogeneous R (x::l).

Theorem hwf_bar_lift_eq R l : hwf (R⇓l) <-> bar (fun x => ~ homogeneous R x) l
where "R⇓[x1;...xn]" := (R↓xn...↓x1).

Definition extends {X} (l m : list X) := ∃x, l = x::m.

Definition Hwf R := well_founded (extends⬇(homogeneous R))
where "R⬇P" := (fun x y => R (proj1_sig x) (proj1_sig y)).

Theorem hwf_Hwf R : hwf R -> Hwf R.

Theorem Hwf_hwf R : (∀ x y, R x y \/ ~ R x y) -> Hwf R -> hwf R.
```

## Remaining questions (unsorted brainstorming)

* Which definition is best, `Hwf` or `hwf` given that Hwf is a bit weaker
  for non-decidable relations. Also the link `well_founded R -> hwf R`
  assumes decidability of `R`. This is not needed for Hwf. However, the
  proof of Ramsey is very nice and short for `hwf` whereas Berardi
  and Stelia's (B&S) proof for `Hwf` is more complicated and probably incomplete.

* Indeed, B&S proof represents trees as predicates over branches and
  thus, it is not possible to decide whereas a tree is empty or not.
  However, this case distinction is used in the proof. Maybe changing
  the representation of trees is necessary for the proof to be implemented.

* Is it possible to generalize the abstract Ramsey's proof to deal with
  poset-indexed families of relations? What could be a definition of
  `AF` or `GOOD` in that case? T. Coquand's proof of the *variable Ramsey
  theorem* seems to be based on `bar` inductive predicates. A proof of
  the non-variable case of Ramsey's theorem using `bar` can be found
  in Daniel Fridlender's thesis but it is more complicated to understand.

* Of course the ultimate objective is a shorter mechanized proof of
  [Kruskal's tree theorem](http://www.loria.fr/~larchey/Kruskal).

## Links and practical information

### How do I set it up? ###

* This should compile with Coq 8.6+ with `cd src; make af.vo hwf.vo`.

### Bibliography

* The draft paper [A direct proof of Ramsey’s Theorem](http://www.cse.chalmers.se/~coquand/ramsey2.pdf) by Thierry Coquand.

* The paper 
 [An intuitionistic version of Ramsey's Theorem and its use in Program Termination](https://doi.org/10.1016/j.apal.2015.08.002) 
  by Stefano Berardi and Silvia Steila.

* The paper [Stop when you are Almost-Full](https://doi.org/10.1.1.225.3021) 
  by Dimitrios Vytiniotis, Thierry Coquand and David Wahlstedt.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)


