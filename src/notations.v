(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

(** Short notations for universal quantification *)

Notation "∀ x : t , P" := (forall x:t, P) (at level 200, x ident, only parsing).
Notation "∀ x .. y , P" := (forall x, .. (forall y , P) ..)
  (at level 200, x binder, right associativity, only parsing): type_scope.

Notation "∃ x .. y , P" := (ex (fun x => .. (ex (fun y => P)) ..))
  (at level 200, x binder, right associativity, only parsing): type_scope.

(** Lattice notations for predicates *)

Reserved Notation "A '∩' B"  (at level 72, format "A  ∩  B", left associativity).
Reserved Notation "A '∪' B"  (at level 73, format "A  ∪  B", left associativity).
Reserved Notation "A '⊆' B"  (at level 75, format "A  ⊆  B", no associativity).
Reserved Notation "A '⊇' B"  (at level 75, format "A  ⊇  B", no associativity).
Reserved Notation "A '≃' B"  (at level 75, format "A  ≃  B", no associativity).

(** Lattice notations *)

Reserved Notation "A '⊓' B"  (at level 72, format "A  ⊓  B", left associativity).
Reserved Notation "A '⊔' B"  (at level 73, format "A  ⊔  B", left associativity).
Reserved Notation "A '⊑' B " (at level 75, format "A  ⊑  B", no associativity).
Reserved Notation "A '≡' B " (at level 75, format "A  ≡  B", no associativity).

(** Lifting notations *)

Reserved Notation "R '⋅' x"  (at level 11, format "R ⋅ x", left associativity).
Reserved Notation "R '⋄' x"  (at level 11, format "R ⋄ x", left associativity).
Reserved Notation "R '↑' x"  (at level 11, format "R ↑ x", left associativity).
Reserved Notation "R '↓' x"  (at level 11, format "R ↓ x", left associativity).
Reserved Notation "R '⇑' l"  (at level 61, format "R ⇑ l", left associativity).
Reserved Notation "R '⇓' l"  (at level 61, format "R ⇓ l", left associativity).

(** Restriction notation *)

Reserved Notation "R '⬇' P"  (at level 61, format "R ⬇ P", left associativity).
Reserved Notation "R '↡' P"  (at level 61, format "R ↡ P", left associativity).

Definition rel_restr X (P : X -> Prop) (R : X -> X -> Prop) (x y : sig P) := R (proj1_sig x) (proj1_sig y).
Arguments rel_restr {X}.

Definition pred_restr X (P Q : X -> Prop) (x : sig P) := Q (proj1_sig x).
Arguments pred_restr {X}. 

Notation "R ⬇ P" := (rel_restr P R).
Notation "Q ↡ P" := (pred_restr P Q).

Definition extends X (l m : list X) := exists x, l = x::m.
Arguments extends {X}.





