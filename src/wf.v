(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Relations.

Require Import base.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x y, A x y -> B x y).

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section IND.

  (* This characterization of well_founded comes from Berardi's paper *)

  (* A R-inductive property *)

   Definition IND I (R : I -> I -> Prop) (P : I -> Prop) := forall x, (forall y, R y x -> P y) -> P x.

   Variable (X : Type) (D : X -> Prop) (R : X -> X -> Prop).
   
   Implicit Type (P : X -> Prop).

  (* A R-inductive property over a subtype D *)

  Definition IND_st P := forall x, D x -> (forall y, D y -> R y x -> P y) -> P x.
    
  (* P is R-inductive over subtype D iff P restricted to D is (R restricted to D)-inductive *)
    
  Theorem IND_st_IND P : IND_st P <-> IND (R⬇D) (P↡D).
  Proof.
    split.
    * intros H (x & Hx) H1; simpl.
      apply (H _ Hx).
      intros y Hy; apply (H1 (exist _ y Hy)).
    * intros H x Hx H1.
      apply (H (exist _ x Hx)).
      intros (y & ?); cbv; auto.
  Qed.

  (* a point is R-well-founded iff it is contained in any R-inductive property *)
  
  Definition wf x := ∀P, IND R P -> P x.
  
  (* This is the same as accessibility *)
  
  Lemma wf_eq_Acc x : wf x <-> Acc R x.
  Proof.
    split.
    * intros H; apply H.
      intro; apply Acc_intro.
    * intros H P HP; revert H.
      induction 1 as [ x _ IHx ].
      apply HP, IHx.
  Qed.
  
  (* a relation is well_founded iff all its points are well-founded *)

  Theorem well_founded_all_wf : well_founded R <-> ∀ x, wf x.
  Proof. split; intros H x; generalize (H x); apply wf_eq_Acc. Qed.
  
  (* a point is R-well-founded over D iff it is contained in D and in any R-inductive property over D *)

  Definition wf_st x := D x /\ ∀P, IND_st P -> P x.
  
  (* This is the same as accessibility in the subtype *)
  
  Lemma wf_st_eq_Acc x : wf_st x <-> D x /\ ∀H, Acc (R⬇D) (exist _ x H).
  Proof.
    split.
    * intros (H & H1); split; auto; clear H.
      apply H1.
      intros y H2 H3 H4.
      constructor 1.
      intros (z & Hz) H5.
      apply H3; auto.
    * intros (H1 & H2).
      split; auto; intros P HP.
      change (P (proj1_sig (exist _ x H1))).
      generalize (exist _ x H1) (H2 H1); clear x H1 H2.
      induction 1 as [ (x & Hx) H IH ]; simpl.
      apply HP; auto.
      intros y H3 H4.
      apply (IH (exist _ y H3)); auto.
  Qed.

  Theorem well_founded_all_wf_st : well_founded (R⬇D) <->  ∀ x P, D x -> IND_st P -> P x.
  Proof.
    split.
    * intros H x P H1; revert P.
      apply (wf_st_eq_Acc x); split; auto.
    * intros H (x & Hx).
      apply wf_st_eq_Acc; split; auto.
      intro; apply H; auto.
  Qed.

End IND.

