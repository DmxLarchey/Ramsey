(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Require Import base.

Local Notation "A ⊆ B" := (∀x y, A x y -> B x y).
Local Notation "A ∩ B" := (fun x y => A x y /\ B x y).
Local Notation "A ∪ B" := (fun x y => A x y \/ B x y).

Local Notation "R ↑ x" := (fun a b => R a b \/ R x a).

Set Implicit Arguments.

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section good.

  Variables (X : Type) (R : X -> X -> Prop).

  Inductive good : list X -> Prop := 
    | in_good_0 : ∀ ll a b, In b ll -> R b a -> good (a::ll)
    | in_good_1 : ∀ ll a, good ll -> good (a::ll).

  Inductive bad : list X -> Prop :=
    | in_bad_0 : bad nil
    | in_bad_1 : ∀ ll a, (∀b, In b ll -> ~ R b a) -> bad ll -> bad (a::ll).

  Fact good_nil_inv : good nil <-> False.
  Proof. split;  intros H; inversion H. Qed.

  Fact good_cons_inv a ll : good (a::ll) <-> (∃b, In b ll /\ R b a) \/ good ll.
  Proof.
    split.
    * intros H; inversion_clear H.
      + left; exists b; auto.
      + right; auto.
    * intros [ (b & H1 & H2) | H ].
      + constructor 1 with b; auto.
      + constructor 2; auto.
  Qed.
  
  Fact bad_cons_inv a ll : bad (a::ll) <-> bad ll /\ ∀b, In b ll -> ~ R b a.
  Proof.
    split.
    * inversion 1; auto.
    * constructor 2; tauto.
  Qed.

  Fact good_sg_inv a : good (a::nil) <-> False.
  Proof.
    rewrite good_cons_inv, good_nil_inv; simpl.
    split; auto; intros [ (_ & [] & _) | [] ].
  Qed.
  
  Fact bad_sg_inv a : bad (a::nil).
  Proof.
    constructor 2.
    * intros _ [].
    * constructor.
  Qed.

  Fact good_cons_not_inv a ll : good (a::ll) -> ~ good ll -> ∃b, In b ll /\ R b a.
  Proof. intros H ?; apply good_cons_inv in H; tauto. Qed.

  Fact good_two_inv a b : good (a::b::nil) <-> R b a.
  Proof.
    split.
    + rewrite good_cons_inv, good_sg_inv.
      intros [ (c & [ | [] ] & ?) | [] ]; subst; auto.
    + constructor 1 with b; simpl; auto.
  Qed.

  Fact good_bad_False ll : good ll -> bad ll -> False.
  Proof. induction 1; rewrite bad_cons_inv; firstorder. Qed.

  Fact not_good_eq_bad ll : bad ll <-> ~ good ll. 
  Proof.
    split.
    + intros ? ?; apply good_bad_False with ll; auto.
    + induction ll; intros H.
      constructor.
      constructor.
      intros; contradict H.
      constructor 1 with (1 := H0); auto.
      apply IHll; contradict H.
      constructor 2; auto.
  Qed.

  Fact good_sublist ll mm : ll <sl mm -> good ll -> good mm.
  Proof.
    induction 1 as [ mm | a ll mm H IH | a ll mm H IH ].
    + rewrite good_nil_inv; tauto.
    + do 2 rewrite good_cons_inv.
      intros [ (b & H1 & H2) | ]; auto.
      left; exists b; split; auto.
      revert H1; apply sl_In; trivial.
    + constructor 2; auto.
  Qed.

  Fact good_app_left ll mm : good mm -> good (ll++mm).
  Proof. apply good_sublist, sl_app_left. Qed.

  Fact good_app_right ll mm : good ll -> good (ll++mm).
  Proof. apply good_sublist, sl_app_right. Qed.
 
  Fact good_spec ll : good ll <-> ∃ l a m b r, ll = l++a::m++b::r /\ R b a.
  Proof.
    split.
    + induction 1 as [ ll a b Hll H1 | ll x Hll IH ].
      apply in_split in Hll; destruct Hll as ( m & r & H2 ).
      exists nil, a, m, b, r; subst; auto.
      destruct IH as (l & a & m & b & r & H1 & H2).
      exists (x::l), a, m, b, r; subst; auto.
    + intros (l & a & m & b & r & H1 & H2); subst.
      apply good_app_left.
      constructor 1 with b; auto.
      apply in_or_app; right; left; auto.
  Qed.

  Fact good_app_inv ll mm : good (ll++mm) <-> good ll
                                           \/ good mm
                                           \/ ∃ a b, In a ll /\ In b mm /\ R b a.
  Proof.
    split.
    + induction ll as [ | x ll IH ]; simpl.
      * tauto.
      * do 2 rewrite good_cons_inv.
        intros [ (b & H1 & H2) | H ].
        - apply in_app_or in H1; destruct H1 as [ H1 | H1 ].
          ** left; left; exists b; auto.
          ** do 2 right; exists x, b; auto.
        - destruct (IH H) as [ H1 | [ H1 | (a & b & H1 & H2 & H3) ] ]; auto.
          do 2 right; exists a, b; auto.
    + intros [ H1 | [ H1 | (a & b & H1 & H2 & H3) ] ].
      * apply good_app_right; auto.
      * apply good_app_left; auto.
      * apply in_split in H1.
        destruct H1 as (l & r & ?); subst.
        rewrite app_ass; simpl.
        apply good_app_left.
        constructor 1 with b; auto.
        apply in_or_app; simpl; auto.
  Qed.
 
  Fact sublist_good_eq ll : good ll <-> ∃ a b, R b a /\ a::b::nil <sl ll.
  Proof.
    rewrite good_spec; split.
    + intros (l & a & m & b & r & ? & H); subst.
      exists a, b; split; auto.
      do 2 (apply sl_trans with (2 := sl_app_left _ _); constructor).
      constructor.
    + intros (a & b & H1 & H2).
      apply sl_cons_inv in H2.
      destruct H2 as (l & mm & H2 & H3).
      rewrite <- In_sl in H3.
      apply in_split in H3.
      destruct H3 as (m & r & H3); subst.
      exists l, a, m, b, r; auto.
  Qed.

  Section decision.

    Variable R_dec : ∀ x y, R x y \/ ~ R x y.
    
    Theorem good_dec ll : good ll \/ ~ good ll.
    Proof.
      induction ll as [ | x ll [ IH | IH ] ].
      + rewrite good_nil_inv; tauto.
      + left; constructor 2; auto.
      + destruct (Exists_l_dec (fun y => R y x)) with (l := ll) as [ (y & H1 & H2) | H ].
        * intro; apply R_dec.
        * left; constructor 1 with y; auto.
        * right; contradict IH.
          rewrite good_cons_inv in IH.
          destruct IH as [ (y & H1 & H2) | ]; auto.
          destruct (H _ H1); auto.
    Qed.

  End decision.

End good.

Fact good_mono X (R S : X -> X -> Prop) : R ⊆ S -> ∀ l, good R l -> good S l.
Proof.
  intros H ll.
  induction 1 as [ ll a b Hll Hab | ].
  constructor 1 with (1 := Hll); auto.
  constructor 2; auto.
Qed.

