(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Set Implicit Arguments.

Section sublist.

  Variable X : Type.

  Reserved Notation "x '<sl' y" (at level 70).

  Inductive sublist : list X -> list X -> Prop :=
    | in_sl_0 : forall ll, nil <sl ll
    | in_sl_1 : forall a ll mm, ll <sl mm -> a::ll <sl a::mm
    | in_sl_2 : forall a ll mm, ll <sl mm -> ll <sl a::mm
  where "x <sl y" := (sublist x y).
  
  Hint Constructors sublist.
  
  Fact sl_refl ll : ll <sl ll.              Proof. induction ll; auto. Qed.
  
  Hint Resolve sl_refl.

  Fact sl_cons a ll : ll <sl a::ll.         Proof. auto. Qed.
  Fact sl_app_left ll mm : mm <sl ll++mm.   Proof. induction ll; simpl; auto. Qed.
  Fact sl_app_right ll mm : ll <sl ll++mm.  Proof. induction ll; simpl; auto. Qed.

  Hint Resolve sl_cons sl_app_left sl_app_right.

  Fact sl_nil_inv l : l <sl nil <-> l = nil.
  Proof. 
    split.
    + inversion 1; auto.
    + intros; subst; auto.
  Qed.
  
  Fact sl_cons_inv x y l m : x::l <sl y::m <-> (x = y /\ l <sl m) \/ x::l <sl m.
  Proof.
    split.
    + inversion 1; subst; auto.
    + intros [[]|]; subst; auto.
  Qed.
  
  Fact sl_trans l1 l2 l3 : l1 <sl l2 -> l2 <sl l3 -> l1 <sl l3.
  Proof.
    intros H1 H2; revert H2 l1 H1.
    induction 1; intros l1 H1; auto.
    + rewrite sl_nil_inv in H1; subst; auto.
    + destruct l1 as [ | b l1 ]; auto.
      rewrite sl_cons_inv in H1.
      destruct H1 as [[]|]; subst; auto.
  Qed.
  
  Fact sl_app l1 m1 l2 m2 : l1 <sl l2 -> m1 <sl m2 -> l1++m1 <sl l2++m2.
  Proof.
    intros H1 H2.
    apply sl_trans with (l2 := l1++m2); auto.
    + clear H1; induction l1; simpl; auto.
    + clear H2; induction H1; simpl; auto.
  Qed.

  Fact sublist_nil_inv x l : x::l <sl nil <-> False.
  Proof. split; inversion 1; auto. Qed.

  Fact sublist_inv_cons ll a : ll <sl a::nil <-> ll = nil \/ ll = a::nil.
  Proof.
    destruct ll as [ | b ll ].
    + split; auto.
    + rewrite sl_cons_inv, sl_nil_inv, sl_nil_inv.
      split.
      * intros [ [] | ]; subst; auto; discriminate.
      * intros [ | H ]; try discriminate.
        inversion H; subst; auto.
  Qed. 
  
  Fact sublist_app_inv_lft l1 r1 mm : l1++r1 <sl mm -> exists l2 r2, mm = l2++r2 /\ l1 <sl l2 /\ r1 <sl r2.
  Proof.
    revert l1 r1; induction mm as [ | x mm IH ]; simpl; intros l1 r1 H.
    + rewrite sl_nil_inv in H.
      destruct l1; destruct r1; try discriminate.
      exists nil, nil; auto.
    + destruct l1 as [ | y l1 ].
      * exists nil, (x::mm); auto.
      * simpl in H; rewrite sl_cons_inv in H.
        destruct H as [ (? & H) | H ]; subst.
        - destruct (IH _ _ H) as (l2 & r2 & H1 & H2 & H3).
          exists (x::l2), r2; subst; auto.
        - destruct (IH (y::l1) r1 H) as (l2 & r2 & H1 & H2 & H3).
          exists (x::l2), r2; subst; auto.
  Qed.

  Fact sublist_app_inv_rt ll l2 r2 : ll <sl l2++r2 -> exists l1 r1, ll = l1++r1 /\ l1 <sl l2 /\ r1 <sl r2.
  Proof.
    revert ll; induction l2 as [ | x l2 IH ]; intros ll H.
    + exists nil, ll; auto.
    + destruct ll as [ | y ll ].
      * exists nil, nil; auto.
      * simpl in H; rewrite sl_cons_inv in H.
        destruct H as [ (? & H) | H ]; subst.
        - destruct (IH _ H) as (l1 & r1 & H1 & H2 & H3).
          exists (x::l1), r1; subst; auto.
        - destruct (IH _ H) as (l1 & r1 & H1 & H2 & H3).
          exists l1, r1; subst; auto.
  Qed.

  Fact sublist_cons_inv_rt ll x mm : ll <sl x::mm -> ll <sl mm \/ exists l', ll = x::l' /\ l' <sl mm.
  Proof.
    destruct ll; auto.
    rewrite sl_cons_inv.
    intros [[]|]; subst; auto.
    right; firstorder.
  Qed.
  
  Fact sl_length ll mm : ll <sl mm -> length ll <= length mm.
  Proof. induction 1; simpl; auto; omega. Qed.

  Fact sl_In ll mm x : ll <sl mm -> In x ll -> In x mm.
  Proof. induction 1; simpl; tauto. Qed.

  Fact In_sl x ll : In x ll <-> x::nil <sl ll.
  Proof.
    split.
    + intros H; apply in_split in H.
      destruct H as (? & ? & ?); subst.
      apply sl_trans with (2 := sl_app_left _ _); auto.
    + intros H; apply (sl_In _ H); left; auto.
  Qed.
  
  Fact sl_erase l m r mm : l++m++r <sl mm -> l++r <sl mm.
  Proof. intros H; apply sl_trans with (2 := H), sl_app; auto. Qed.

  Fact sl_snoc l m x : l <sl m -> l <sl (m++x::nil).
  Proof. intros H; apply sl_trans with (1 := H); auto. Qed.
  
  Hint Resolve sl_app sl_snoc.
  
  Fact sl_rev l m : l <sl m -> rev l <sl rev m.
  Proof. induction 1; simpl; auto. Qed.

  Fact sublist_cons_inv x ll mm : x::ll <sl mm <-> exists l r, mm = l++x::r /\ ll <sl r.
  Proof.
    split.
    * change (x::ll) with ((x::nil)++ll); intros H.
      apply sublist_app_inv_lft in H.
      destruct H as (pp & r & H1 & H2 & H3).
      rewrite <- In_sl in H2.
      apply in_split in H2.
      destruct H2 as (l & m & H2); subst.
      exists l, (m++r); rewrite app_ass; simpl; split; auto.
      apply sl_trans with (2 := sl_app_left _ _); auto.
    * intros (? & ? & ? & ?); subst.
      apply sl_trans with (2 := sl_app_left _ _); auto.
  Qed.
  
  Fact sublist_snoc_inv ll mm x : ll <sl mm++x::nil -> ll <sl mm \/ exists l', l' <sl mm /\ ll = l'++x::nil.
  Proof.
    intros H.
    apply sublist_app_inv_rt in H.
    destruct H as ( l1 & r1 & H1 & H2 & H3 ).
    inversion H3; subst.
    left; rewrite <- app_nil_end; auto.
    apply sublist_inv_cons in H3.
    destruct H3 as [ H3 | H3 ]; try discriminate H3.
    injection H3; clear H3; intros; subst.
    right; exists l1; auto.
    left; rewrite (app_nil_end mm); auto.
  Qed.

  Fact sl_cons_erase a l m : a::l <sl m -> l <sl m.
  Proof. apply sl_erase with (l := nil) (m := a::nil). Qed.

  Fact sublist_eq ll mm : ll <sl mm -> length mm <= length ll -> ll = mm.
  Proof.
    induction 1 as [ mm | a ll mm H IH | a ll mm H IH ].
    destruct mm; simpl; try omega; auto.
    simpl; intros H1; apply le_S_n in H1; f_equal; auto.
    simpl; intros H1; apply sl_length in H; omega.
  Qed.

End sublist.

Infix "<sl" := (@sublist _) (at level 70).

Hint Constructors sublist.

Hint Resolve sl_refl sl_cons sl_app_left sl_app_right sl_app sl_snoc.

Fact sublist_map X Y (f : X -> Y) l m : l <sl m -> map f l <sl map f m.
Proof. induction 1; simpl; auto. Qed.


