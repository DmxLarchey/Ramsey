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

  Fact sl_refl ll : ll <sl ll.
  Proof. 
    induction ll.
    constructor 1.
    constructor 2; auto.
  Qed.

  Fact sl_cons a ll : ll <sl a::ll.
  Proof.
    constructor 3.
    apply sl_refl.
  Qed.
  
  Fact sublist_length ll mm : ll <sl mm -> length ll <= length mm.
  Proof.
    induction 1; simpl; auto; omega.
  Qed.

  Fact sublist_nil_inv ll : ll <sl nil -> ll = nil.
  Proof. inversion 1; auto. Qed.

  Fact sublist_inv_cons ll a : ll <sl a::nil -> ll = nil \/ ll = a::nil.
  Proof. 
    inversion_clear 1; auto.
    inversion_clear H0; auto.
    inversion_clear H0; auto.
  Qed.
  
  Fact sublist_cons_inv a ll mm : a::ll <sl mm -> (exists mm', mm = a::mm' /\ ll <sl mm')
                                               \/ (exists b mm', mm = b::mm' /\ a::ll <sl mm').
  Proof.
    inversion_clear 1.
    left; exists mm0; auto.
    right; exists a0, mm0; auto.
  Qed.

  Let sublist_app_inv_rt_rec ll mm : ll <sl mm -> forall l2 r2, mm = l2++r2 -> exists l1 r1, ll = l1++r1 /\ l1 <sl l2 /\ r1 <sl r2.
  Proof.
    induction 1 as [ l1 | a l1 l2 H IH | a l1 l2 H IH ]; intros m1 m2 H0; subst.
    exists nil, nil; repeat split; auto; constructor 1.

    destruct m1 as [ | b m1 ]; simpl in H0; subst.
    exists nil, (a::l1); simpl; repeat split; auto.
    constructor 1.
    constructor 2; auto.
    injection H0; clear H0; intros; subst.
    destruct (IH _ _ eq_refl) as (u1 & u2 & ? & ? & ?); subst.
    exists (b::u1), u2; simpl; repeat split; auto.
    constructor 2; auto.
    
    destruct m1 as [ | b m1 ]; simpl in H0; subst.
    exists nil, l1; simpl; repeat split; auto.
    constructor 1.
    constructor 3; auto.
    injection H0; clear H0; intros; subst.
    destruct (IH _ _ eq_refl) as (u1 & u2 & ? & ? & ?); subst.
    exists u1, u2; simpl; repeat split; auto.
    constructor 3; auto.
  Qed.

  Fact sublist_app_inv_lft l1 r1 mm : l1++r1 <sl mm -> exists l2 r2, mm = l2++r2 /\ l1 <sl l2 /\ r1 <sl r2.
  Proof.
    revert l1 r1; induction mm as [ | y mm IHmm ]; intros l1 l2 H.
    apply sublist_nil_inv in H.
    destruct l1; destruct l2; try discriminate H.
    exists nil, nil; repeat split; auto; constructor 1.
    destruct l1 as [ | x l1 ]; simpl in H.
    exists nil, (y::mm); repeat split; auto; constructor 1.
    apply sublist_cons_inv in H.
    destruct H as [ (m1 & H1 & H2) | (z & m1 & H1 & H2) ];
    injection H1; clear H1; intros ? ?; subst.
    destruct (IHmm _ _ H2) as (l3 & r3 & H3 & H4 & H5); subst.
    exists (x::l3), r3; repeat split; auto; constructor 2; auto.
    change (x::l1++l2) with ((x::l1)++l2) in H2.
    destruct (IHmm _ _ H2) as (l3 & r3 & H3 & H4 & H5); subst.
    exists (z::l3), r3; repeat split; auto.
    constructor 3; auto.
  Qed.

  Fact sublist_app_inv_rt ll l2 r2 : ll <sl l2++r2 -> exists l1 r1, ll = l1++r1 /\ l1 <sl l2 /\ r1 <sl r2.
  Proof.
    intros H; apply sublist_app_inv_rt_rec with (1 := H); auto.
  Qed.

  Fact sublist_cons_inv_rt ll x mm : ll <sl x::mm -> ll <sl mm \/ exists l', ll = x::l' /\ l' <sl mm.
  Proof.
    change (x::mm) with ((x::nil)++mm).
    intros H.
    apply sublist_app_inv_rt in H.
    destruct H as (l & r & H1 & H2 & H3).
    apply sublist_inv_cons in H2.
    destruct H2; subst; simpl; auto.
    right; exists r; auto.
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
    apply sublist_nil_inv in H4; subst.
    left; rewrite <- app_nil_end; auto.
  Qed.

  Fact sl_erase_rec ll mm : ll <sl mm -> forall l m r, ll = l++m++r -> l++r <sl mm.
  Proof.
    induction 1 as [ l1 | a l1 l2 H IH | a l1 l2 H IH ]; intros l m r Eq; subst.
    destruct l; try discriminate Eq; simpl in Eq |- *.
    destruct m; try discriminate Eq; simpl in Eq |- *.
    subst; constructor 1.
    
    destruct l as [ | a' l ]; simpl in Eq |- *.
    destruct m as [ | b' l ]; simpl in Eq |- *.
    subst; constructor 2; auto.
    injection Eq; clear Eq; intros; subst.
    constructor 3.
    apply (IH nil l r); auto.
    injection Eq; clear Eq; intros; subst.
    constructor 2.
    apply (IH _ m); auto.
    constructor 3.
    apply (IH _ m); auto.
  Qed.
  
  Fact sl_erase l m r mm : l++m++r <sl mm -> l++r <sl mm.
  Proof.
    intros H; apply sl_erase_rec with (1 := H) (m := m); auto.
  Qed.

  Fact sl_cons_erase a l m : a::l <sl m -> l <sl m.
  Proof.
    apply sl_erase with (l := nil) (m := a::nil).
  Qed.
    
  Let sl_trans_rec l1 l2 : l1 <sl l2 -> forall mm l3, mm++l2 <sl l3 -> mm++l1 <sl l3.
  Proof.
    induction 1 as [ l1 | a l1 l2 H IH | a l1 l2 H IH ].
    
    intros mm l3.
    cutrewrite (mm++l1 = mm++l1++nil).
    apply sl_erase.
    rewrite <- app_nil_end; auto.
    
    intros mm l3 H3.
    cutrewrite (mm++a::l1 = (mm++a::nil)++l1).
    apply IH.
    rewrite app_ass; auto.
    rewrite app_ass; auto.
    
    intros mm l3 H3.
    apply IH.
    apply sl_erase with (m := a::nil).
    simpl; auto.
  Qed.

  Fact sl_trans l1 l2 l3 : l1 <sl l2 -> l2 <sl l3 -> l1 <sl l3.
  Proof.
    intro; apply sl_trans_rec with (mm := nil); auto.
  Qed.

  Fact sl_app_left ll mm : mm <sl ll++mm.
  Proof.
    induction ll as [ | x ll IH ]; simpl; auto.
    apply sl_refl.
    apply sl_trans with (1 := IH), sl_cons.
  Qed.
  
  Fact sl_app_right ll mm : ll <sl ll++mm.
  Proof.
    induction ll; simpl.
    constructor 1.
    constructor 2; auto.
  Qed.

  Fact sl_app l1 m1 l2 m2 : l1 <sl l2 -> m1 <sl m2 -> l1++m1 <sl l2++m2.
  Proof.
    intros H1 H2.
    apply sl_trans with (l2 := l1++m2).
    clear H1; induction l1; auto; simpl; constructor 2; auto.
    clear H2; induction H1; simpl.
    apply sl_app_left.
    constructor 2; auto.
    constructor 3; auto.
  Qed.  
  
  Fact sl_snoc l m x : l <sl m -> l <sl (m++x::nil).
  Proof. intros H; apply sl_trans with (1 := H), sl_app_right. Qed.
  
  Fact sl_rev l m : l <sl m -> rev l <sl rev m.
  Proof.
    induction 1 as [ l | a l m | a l m ].
    constructor 1.
    simpl; apply sl_app; auto; apply sl_refl.
    simpl; apply sl_snoc; auto.
  Qed.
  
  Fact sl_In ll mm x : ll <sl mm -> In x ll -> In x mm.
  Proof.
    induction 1 as [ mm | a ll mm H IH | a ll mm H IH ].
    intros [].
    intros [ H' | H' ]; subst; simpl; tauto.
    right; auto.
  Qed.

  Fact In_sl (a : X) l : In a l -> a::nil <sl l.
  Proof.
    induction l.
    intros [].
    intros [ []| ].
    constructor 2; constructor 1.
    constructor 3; auto.
  Qed.

  Fact sublist_eq ll mm : ll <sl mm -> length mm <= length ll -> ll = mm.
  Proof.
    induction 1 as [ mm | a ll mm H IH | a ll mm H IH ].
    destruct mm; simpl; try omega; auto.
    simpl; intros H1; apply le_S_n in H1; f_equal; auto.
    simpl; intros H1; apply sublist_length in H; omega.
  Qed.

End sublist.

Infix "<sl" := (@sublist _) (at level 70).

Fact sublist_map X Y (f : X -> Y) l m : l <sl m -> map f l <sl map f m.
Proof.
  induction 1; simpl.
  constructor 1.
  constructor 2; auto.
  constructor 3; auto.
Qed.
 

