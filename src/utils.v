(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded.

Set Implicit Arguments.

Theorem measure_rect X (m : X -> nat) (P : X -> Type) :
      (forall x, (forall y, m y < m x -> P y) -> P x) -> forall x, P x.
Proof. 
  apply well_founded_induction_type, wf_inverse_image, lt_wf.
Qed.

Section list_snoc_ind.

  Variable (X : Type) (P : list X -> Type)
           (HP0 : P nil) (HP1 : forall x l, P l -> P (l++x::nil)).
           
  Theorem list_snoc_ind : forall l, P l.
  Proof.
    intros l.
    rewrite <- (rev_involutive l).
    generalize (rev l); clear l; intros l.
    induction l as [ | x l IHl ].
    apply HP0.
    simpl; apply HP1; auto.
  Qed.
  
End list_snoc_ind.

Fact list_snoc_inv X l m (x y : X) : l++x::nil = m++y::nil -> l = m /\ x = y.
Proof.
  intros H.
  apply f_equal with (f := @rev _) in H.
  do 2 rewrite rev_app_distr in H; simpl in H.
  inversion H; subst.
  rewrite <- (rev_involutive l), H2, rev_involutive; auto.
Qed.

Fact list_snoc_destruct X l : { x : X & { m | l = m++x::nil } } + { l = nil }.
Proof.
  induction l  as [ | x l _ ] using list_snoc_ind.
  * right; auto.
  * left; exists x, l; auto.
Qed.

Definition app_split X (l1 : list X) : forall l2 r1 r2, l1++r1 = l2++r2
                                      -> { m | l2 = l1++m /\ r1 = m++r2 }
                                       + { m | l1 = l2++m /\ r2 = m++r1 }.
Proof.
  induction l1 as [ | x l1 Hl1 ].
  left; exists l2; auto.
  intros [ | y l2 ] r1 r2 H.
  right; exists (x::l1); auto.
  simpl in H; injection H; clear H; intros H ?; subst.
  apply Hl1 in H.
  destruct H as [ (m & H1 & H2) | (m & H1 & H2) ].
  left; exists m; subst; auto.
  right; exists m; subst; auto.
Qed.

Fact list_split_first_half U (ll : list U) x : x <= length ll -> { l : _ & { r | ll = l++r /\ length l = x } }.
Proof.
  revert ll; induction x as [ | x IHx ]; intros [ | u ll ] Hx.
  exists nil, nil; simpl; auto.
  exists nil, (u::ll); auto.
  simpl in Hx; omega.
  destruct (IHx ll) as (l & r & H1 & H2).
  simpl in Hx; omega.
  exists (u::l), r; simpl; split; f_equal; auto.
Qed.
    
Fact list_split_second_half U (ll : list U) x : x <= length ll -> { l : _ & { r | ll = l++r /\ length r = x } }.
Proof.
  intros Hx.
  destruct list_split_first_half with (ll := ll) (x := length ll - x)
    as (l & r & H1 & H2).
  omega.
  exists l, r; split; auto.
  apply f_equal with (f := @length _) in H1.
  rewrite app_length in H1.
  omega.
Qed.  

Section Forall.

  Variables (X : Type) (P : X -> Prop).

  Fact Forall_app ll mm : Forall P (ll++mm) <-> Forall P ll /\ Forall P mm.
  Proof.
    split.
    induction ll as [ | x ll ]; split; auto.
    constructor;
    inversion H; auto.
    apply IHll; auto.
    inversion H; apply IHll; auto.
    intros (H1 & H2).
    induction H1; simpl; auto; constructor; auto.
  Qed.

  Fact Forall_cons_inv x ll : Forall P (x::ll) <-> P x /\ Forall P ll.
  Proof.
    split.
    inversion_clear 1; auto.
    constructor; tauto.
  Qed.
  
  Hypothesis P_dec : forall x, P x \/ ~ P x.
  
  Fact Forall_l_dec l : Forall P l \/ ~ Forall P l.
  Proof.
    induction l as [ | x l [ IHl | IHl ] ].
    + left; auto.
    + destruct (P_dec x) as [ H | H ].
      * left; constructor; auto.
      * right; contradict H; rewrite Forall_cons_inv in H; tauto.
    + right; contradict IHl; rewrite Forall_cons_inv in IHl; tauto.
  Qed.
  
  Fact Exists_l_dec l : (exists x, In x l /\ P x) \/ forall x, In x l -> ~ P x.
  Proof.
    induction l as [ | x l [ (y & H1 & H2) | IHl ] ].
    + right; simpl; tauto.
    + left; exists y; simpl; auto.
    + destruct (P_dec x) as [ H | H ].
      * left; exists x; simpl; auto.
      * right; intros ? [|]; subst; auto.
  Qed.

End Forall.



