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

Local Notation "R ↓ x" := (fun a b => R a b /\ R b x).

Set Implicit Arguments.

(** The definition of R-homogeneous list for a binary relation R 

    homogeneous R (x1::...::xn::nil) <=> ∀ i < j, xi R xj
    
    see homogeneous_spec below 
*)

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section homogeneous.

  Variable (X : Type) (R : X -> X -> Prop).

  Inductive homogeneous : list X -> Prop :=
    | in_homogeneous_0 : homogeneous nil
    | in_homogeneous_1 : ∀ x l, homogeneous l -> Forall (R x) l -> homogeneous (x::l).
    
  Fact homogeneous_sg x : homogeneous (x::nil).
  Proof. do 2 constructor. Qed.
    
  Fact homogeneous_inv x l : homogeneous (x::l) <-> Forall (R x) l /\ homogeneous l.
  Proof. 
    split. 
    * inversion 1; subst; auto.
    * constructor; tauto. 
  Qed.
  
  Fact homogeneous_app_inv l m : 
         homogeneous (l++m) <-> homogeneous l 
                             /\ homogeneous m 
                             /\ ∀ x y, In x l -> In y m -> R x y.
  Proof.
    split.
    + induction l as [ | x l IHl ]; simpl.
      * repeat split; auto; try constructor; intros _ _ [].
      * intros H.
        apply homogeneous_inv in H.
        destruct H as [ H1 H2 ].
        apply IHl in H2.
        destruct H2 as (H2 & H3 & H4).
        apply Forall_app in H1.
        destruct H1 as [ H0 H1 ].
        repeat split; auto.
        constructor; auto.
        intros x' y [ | H' ] Hy; auto.
        subst.
        rewrite Forall_forall in H1; auto.
    + intros (H1 & H2 & H3); revert H3.
      induction H1 as [ | x l H1 IH1 H3 ]; intros H4; simpl; auto.
      constructor.
      * apply IH1; intros; apply H4; auto; right; auto.
      * rewrite Forall_app; split; auto.
        rewrite Forall_forall.
        intros; apply H4; auto; left; auto.
  Qed.
 
  Fact homogeneous_two_inv x y l : homogeneous (x::y::l) -> R x y.
  Proof.
    inversion 1; subst.
    inversion H3; subst; auto.
  Qed.
  
  (* This is a non-inductive characterization of homogeneous *)
  
  Theorem homogeneous_spec ll : homogeneous ll <-> ∀ l x m y r, ll = l++x::m++y::r -> R x y.
  Proof.
    split.
    + intros H l x m y r E; subst.
      rewrite homogeneous_app_inv in H.
      destruct H as (_ & H & _).
      rewrite homogeneous_inv, Forall_app, Forall_cons_inv in H.
      tauto.
    + induction ll as [ | a ll IHll ]; intros Hll; constructor.
      * apply IHll.
        intros l x m y r E.
        apply (Hll (a::l) x m y r); subst; auto.
      * rewrite Forall_forall; intros u Hu.
        apply in_split in Hu; destruct Hu as (l & r & Hu).
        apply (Hll nil a l u r); subst; auto.
  Qed.
    
  Hypothesis R_dec : forall x y, R x y \/ ~ R x y.
  
  Theorem homogeneous_dec l : homogeneous l \/ ~ homogeneous l.
  Proof. 
    induction l as [ | x l [ H | H ] ].
    + left; constructor.
    + destruct Forall_l_dec with (P := R x) (l := l) as [ H1 | H1 ].
      * intro; apply R_dec.
      * left; constructor; auto.
      * right; contradict H1; rewrite homogeneous_inv in H1; tauto.
    + right; contradict H; rewrite homogeneous_inv in H; tauto.
  Qed.

End homogeneous.

Fact homogeneous_snoc X R ll x : @homogeneous X R (ll ++ x :: nil) -> homogeneous (R↓x) ll.
Proof.
  intros H; apply homogeneous_app_inv in H.
  destruct H as (H1 & _ & H2).
  assert (Forall (fun y => R y x) ll) as H3.
  { rewrite Forall_forall; intros y Hy; apply H2; simpl; auto. }
  clear H2; revert H1 x H3.
  induction 1 as [ | x ll H1 H2 IH2 ]; intros y Hy; simpl.
  + constructor.
  + rewrite Forall_cons_inv in Hy.
    destruct Hy as [ H3 H4 ].
    constructor 2; auto.
    revert IH2 H4; repeat rewrite Forall_forall; firstorder.
Qed.

