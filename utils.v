(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded.

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
