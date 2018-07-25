(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Relations.

Require Import base af hwf.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x y, A x y -> B x y).
Local Notation "R ↑ x" := (fun a b => R a b \/ R x a).
Local Notation "R ↓ x" := (fun a b => R a b /\ R b x).

Local Notation "A ∩ B" := (fun x y => A x y /\ B x y).
Local Notation "A ∪ B" := (fun x y => A x y \/ B x y).

Section af_hwf.

  Variable (X : Type).
  Implicit Type (R S : X -> X -> Prop).

  Let af_hwf R : af R -> hwf (fun x y => ~ R y x).
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    * constructor 1; intros; auto.
    * constructor 2; intros x.
      generalize (IHR x); apply hwf_anti.
      tauto.
  Qed.

  Let hwf_af R : (forall x y, R x y \/ ~ R x y) -> hwf R -> af (fun x y => ~ R y x).
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ R HR | R HR IHR ]; intros H1.
    * constructor 1; intros; auto.
    * constructor 2; intros x.
      eapply af_mono.
      2: apply (IHR x).
      + intros a b; simpl.
        generalize (H1 b a) (H1 a x); tauto.
      + intros a b.
        generalize (H1 a b) (H1 b x); tauto.
  Qed.

  Variables (R : X -> X -> Prop) (HR : forall x y, R x y \/ ~ R x y).

  Theorem af_hwf_eq : af R <-> hwf (fun x y => ~ R y x).
  Proof.
    split; auto.
    intros H.
    eapply af_mono.
    2: apply hwf_af with (2 := H).
    + intros a b; generalize (HR a b); tauto.
    + intros a b; generalize (HR b a); tauto.
  Qed.

  Theorem hwf_af_eq : hwf R <-> af (fun x y => ~ R y x).
  Proof.
    split; auto.
    intros H.
    eapply hwf_anti.
    2: apply af_hwf with (1 := H).
    intros a b; simpl; tauto.
  Qed.

End af_hwf.

Check af_hwf_eq.
Check hwf_af_eq.
    
