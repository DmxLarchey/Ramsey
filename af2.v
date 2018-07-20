(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import notations sublist utils af.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "R ↓ x" := (fun a b => R a b /\ R x a).
Local Notation "R ↑ x" := (fun a b => R a b \/ R x a).

Section af2.

  Variable (X : Type).
  Implicit Type (R : X -> X -> Prop).

  Inductive af R : Prop :=
    | in_af_0 : (forall a b, R a b)  -> af R
    | in_af_1 : (forall x, af (R↑x)) -> af R.

  Fact af_mono (R S : _ -> _ -> Prop) : (forall x y, R x y -> S x y) -> af R -> af S.
  Proof.
    intros H1 H2; revert H2 S H1.
    induction 1 as [ R HR | R HR IHR ]; intros S H1.
    * constructor 1; auto.
    * constructor 2; intros x.
      apply (IHR x); intros ? ? [|]; [ left | right ]; auto.
  Qed.

  Let new R l := 
    match l with
      | a::b::_ => R a b
      | _ => False
    end.

  Fact af_AF R : af R -> AF (new R).
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    * constructor 2; intros a.
      constructor 2; intros b.
      constructor 1.
      intros l; do 2 right; simpl; auto.
    * constructor 2; intros x.
      generalize (IHR x); apply AF_mono.
      intros [|?[|]]; simpl; tauto.
  Qed.

  Let wen (S : list X -> Prop) a b := S (a::b::nil).

  Let wen_new R a b : wen (new R) a b <-> R a b.
  Proof. cbv; tauto. Qed.

(*  Let new_wen S a b l : new (wen S) (a::b::l) <-> S (a::b::nil).
  Proof. cbv; tauto. Qed. *)

  Let Ar2 (S : list X -> Prop) := forall a b l, S (a::b::nil) <-> S (a::b::l).

  Fact AF_af S : AF S -> Ar2 S -> af (wen S).
  Proof.
    induction 1 as [ S HS | S HS IHS ]; intros Ha.
    * constructor 1; cbv; intros; auto.
    * constructor 2; intros x; red in Ha.
      eapply af_mono.
      2: apply (IHS x).
      + intros a b; cbv; rewrite <- (Ha _ _ (_::_)); tauto.
      + intros a b l.
        do 2 rewrite <- (Ha _ _ (b::_)).
        rewrite <- (Ha _ _ l).
        tauto.
  Qed.

  Theorem af_AF_eq R : af R <-> AF (new R).
  Proof.
    split.
    * apply af_AF.
    * intros H.
      eapply af_mono.
      2: apply AF_af with (1 := H).
      intros a b; apply wen_new.
      intros a b l; simpl; tauto.
  Qed.

End af2.

Section hwf2.

  Variable (X : Type).
  Implicit Type (R : X -> X -> Prop).

  Inductive hwf R : Prop :=
    | in_hwf_0 : (forall a b, ~ R a b) -> hwf R
    | in_hwf_1 : (forall x, hwf (R↓x)) -> hwf R.

  Fact hwf_anti (R S : _ -> _ -> Prop) : (forall x y, S x y -> R x y) -> hwf R -> hwf S.
  Proof.
    intros H1 H2; revert H2 S H1.
    induction 1 as [ R HR | R HR IHR ]; intros S H1.
    * constructor 1; intros a b H; apply (HR a b); auto.
    * constructor 2; intros x.
      apply (IHR x); intros ? ? []; split; auto.
  Qed.

  Let new R l := 
    match l with
      | a::b::l_ => R a b
      | _ => False
    end.

  Fact hwf_HWF R : hwf R -> HWF (new R).
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    * constructor 1.
      intros [|?[|?[|]]]; simpl; auto.
    * constructor 2; intros x.
      generalize (IHR x); apply HWF_anti.
      intros [|?[|?[|]]]; simpl; tauto.
  Qed.

  Let wen (S : list X -> Prop) a b := S (a::b::nil).

  Let wen_new R a b : wen (new R) a b <-> R a b.
  Proof. cbv; tauto. Qed.

(*  Let new_wen S a b l : new (wen S) (a::b::l) <-> S (a::b::nil).
  Proof. destruct l; cbv. tauto. Qed. *)

  Let Ar2 (S : list X -> Prop) := forall a b l, S (a::b::nil) <-> S (a::b::l).

  Fact HWF_hwf S : HWF S -> Ar2 S -> hwf (wen S).
  Proof.
    induction 1 as [ S HS | S HS IHS ]; intros Ha.
    * constructor 1; intros ? ?; apply HS.
    * constructor 2; intros x; red in Ha.
      eapply hwf_anti.
      2: apply (IHS x).
      + intros a b; cbv; rewrite <- (Ha _ _ (_::_)); tauto.
      + intros a b l.
        do 2 rewrite <- (Ha _ _ (b::_)).
        rewrite <- (Ha _ _ l).
        tauto.
  Qed.

  Theorem hwf_HWF_eq R : hwf R <-> HWF (new R).
  Proof.
    split.
    * apply hwf_HWF.
    * intros H.
      eapply hwf_anti.
      2: apply HWF_hwf with (1 := H).
      intros a b; apply wen_new.
      intros a b l; simpl; tauto.
  Qed.

End hwf2.

  