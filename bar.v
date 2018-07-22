(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import notations sublist utils.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).

Section bar.

  Variable (X : Type).

  Implicit Type (P Q : list X -> Prop).

  Inductive bar P l : Prop :=
    | in_bar_0 : P l -> bar P l
    | in_bar_1 : (forall x, bar P (x::l)) -> bar P l.

  Fact bar_mono P Q : P ⊆ Q -> bar P ⊆ bar Q.
  Proof. induction 2; [ constructor 1 | constructor 2 ]; auto. Qed.

  Fact bar_inv P l : bar P l -> P l \/ (forall x, bar P (x::l)).
  Proof. induction 1; auto. Qed.

  Section bar_lift.

    Variables (P : list X -> Prop).

    Let bar_lift1 k : bar P k -> forall u v, k = v++u -> bar (fun v => P (v++u)) v.
    Proof.
      induction 1 as [ l Hl | l Hl IHl ]; intros u v ?; subst.
      * apply in_bar_0; auto.
      * apply in_bar_1; intros a.
        apply (IHl a); auto.
    Qed.
  
    Let bar_lift2 u v : bar (fun v => P (v++u)) v -> bar P (v++u).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * apply in_bar_0; auto.
      * apply in_bar_1; apply IHl.
    Qed.

    Theorem bar_lift u : bar P u <-> bar (fun v => P (v++u)) nil.
    Proof.
      split.
      * intro H; apply bar_lift1 with (1 := H); auto.
      * apply bar_lift2.
    Qed.

    Hypothesis HP : forall x l, P l -> P (x::l).

    Theorem bar_nil : bar P nil <-> forall l, bar P l.
    Proof.
      split; auto.
      intros H l; rewrite app_nil_end; revert H.
      generalize (@nil X); intros m H.
      induction l as [ | x l IHl ]; auto.
      apply bar_inv in IHl; destruct IHl; simpl; auto.
      apply in_bar_0, HP; auto.
    Qed.

  End bar_lift.

  Theorem bar_snoc P x l : bar P (l++x::nil) <-> bar (fun v => P (v++x::nil)) l.
  Proof.
    rewrite bar_lift, (bar_lift _ l).
    split; apply bar_mono; intro; rewrite app_ass; auto.
  Qed.

End bar.

Section bar_relmap.

  Variables (X Y : Type) (f : X -> Y -> Prop) 
            (R : list X -> Prop) (S : list Y -> Prop)
            (Hf : ∀y, ∃x, f x y)                  (* f is surjective *)
            (HRS : ∀ l m, Forall2 f l m -> R l -> S m).  (* f is a morphism form R to S *)

  Theorem bar_relmap l m : Forall2 f l m -> bar R l -> bar S m.
  Proof.
    intros H1 H2; revert H2 m H1 S HRS.
    induction 1 as [ l Hl | l Hl IHl ]; intros m H1 S HRS.
    * constructor 1; revert Hl; apply HRS; auto.
    * constructor 2; intros y.
      destruct (Hf y) as (x & Hx).
      apply (IHl x); auto.
  Qed.
    
End bar_relmap.
