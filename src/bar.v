(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import base.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).

Section prefix.

  Variable X : Type.
 
  Implicit Type (f : nat -> X).

  Fixpoint pfx_rev f n :=
    match n with 
      | 0   => nil
      | S n => f n :: pfx_rev f n
    end.

  Fact pfx_rev_add f a b : pfx_rev f (a+b) = pfx_rev (fun n => f (n+b)) a ++ pfx_rev f b.
  Proof. revert f; induction a; intros f; simpl; f_equal; auto. Qed.

  Fact pfx_rev_ext f g n : (forall i, i < n -> f i = g i) -> pfx_rev f n = pfx_rev g n.
  Proof. induction n; intros H; simpl; f_equal; auto. Qed.

  Fixpoint pfx f n :=
    match n with
      | 0   => nil
      | S n => f 0 :: pfx (fun n => f (S n)) n
    end.

  Fact pfx_add f a b : pfx f (a+b) = pfx f a ++ pfx (fun n => f (a+n)) b.
  Proof.
    revert f; induction a as [ | a IHa ]; intros f; simpl; f_equal; auto; apply IHa.
  Qed.
   
  Fact pfx_pfx_rev f n : pfx f n = rev (pfx_rev f n).
  Proof.
    revert f; induction n as [ | n IHn ]; intros f; auto.
    replace (S n) with (n+1) at 2 by omega.
    rewrite pfx_rev_add; simpl.
    rewrite rev_app_distr; simpl; f_equal.
    rewrite IHn; f_equal.
    apply pfx_rev_ext; intros; f_equal; omega.
  Qed.

End prefix.

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

  Fact bar_seq P l : bar P l -> forall f n, l = pfx_rev f n -> exists k, n <= k /\ P (pfx_rev f k).
  Proof.
    induction 1 as [ l Hl | l Hl IHl ]; intros f n Hn.
    + exists n; subst; auto.
    + subst; destruct (IHl _ _ (S n) eq_refl) as (x & H1 & H2).
      exists x; split; auto; omega.
  Qed.

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

  Variable P : list X -> Prop.

  Theorem bar_Acc l : bar (fun m => ~ P m) l -> ∀ Hl, Acc (extends ⬇ P) (exist _ l Hl).
  Proof.
    induction 1 as [ l H | l H IH ].
    + intros ?; destruct H; auto.
    + intros Hl; constructor 1.
      intros (m & Hm) (x & Hx); simpl in *; subst; auto.
  Qed.

  Hypothesis P_dec : ∀l, P l \/ ~ P l.  

  Theorem Acc_bar l : Acc (extends ⬇ P) l -> bar (fun m => ~ P m) (proj1_sig l).
  Proof.
    induction 1 as [ (l&Hl) H IH ]; simpl.
    constructor 2; intros x.
    destruct (P_dec (x::l)) as [ H1 | H1 ].
    + apply (IH (exist _ _ H1)); exists x; auto.
    + constructor 1; auto.
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
