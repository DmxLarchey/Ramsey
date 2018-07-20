(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded.

Require Import notations sublist utils af ramsey.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "R ↓ x" := (fun a b => R a b /\ R x a).
Local Notation "R ↑ x" := (fun a b => R a b \/ R x a).

Local Notation "A ⊓ B" := (fun x y => A x y /\ B x y).
Local Notation "A ⊔ B" := (fun x y => A x y \/ B x y).

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

  Theorem ramsey_2 R S : af R -> af S -> af (R⊓S).
  Proof.
    do 3 rewrite af_AF_eq; intros H1 H2.
    eapply AF_mono.
    2: apply Ramsey_Coquand with (3 := H1) (4 := H2).
    * intros [|?[|]]; cbv; tauto.
    * do 2 (constructor 2; intros ?); constructor 1; cbv; tauto.
    * do 2 (constructor 2; intros ?); constructor 1; cbv; tauto.
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

  Theorem berardi_2 R S : hwf R -> hwf S -> hwf (R⊔S).
  Proof.
    do 3 rewrite hwf_HWF_eq; intros H1 H2.
    eapply HWF_anti.
    2: apply Ramsey_Berardi with (3 := H1) (4 := H2).
    * intros [|?[|]]; cbv; tauto.
    * do 2 (constructor 2; intros ?); constructor 1; cbv; tauto.
    * do 2 (constructor 2; intros ?); constructor 1; cbv; tauto.
  Qed.

  (* hwf implies no increasing sequence *)

  Fact hwf_seq R : hwf R -> forall f : nat -> X, (forall i j, i < j -> R (f i) (f j)) -> False.
  Proof.
    induction 1 as [ R HR | R HR IHR ]; intros f Hf.
    * apply (HR (f 0) (f 1)), Hf; auto.
    * apply (IHR (f 0) (fun n => f (S n))).
      intros i j Hij; split; apply Hf; omega.
  Qed.

  Corollary hwf_irr R : hwf R -> forall x, ~ R x x.
  Proof. intros HR x Hx; apply (hwf_seq HR (fun _ => x)); auto. Qed.

  Fact Acc_seq R a : Acc (fun x y => R y x) a -> forall f, f 0 = a -> (forall i, R (f i) (f (S i))) -> False.
  Proof.
    induction 1 as [ a Ha IHa ]; intros f H1 H2.
    apply (IHa (f 1)) with (f0 := fun n => f (S n)); auto.
    subst; apply H2.
  Qed.

  Fact wf_seq R : well_founded (fun x y => R y x) -> forall f, (forall i, R (f i) (f (S i))) -> False.
  Proof. intros HR f Hf; apply (@Acc_seq _ _ (HR (f 0)) f); auto. Qed.

  Section Acc_hwf.

    Variable R : X -> X -> Prop.

    Hypothesis R_ldec : forall x y, R x y \/ ~ R x y.

    Fact Acc_hwf x : Acc (fun u v => R v u) x -> hwf (R↓x).
    Proof.
      induction 1 as [ x Hx IHx ].
      constructor 2; intros y.
      destruct (R_ldec x y) as [ H | H ].
      + generalize (IHx _ H); apply hwf_anti; cbv; tauto.
      + constructor 1; tauto.
    Qed.
  
    Fact Wellfounded_hwf : well_founded (fun u v => R v u) -> hwf R.
    Proof. intros H; constructor 2; intros x; apply Acc_hwf, H. Qed.

  End Acc_hwf.

  (* Show that hwf implies wf when R is transitive, look in berardi
     if you do not find a simple proof *)
    
  Fact hwf_Acc R : hwf R -> (forall x y z, R x y -> R y z -> R x z) -> well_founded (fun x y => R y x).
  Proof.
    induction 1 as [ R HR | R HR IHR ]; intros H1 a.
    + constructor; intros y Hy; exfalso; apply (HR _ _ Hy).
    + constructor; intros y Hy.
      specialize (IHR y).
      eapply Acc_incl.
      2: apply IHR.
      intros u v.
      2: intros u v w; generalize (H1 u v w); tauto.

      SearchAbout Acc.
      generalize (IHR a y). 
    

End hwf2.

(* gt = fun x y => y < x is homogeneous well-founded *)

Theorem hwf_lt : hwf gt.
Proof.
  constructor 2; intros x.
  induction x as [ x IHx ] using (well_founded_induction lt_wf).
  constructor 2; intros y.
  destruct (le_lt_dec x y) as [ | H ].
  + constructor 1; intros; omega.
  + generalize (IHx _ H); apply hwf_anti; intros; omega.
Qed. 
  
(* Show the link between well_founded and hwf ... 
   maybe only for decidable relations *)

  