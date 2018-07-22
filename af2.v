(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Relations.

Require Import notations sublist utils bar af ramsey.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x y, A x y -> B x y).
Local Notation "R ↓ x" := (fun a b => R a b /\ R x a).
Local Notation "R ↑ x" := (fun a b => R a b \/ R x a).

Local Notation "A ⊓ B" := (fun x y => A x y /\ B x y).
Local Notation "A ⊔ B" := (fun x y => A x y \/ B x y).

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section af2.

  Variable (X : Type).
  Implicit Type (R : X -> X -> Prop).

  Inductive af R : Prop :=
    | in_af_0 : (∀ a b, R a b) -> af R
    | in_af_1 : (∀x, af (R↑x)) -> af R.

  Fact af_mono (R S : _ -> _ -> Prop) : R ⊆ S -> af R -> af S.
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

  Let Ar2 (S : list X -> Prop) := ∀ a b l, S (a::b::nil) <-> S (a::b::l).

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

Section homogeneous.

  Variable (X : Type) (R : X -> X -> Prop).

  (* homogeneous R (x1::...::xn::nil) iff forall i < j, xj R xi *)

  Inductive homogeneous : list X -> Prop :=
    | in_homo_0 : homogeneous nil
    | in_homo_1 : ∀ x l, homogeneous l -> Forall (fun y => R y x) l -> homogeneous (x::l).
    
  Fact homogeneous_sg x : homogeneous (x::nil).
  Proof. do 2 constructor. Qed.
    
  Fact homogeneous_inv x l : homogeneous (x::l) <-> Forall (fun y => R y x) l /\ homogeneous l.
  Proof. 
    split. 
    * inversion 1; subst; auto.
    * constructor; tauto. 
  Qed.
  
  Fact homogeneous_app_inv l m : 
         homogeneous (l++m) -> homogeneous l 
                            /\ homogeneous m 
                            /\ ∀ x y, In x l -> In y m -> R y x.
  Proof.
    induction l as [ | x l IHl ]; simpl.
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
  Qed.
 
  Fact homogeneous_two_inv x y l : homogeneous (x::y::l) -> R y x.
  Proof.
    inversion 1; subst.
    inversion H3; subst; auto.
  Qed.

End homogeneous.

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section hwf2.

  Variable (X : Type).
  Implicit Type (R S : X -> X -> Prop).

  Inductive hwf R : Prop :=
    | in_hwf_0 : (forall a b, ~ R a b) -> hwf R
    | in_hwf_1 : (forall x, hwf (R↓x)) -> hwf R.

  Fact hwf_anti R S : S ⊆ R -> hwf R -> hwf S.
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

  Let Ar2 (S : list X -> Prop) := ∀ a b l, S (a::b::nil) <-> S (a::b::l).

  Fact HWF_hwf T : HWF T -> Ar2 T -> hwf (wen T).
  Proof.
    induction 1 as [ T HT | T HT IHT ]; intros Ha.
    * constructor 1; intros ? ?; apply HT.
    * constructor 2; intros x; red in Ha.
      eapply hwf_anti.
      2: apply (IHT x).
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

  Fact hwf_seq R : hwf R -> ∀f, (∀ i j, i < j -> R (f i) (f j)) -> False.
  Proof.
    induction 1 as [ R HR | R HR IHR ]; intros f Hf.
    * apply (HR (f 0) (f 1)), Hf; auto.
    * apply (IHR (f 0) (fun n => f (S n))).
      intros i j Hij; split; apply Hf; omega.
  Qed.

  Corollary hwf_irr R : hwf R -> ∀x, ~ R x x.
  Proof. intros HR x Hx; apply (hwf_seq HR (fun _ => x)); auto. Qed.

  Fact Acc_seq R a : Acc (fun x y => R y x) a -> ∀f, f 0 = a -> (∀i, R (f i) (f (S i))) -> False.
  Proof.
    induction 1 as [ a Ha IHa ]; intros f H1 H2.
    apply (IHa (f 1)) with (f0 := fun n => f (S n)); auto.
    subst; apply H2.
  Qed.

  Fact wf_seq R : well_founded (fun x y => R y x) -> ∀f, (∀i, R (f i) (f (S i))) -> False.
  Proof. intros HR f Hf; apply (@Acc_seq _ _ (HR (f 0)) f); auto. Qed.

  Section wf_hwf.

    Variable R : X -> X -> Prop.

    Hypothesis R_ldec : ∀ x y, R x y \/ ~ R x y.

    Fact Acc_hwf x : Acc (fun u v => R v u) x -> hwf (R↓x).
    Proof.
      induction 1 as [ x Hx IHx ].
      constructor 2; intros y.
      destruct (R_ldec x y) as [ H | H ].
      + generalize (IHx _ H); apply hwf_anti; cbv; tauto.
      + constructor 1; tauto.
    Qed.
  
    Theorem well_founded_hwf : well_founded (fun u v => R v u) -> hwf R.
    Proof. intros H; constructor 2; intros x; apply Acc_hwf, H. Qed.

  End wf_hwf.

  Section hwf_wf.

    Fact down_transitive R : transitive _ R -> forall x, transitive _ (R↓x).
    Proof. intros H a x y z H1 H2; specialize (H x y); firstorder. Qed.
  
    Theorem hwf_well_founded R : hwf R -> transitive _ R -> well_founded (fun x y => R y x).
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros H1 a; constructor; intros b Hb.
      + destruct (HR _ _ Hb).
      + specialize (IHR _ (down_transitive H1 a) b).
        induction IHR as [ b Hb' IHb ].
        constructor 1; intros c Hc.
        apply IHb; auto.
        apply H1 with (1 := Hb); auto.
    Qed.

  End hwf_wf.

  Fixpoint rel_downlift R l :=
    match l with
      | nil  => R
      | x::l => (R⇓l)↓x
    end
  where "R ⇓ l" := (rel_downlift R l).

  Fact downlift_mono R S : R ⊆ S -> ∀x, R↓x ⊆ S↓x.
  Proof. cbv; firstorder. Qed.

  Fact rel_downlift_app R l m : R⇓(l++m) = R⇓m⇓l.
  Proof. induction l; simpl; auto; rewrite IHl; auto. Qed.
 
  Fact rel_downlift_mono R S : R ⊆ S -> ∀l, R⇓l ⊆ S⇓l.
  Proof.
    intros H l; revert R S H; induction l; simpl; intros R S H; auto.
    apply downlift_mono, IHl; auto.
  Qed.

  Fact rel_downlift_eq R l x y : (R⇓l) x y <-> R x y /\ Forall (fun y => R y x) l /\ homogeneous R l.
  Proof.
    revert x y; induction l as [ | a l IHl ]; intros x y; simpl.
    + repeat split; try tauto; constructor.
    + do 2 rewrite IHl.
      repeat rewrite homogeneous_inv.
      repeat rewrite Forall_cons_inv.
      tauto.
  Qed.

  Section hwf_homogeneous.

    Let hwf_bar_rec R : hwf R -> ∀ l S, S⇓l ⊆ R -> bar (fun x => ~ homogeneous S x) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_1; intros a.
        apply in_bar_1; intros b.
        apply in_bar_0; intros H.
        apply (HR a b), HS.
        rewrite rel_downlift_eq.
        rewrite homogeneous_inv, homogeneous_inv, Forall_cons_inv in H.
        tauto.
      * apply in_bar_1; intros x.
        apply (IHR x).
        simpl; intros ? ? []; split; auto.
    Qed.

    Let bar_hwf S l : bar (fun x => ~ homogeneous S x) l -> hwf (S⇓l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * constructor 1; intros x y Hxy.
        rewrite rel_downlift_eq in Hxy.
        apply Hl; tauto.
      * constructor 2; intros; apply IHl.
    Qed.

    Theorem hwf_bar_lift_eq R l : hwf (R⇓l) <-> bar (fun x => ~ homogeneous R x) l.
    Proof.
      split; auto.
      intros H; apply hwf_bar_rec with (R := R⇓l); auto. 
    Qed.

  End hwf_homogeneous.

  Corollary hwf_bar_eq R : hwf R <-> bar (fun x => ~ homogeneous R x) nil.
  Proof. apply hwf_bar_lift_eq with (l := nil). Qed.

End hwf2.

Check well_founded_hwf.
Check hwf_well_founded.

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

  