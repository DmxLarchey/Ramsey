(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Relations.

Require Import notations sublist utils bar arity HWF.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x y, A x y -> B x y).

Local Notation "A ⊓ B" := (fun x y => A x y /\ B x y).
Local Notation "A ⊔ B" := (fun x y => A x y \/ B x y).

Definition rel_restr X (P : X -> Prop) (R : X -> X -> Prop) (x y : sig P) := R (proj1_sig x) (proj1_sig y).
Arguments rel_restr {X}.

Local Notation "R ⬇ P" := (rel_restr P R).

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section homogeneous.

  Variable (X : Type) (R : X -> X -> Prop).

  (* homogeneous R (x1::...::xn::nil) iff forall i < j, xi R xj, see homogeneous_spec below *)

  Inductive homogeneous : list X -> Prop :=
    | in_homo_0 : homogeneous nil
    | in_homo_1 : ∀ x l, homogeneous l -> Forall (R x) l -> homogeneous (x::l).
    
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

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Local Notation "R ↓ x" := (fun a b => R a b /\ R b x).

Section hwf_binary.

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
    match rev l with
      | a::b::l_ => R b a
      | _ => False
    end.

  Fact hwf_HWF R : hwf R -> HWF (new R).
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    * constructor 1.
      intros l; rewrite <- (rev_involutive l); generalize (rev l); clear l.
      intros l; unfold new; rewrite rev_involutive; revert l.
      intros [|?[|?[|]]]; simpl; auto.
    * constructor 2; intros x.
      generalize (IHR x); apply HWF_anti.
      intros l; unfold new; rewrite rev_app_distr; simpl.
      destruct (rev l) as [|?[|?[|]]]; simpl; tauto.
  Qed.

  Let wen (S : list X -> Prop) a b := S (a::b::nil).

  Let wen_new R a b : wen (new R) a b <-> R a b.
  Proof. cbv; tauto. Qed.

  Let Ar2 (S : list X -> Prop) := ∀ a b l, S (a::b::nil) <-> S (a::b::l).

  Fact HWF_hwf T : HWF T -> kary 2 (fun l => T (rev l)) -> hwf (wen T).
  Proof.
    induction 1 as [ T HT | T HT IHT ]; intros Ha.
    * constructor 1; intros ? ?; apply HT.
    * constructor 2; intros x; red in Ha; simpl in Ha.
      eapply hwf_anti.
      2: apply (IHT x).
      + intros a b; cbv.
        rewrite (Ha x b (a::nil)); tauto. 
      + intros a b l; simpl.
        rewrite Ha, (Ha x a (b::nil)), (Ha x a (b::l)).
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
      unfold kary, new.
      intros a b l; repeat rewrite rev_involutive; tauto.
  Qed.
  
  (* This is a generalization of Berardi's thm *)

  Theorem hwf_Ramsey R S : hwf R -> hwf S -> hwf (R⊔S).
  Proof.
    do 3 rewrite hwf_HWF_eq; intros H1 H2.
    eapply HWF_anti.
    2: apply HWF_Ramsey with (3 := H1) (4 := H2).
    * intros l; unfold new; destruct (rev l) as [|?[|]]; tauto.
    * do 2 (constructor 2; intros ?); constructor 1.
      intros ? ?; unfold new; repeat (rewrite rev_app_distr; simpl); tauto.
    * do 2 (constructor 2; intros ?); constructor 1.
      intros ? ?; unfold new; repeat (rewrite rev_app_distr; simpl); tauto.
  Qed.

  (* hwf implies no increasing sequence *)

  Fact hwf_seq R : hwf R -> ∀f, (∀ i j, i < j -> R (f j) (f i)) -> False.
  Proof.
    induction 1 as [ R HR | R HR IHR ]; intros f Hf.
    * apply (HR (f 1) (f 0)), Hf; auto.
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

    Fact Acc_hwf x : Acc R x -> hwf (R↓x).
    Proof.
      induction 1 as [ x Hx IHx ].
      constructor 2; intros y.
      destruct (R_ldec y x) as [ H | H ].
      + generalize (IHx _ H); apply hwf_anti; cbv; tauto.
      + constructor 1; tauto.
    Qed.
  
    Theorem well_founded_hwf : well_founded R -> hwf R.
    Proof. intros H; constructor 2; intros x; apply Acc_hwf, H. Qed.

  End wf_hwf.

  Section hwf_wf.

    Fact down_transitive R : transitive _ R -> forall x, transitive _ (R↓x).
    Proof. intros H a x y z H1 H2; specialize (H x y); firstorder. Qed.
  
    Theorem hwf_well_founded R : hwf R -> transitive _ R -> well_founded R.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros H1 a; constructor; intros b Hb.
      + destruct (HR _ _ Hb).
      + specialize (IHR _ (down_transitive H1 a) b).
        induction IHR as [ b Hb' IHb ].
        constructor 1; intros c Hc.
        apply IHb; auto.
        apply H1 with (1 := Hc); auto.
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

  Fact rel_downlift_eq R l x y : (R⇓l) x y <-> R x y /\ Forall (R y) l /\ homogeneous R l.
  Proof.
    revert x y; induction l as [ | a l IHl ]; intros x y; simpl.
    + repeat split; try tauto; constructor.
    + do 2 rewrite IHl.
      repeat rewrite homogeneous_inv.
      repeat rewrite Forall_cons_inv.
      tauto.
  Qed.
  
  Fact homogeneous_downlift R ll x : homogeneous R (ll ++ x :: nil) -> homogeneous (R↓x) ll.
  Proof.
    intros H; apply homogeneous_app_inv in H.
    destruct H as (H1 & _ & H2).
    assert (Forall (fun y => R y x) ll) as H3.
    { rewrite Forall_forall; intros y Hy.
      apply H2; simpl; auto. }
    clear H2; revert H1 x H3.
    induction 1 as [ | x ll H1 H2 IH2 ]; intros y Hy; simpl.
    + constructor.
    + rewrite Forall_cons_inv in Hy.
      destruct Hy as [ H3 H4 ].
      constructor 2; auto.
      revert IH2 H4; repeat rewrite Forall_forall; firstorder.
  Qed.

  Section hwf_homogeneous.

    Let hwf_bar_rec R : hwf R -> ∀ l S, S⇓l ⊆ R -> bar (fun x => ~ homogeneous S x) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_1; intros a.
        apply in_bar_1; intros b.
        apply in_bar_0; intros H.
        apply (HR b a), HS.
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
  
  Definition extends (l m : list X) := exists x, l = x::m.
 
  Definition Hwf R := well_founded (extends⬇(homogeneous R)).
  
  Section Hwf_hwf.
  
    Variable (R : X -> X -> Prop).
    
    Theorem hwf_Hwf : hwf R -> Hwf R.
    Proof.
      induction 1 as [ R HR | R HR IHR ].
      + intros (l & Hl).
        constructor 1; intros (m & H1) (x & Hx); simpl in *; subst.
        constructor 1; intros (m & H2) (y & Hy); simpl in *; subst.
        exfalso; apply homogeneous_two_inv in H2; revert H2; apply HR.
      + intros (l & Hl); constructor 1; intros (m & Hm) (x & Hx); simpl in *; subst.
        assert (exists m y, x::l = m++y::nil) as H1.
        { rewrite <- (rev_involutive l).
          destruct (rev l) as [ | y m ].
          + exists nil, x; auto.
          + exists (x::rev m), y; auto. }
        destruct H1 as (m & y & H1).
        revert Hm; rewrite H1; intros Hm.
        generalize (homogeneous_downlift _ _ Hm); intros H2.
        generalize (IHR y (exist _ m H2)).
        generalize 
        assert (homogeneous (R↓x) l) as H.
        { apply homogeneous_inv, proj1 in Hm.
          rewrite homogeneous_spec in Hl.
          apply homogeneous_spec.
          intros u a v b w E; split.
          
          
      specialize (IHR x (exist _ l Hl)).
  
    Hypothesis R_dec : forall x y, R x y \/ ~ R x y.
  
    Let Hwf_hwf_rec x : Acc (extends⬇(homogeneous R)) x -> hwf (R⇓proj1_sig x).
    Proof.
      induction 1 as [ (m&Hm) H IHm ]; simpl in *.
      constructor 2; intros x.
      destruct (homogeneous_dec R R_dec (x::m)) as [ H1 | H1 ].
      apply (IHm (exist _ _ H1)); exists x; auto.
      constructor 1.
      intros a b; contradict H1; constructor; auto.
      do 2 rewrite rel_downlift_eq in H1; tauto.
    Qed.
 
    Theorem Hwf_hwf : Hwf R -> hwf R.
    Proof. intros H; apply Hwf_hwf_rec with (x := exist _ _ (in_homo_0 R)), H. Qed.
    
  End Hwf_hwf.
  
  Check Hwf_hwf.
    assert (forall l, homogeneous R l -> hwf (R⇓l)) as H1.
    { intros l Hl.
      specialize (H (exist _ l Hl)).
      specialize (
    intros H; constructor 2; intros x.
    specialize (H (exist _ _ (homogeneous_sg R x))).
    
  
  Theorem hwf_Hwf R : hwf R -> Hwf R.
  Proof.
    induction 1 as [ R HR | R HR IHR ].
    + intros (l & Hl).
      constructor; intros (m & Hm) (x & Hx); simpl in *; subst.
      constructor; intros (p & Hp) (y & Hy); simpl in *; subst.
      exfalso; apply homogeneous_two_inv in Hp; revert Hp; apply HR.
    + constructor 
      
      
      

End hwf_binary.

Check well_founded_hwf.
Check hwf_well_founded.

(* gt = fun x y => y < x is homogeneous well-founded *)

Theorem hwf_lt : hwf lt.
Proof.
  apply well_founded_hwf.
  + intros; omega.
  + apply lt_wf.
Qed.

