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

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section IND.

  Definition IND I (R : I -> I -> Prop) (P : I -> Prop) := forall x, (forall y, R y x -> P y) -> P x.

  Definition IND_in I (D : I -> Prop) (R : I -> I -> Prop) (P : I -> Prop) := forall x, D x -> (forall y, D y -> R y x -> P y) -> P x.
    
  Theorem IND_in_IND I D R P : @IND_in I D R P <-> IND (R⬇D) (P↡D).
  Proof.
    split.
    * intros H (x & Hx) H1; simpl.
      apply (H _ Hx).
      intros y Hy; apply (H1 (exist _ y Hy)).
    * intros H x Hx H1.
      apply (H (exist _ x Hx)).
      intros (y & ?); cbv; auto.
  Qed.
  
  Variable (I : Type) (R : I -> I -> Prop).
  
  Definition wf x := forall P, IND R P -> P x.
  
  Theorem wf_eq_Acc x : wf x <-> Acc R x.
  Proof.
    split.
    * intros H; apply H.
      intro; apply Acc_intro.
    * intros H P HP; revert H.
      induction 1 as [ x _ IHx ].
      apply HP, IHx.
  Qed.

  Theorem well_founded_all_wf : well_founded R <-> forall x, wf x.
  Proof.
    split; intros H x; generalize (H x); apply wf_eq_Acc.
  Qed.

End IND.

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

  (* This is the definition in Berardi's paper *)
 
  Definition Hwf R := well_founded (extends⬇(homogeneous R)).

  Section well_founded_Hwf. 

    Variable (R : X -> X -> Prop).

    Let P y := forall l (Hl : homogeneous R (y::l)), Acc (extends⬇(homogeneous R)) (exist _ _ Hl).
  
    Let HP : IND R P.
    Proof.
      intros y Hy; unfold P in *; intros l Hl.
      constructor; auto.
      intros (p&Hp) (z & ?); simpl in *; subst.
      apply Hy; auto.
      revert Hp; apply homogeneous_two_inv.
    Qed.

    Theorem well_founded_Hwf : well_founded R -> Hwf R.
    Proof.
      rewrite well_founded_all_wf; intros HR.
      assert (forall x, P x) as Hx.
      { intros x; apply (HR x), HP. }
      intros (l & Hl); constructor; auto.
      intros (m & Hm) (y & ?); simpl in *; subst; apply Hx; auto.
    Qed.

  End well_founded_Hwf. 

  Section Hwf_wf.

    Variable (R : X -> X -> Prop).

    (* This proof comes from Berardi's paper ... is there
       a direct proof than doesn't uses wf/IND ? *)

    Theorem Hwf_well_founded : Hwf R -> transitive _ R -> well_founded R.
    Proof.
      rewrite well_founded_all_wf; intros H HR x P HP.
      set (Y l := homogeneous R l /\ match l with nil  => True | y::l => P y end).
      assert (IND_in (homogeneous R) extends Y) as HY.
      { intros [ | y l ] H1 H2; split; simpl; auto.
        apply HP.
        intros z Hz.
        apply (H2 (z::y::l)).
        constructor; auto.
        apply homogeneous_inv, proj1 in H1; constructor; auto.
        revert H1; apply Forall_impl; intro; apply HR; auto.
        exists z; auto. }
      red in H.
      rewrite IND_in_IND in HY.
      specialize (H (exist _ _ (homogeneous_sg R x))).
      rewrite <- wf_eq_Acc in H.
      apply (H _ HY).
    Qed.

  End Hwf_wf.
  
  Section Hwf_hwf.
 
    (** We show the equivalence between Berardi's definition and
        the direct inductive charaterization. We use the bar
        inductive characterization for a wery short proof *)
  
    Variable (R : X -> X -> Prop).

    (* hwf is always stronger than Hwf *)
    
    Theorem hwf_Hwf : hwf R -> Hwf R.
    Proof.
      rewrite hwf_bar_eq, bar_nil.
      + intros H (l & Hl); apply (bar_Acc _ (H l)).
      + intros x m H1; contradict H1.
        rewrite homogeneous_inv in H1; tauto.
    Qed.

    Hypothesis R_dec : forall x y, R x y \/ ~ R x y.

    (* For logically decidable relations, Hwf is equivalent to hwf *)

    Hint Resolve homogeneous_dec.

    Theorem Hwf_hwf : Hwf R -> hwf R.
    Proof.
      rewrite hwf_bar_eq; intro; apply Acc_bar with (l := exist _ _ (in_homo_0 R)); auto.
    Qed.

    Hint Resolve hwf_Hwf Hwf_hwf.
  
    Theorem Hwf_hwf_eq : Hwf R <-> hwf R.
    Proof. split; auto. Qed. 

  End Hwf_hwf.

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

  Section Hwf_Ramsey.
    
    (* Hence very short proof of Berardi's thm for decidable relations *)

    Variables (R S : X -> X -> Prop)
              (HR : forall x y, R x y \/ ~ R x y)
              (HS : forall x y, S x y \/ ~ S x y).

    Theorem Hwf_Ramsey : Hwf R -> Hwf S -> Hwf (R⊔S).
    Proof.
      repeat rewrite Hwf_hwf_eq; auto.
      + apply hwf_Ramsey.
      + intros x y; destruct (HR x y); destruct (HS x y); tauto.
    Qed.

  End Hwf_Ramsey.

End hwf_binary.

Check hwf_Hwf.
Check Hwf_well_founded.
Check hwf_well_founded.

Check hwf_Hwf.
Check Hwf_hwf.
Check well_founded_Hwf.
Check well_founded_hwf.

Check hwf_Ramsey.
Check Hwf_Ramsey.

(* gt = fun x y => y < x is homogeneous well-founded *)

Theorem hwf_lt : hwf lt.
Proof.
  apply well_founded_hwf.
  + intros; omega.
  + apply lt_wf.
Qed.

