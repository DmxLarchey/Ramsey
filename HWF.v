(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import notations sublist utils bar arity ramsey_paper.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "A ⊇ B" := (∀x, B x -> A x) (only parsing).
Local Notation "A ∩ B" := (fun z => A z /\ B z).
Local Notation "A ∪ B" := (fun z => A z \/ B z).

Local Notation "R ⋅ x" := (fun l => R (l++x::nil)).
Local Notation "R ↓ x" := (fun l => R l /\ R (l++x::nil)).

Section rel_lift.

  Variable X : Type.
  
  Implicit Type (R S : list X -> Prop).
  
  Fact down_lift_mono R S : R ⊆ S -> forall x, R↓x ⊆ S↓x.
  Proof. intros H x l; generalize (H l) (H (l++x::nil)); tauto. Qed.

  Hint Resolve down_lift_mono.

  Fixpoint rel_dlift R l :=
    match l with
      | nil  => R
      | x::l => (R⇓l)↓x
    end
  where "R ⇓ l" := (rel_dlift R l).

  Fact rel_dlift_app R l m : R⇓(l++m) = R⇓m⇓l.
  Proof. induction l; simpl; auto; rewrite IHl; auto. Qed.
 
  Fact rel_dlift_mono R S : R ⊆ S -> ∀l, R⇓l ⊆ S⇓l.
  Proof.
    intros H l; revert R S H; induction l; simpl; intros R S H; auto.
    apply down_lift_mono, IHl; auto.
  Qed.
  
  (**
  
  Fact rel_dlift_sl R l m : (R⇓l) m <-> ∀k, k <sl l -> R (m++rev k).
  Proof.
    revert m R.
    induction l as [ | x l IHl ]; intros m R; simpl.
    * split.
      + intros H k Hk.
        apply sublist_nil_inv in Hk; subst; auto.
        simpl; rewrite <- app_nil_end; auto.
      + intros H; rewrite app_nil_end; apply (H nil); constructor.
    * do 2 rewrite IHl; split.
      + intros (H1 & H2) k Hk.
        apply sublist_cons_inv_rt in Hk.
        destruct Hk as [ Hk | (p & H3 & H4) ]; auto.
        subst; simpl; rewrite app_ass; auto.
      + intros H; split; intros k Hk.
        - apply H; constructor 3; auto.
        - replace (rev k++x::m) with (rev (x::k)++m).
          apply H; constructor 2; auto.
          simpl; rewrite app_ass; auto.
  Qed.

  Fact rel_dlift_sl_not R l m : ((fun l => ~ R l)⇓l) m <-> ~ ∃k, k <sl l /\ R (rev k++m).
  Proof.
    rewrite rel_dlift_sl; split.
    + intros H (k & H1 & H2); revert H2; apply H; auto.
    + intros H k Hk; contradict H; exists k; auto.
  Qed.

  *)

End rel_lift.
  
Arguments rel_dlift {X}.
Local Notation "R ⇓ l" := (rel_dlift R l).

Section HWF.

  Variable (X : Type).

  Implicit Type (R S : list X -> Prop).

  (** HWF is an inductive characterization of Homogeneous Well-Founded *)

  Inductive HWF R : Prop := 
    | in_HWF_0 : (∀x, ~ R x)     -> HWF R
    | in_HWF_1 : (∀x, HWF (R↓x)) -> HWF R.

  Fact HWF_anti R S : S ⊆ R -> HWF R -> HWF S.
  Proof.
    intros H1 H2; revert H2 S H1. 
    induction 1 as [ | R HR IHR ]; intros S HS; 
      [ constructor 1 | constructor 2 ]; auto.
    * intros l Hl; apply (H l); auto.
    * intros x; apply (IHR x), down_lift_mono; auto.
  Qed.
  
  (* HWF is an instance of Ultimately Least *)

  Local Fact HWF_UL R : HWF R <-> UF (fun R S => R ⊇ S) (fun R S => R ∩ S) 
                                     (fun _ => False) (fun a R => R⋅a) R.
  Proof.
    split; (induction 1; [ constructor 1 | constructor 2 ]; auto); unfold lattice_eq in *; tauto.
  Qed.

  (* This is an abstract proof of Berardi's result *)
 
  Theorem HWF_Ramsey R S : Ar_tail R -> Ar_tail S -> HWF R -> HWF S -> HWF (R∪S).
  Proof.
    rewrite Ar_tail_US_rev, Ar_tail_US_rev, HWF_UL, HWF_UL, HWF_UL.
    revert R S. 
    apply (@Ramsey_lattice) with (bot := fun _ => True); auto.
    * split. 
      + intros H; split; intros ? ?; apply H; auto.
      + intros H; split; apply H; auto.
    * split; auto; intros [] ? [|]; auto.
    * tauto.
    * tauto.
  Qed.

  (* Homogeneous, what about homogeneous for strict k-ary relations ? *)

  Definition homo S l := ∃m, ∀x, x <sl l -> S (rev x++m).
  
  (*

  Section HWF_bar.

    Let HWF_bar_rec R : HWF R -> ∀ l S, S⇓l ⊆ R -> bar (fun x => ~ homo S x) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_0.
        assert (forall x, ~ (S⇓l) x) as H.
        { intros x Hx; apply (HR x); auto. }
        intros (m & Hm); apply (H m).
        rewrite rel_dlift_sl; auto.
      * apply in_bar_1; intros x.
        apply (IHR x).
        intros m []; split; auto.
    Qed.

    Let bar_HWF R l : bar (fun x => ~ homo R x) l -> HWF (R⇓l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * constructor 1; intros x.
        contradict Hl.
        exists x; rewrite <- rel_dlift_sl; auto.
      * constructor 2; intros; apply IHl.
    Qed.

    Theorem HWF_bar_lift_eq R l : HWF (R⇓l) <-> bar (fun x => ~ homo R x) l.
    Proof.
      split; auto.
      intros H; apply HWF_bar_rec with (R := R⇓l); auto. 
    Qed.

  End HWF_bar.

  (* HWF means bound to become non-homegeneous *)

  Corollary HWF_bar_eq R : HWF R <-> bar (fun x => ~ homo R x) nil.
  Proof. apply HWF_bar_lift_eq with (l := nil). Qed.

  (* R is k-ary strict if R l holds iff l is
     of the form m++r where length m = k and R m *) 
  
  Fixpoint kary_strict k R :=
    match k with 
      | 0   => ∀x, R x <-> R nil
      | S k => ~ R nil /\ forall x, kary_strict k (R⋅x)
    end.
    
  Theorem kary_strict_prefix k R m l : kary_strict k R -> k <= length m -> R m <-> R (m++l).
  Proof.
    revert R m l; induction k as [ | k IHk ]; simpl; intros R m l H1 H2.
    * rewrite (H1 m), (H1 (m++l)); auto.
    * destruct H1 as [ H1 H3 ].
      destruct m as [ | x m ].
      { simpl in H2; omega. }
      simpl in H2; apply le_S_n in H2.
      apply IHk with (1 := H3 x); auto.
  Qed.
  
  Theorem kary_strict_length k R l : kary_strict k R -> R l -> k <= length l.
  Proof.
    revert R l; induction k as [ | k IHk ]; simpl; intros R l.
    * omega.
    * intros (H1 & H2) H3.
      destruct l as [ | x l ].
      { destruct H1; auto. }
      apply IHk with (1 := (H2 x)) in H3; auto.
      simpl; omega.
  Qed.
  
  (* For a strict kary relation, we have a simpler definition of good *)
      
  Theorem good_kary_strict k R l : 
      kary_strict k R -> good R l <-> ∃m, m <sl l /\ R (rev m) /\ length m = k.
  Proof.
    intros H; split.
    * intros H1.
      destruct (H1 nil) as (m & H2 & H3).
      rewrite <- app_nil_end in H3.
      assert (k <= length m) as Hm.
      { rewrite <- rev_length.
        apply kary_strict_length with (1 := H); auto. } 
      destruct list_split_second_half with (1 := Hm) as (m1 & m2 & H4 & H5).
      exists m2; repeat split; auto.
      + apply sl_trans with (2 := H2); subst.
        apply sl_app_left.
      + rewrite kary_strict_prefix with (l := rev m1) (1 := H).
        - rewrite <- rev_app_distr; subst; auto.
        - rewrite rev_length; subst; auto.
    * intros (m & H1 & H2 & H3).
      revert R l m H H1 H2 H3.
      induction k as [ | k IHk ]; simpl; intros R l m H H1 H2 H3 p.
      + exists nil; split.
        - constructor.
        - simpl; revert H2; rewrite (H (rev _)), (H p); auto.
      + destruct H as (H0 & H).
        destruct (list_snoc_destruct m) as [ (x & m' & Hm) | Hm ].
        2: subst; discriminate.
        subst.
        rewrite rev_app_distr in H2; simpl in H2.
        rewrite app_length in H3; simpl in H3.
        assert (length m' = k) as H3' by omega.
        clear H3; rename H3' into H3.
        apply sublist_app_inv_lft in H1.
        destruct H1 as (l1 & l2 & H1 & H4 & H5).
        destruct (IHk _ _ _ (H x) H4 H2 H3 p) as (q & G1 & G2).
        exists (q++x::nil); split.
        - subst; apply sl_app; auto.
        - rewrite rev_app_distr; simpl; auto.
  Qed.

  (* For a strict kary relation, we have a simpler definition of homogeneous *)

  Theorem homo_kary_strict k R l :
      kary_strict k R -> homo R l <-> (exists m, R (rev l++m))
                                   /\ forall m, m <sl l -> length m = k -> R (rev m).
  Proof.
    intros H; split.
    * intros (m & Hm); split.
      + exists m; apply Hm, sl_refl.
      + intros x H1 H2.
        rewrite (kary_strict_prefix R (rev x) m H); auto.
        rewrite rev_length, H2; auto.
    * intros ((m & Hm) & H1); red.
      generalize (kary_strict_length _ _ _ H Hm); intros H2.

    (* probably false *)
  Admitted.
  
  *)
 
End HWF.


