(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import notations sublist utils bar.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "R ⋅ x" := (fun l => R (x::l)).
Local Notation "R ↓ x" := (fun l => R l /\ R (x::l)).
Local Notation "R ↑ x" := (fun l => R l \/ R (x::l)).

Fact up_lift_mono X (R S : list X -> Prop) : R ⊆ S -> forall x, R↑x ⊆ S↑x.
Proof. intros H x l; generalize (H l) (H (x::l)); tauto. Qed.

Fact down_lift_mono X (R S : list X -> Prop) : R ⊆ S -> forall x, R↓x ⊆ S↓x.
Proof. intros H x l; generalize (H l) (H (x::l)); tauto. Qed.

Hint Resolve up_lift_mono down_lift_mono.

Section HWF_AF.

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
    
  (** AF is an inductive characterization Almost Full *)

  Inductive AF R : Prop := 
    | in_AF_0 : (∀x, R x)      -> AF R
    | in_AF_1 : (∀x, AF (R↑x)) -> AF R.

  Fact AF_mono R S : R ⊆ S -> AF R -> AF S.
  Proof.
    intros H1 H2; revert H2 S H1. 
    induction 1 as [ | R HR IHR ]; intros S HS; 
      [ constructor 1 | constructor 2 ]; auto.
    intros x; apply (IHR x), up_lift_mono; auto. 
  Qed.

End HWF_AF.

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section rel_lift.

  Variable X : Type.
  
  Implicit Type (R S : list X -> Prop).

  Fixpoint rel_ulift R l :=
    match l with
      | nil  => R
      | x::l => (R⇑l)↑x
    end
  where "R ⇑ l" := (rel_ulift R l).

  Fact rel_ulift_app R l m : R⇑(l++m) = R⇑m⇑l.
  Proof. induction l; simpl; auto; rewrite IHl; auto. Qed.
 
  Fact rel_ulift_mono R S : R ⊆ S -> forall l, R⇑l ⊆ S⇑l.
  Proof.
    intros H l; revert R S H; induction l; simpl; intros R S H; auto.
    apply up_lift_mono, IHl; auto.
  Qed.
  
  Fact rel_ulift_sl R l m : (R⇑l) m <-> ∃k, k <sl l /\ R (rev k++m).
  Proof.
    revert m R.
    induction l as [ | x l IHl ]; intros m R; simpl.
    * split.
      + exists nil; split; auto; constructor.
      + intros (l & H1 & H2).
        apply sublist_nil_inv in H1; subst; auto.
    * do 2 rewrite IHl; split.
      + intros [ (k & H1 & H2) | (k & H1 & H2) ].
        - exists k; split; auto; constructor; auto.
        - exists (x::k); split.
          ** constructor; auto.
          ** simpl; rewrite app_ass; auto.
      + intros (k & H1 & H2).
        apply sublist_cons_inv_rt in H1.
        destruct H1 as [ H1 | (k' & H1 & H3) ].
        - left; exists k; auto.
        - subst; right; exists k'; split; auto.
          revert H2; simpl; rewrite app_ass; auto.
  Qed.

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
  
  Fact rel_dlift_sl R l m : (R⇓l) m <-> ∀k, k <sl l -> R (rev k++m).
  Proof.
    revert m R.
    induction l as [ | x l IHl ]; intros m R; simpl.
    * split.
      + intros H k Hk.
        apply sublist_nil_inv in Hk; subst; auto.
      + intros H; apply (H nil); constructor.
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

End rel_lift.
  
Arguments rel_ulift {X}.
Arguments rel_dlift {X}.

Local Notation "R ⇑ l" := (rel_ulift R l).
Local Notation "R ⇓ l" := (rel_dlift R l).

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section good.

  Variable (X : Type).
  
  Implicit Type (R S : list X -> Prop).
  
  (* This seems to be a good definition of good 
     Can we find an equivalent inductive characterization ? *)
  
  Definition good R l := ∀m, ∃k, k <sl l /\ R (rev k++m).
  
  Fact good_rel_ulift_eq R l : good R l <-> ∀m, (R⇑l) m.
  Proof. split; intros H m; apply rel_ulift_sl; auto. Qed.
  
  Fact good_nil R : (∀l, R l) -> good R nil.
  Proof. rewrite good_rel_ulift_eq; auto. Qed.
  
  Fact good_snoc R x l : good (R↑x) l -> good R (l++x::nil).
  Proof.
    do 2 rewrite good_rel_ulift_eq.
    intros H1 m.
    rewrite rel_ulift_app; apply H1.
  Qed.
  
  Fact good_mono R S : R ⊆ S -> good R ⊆ good S.
  Proof.
    intros H1 l H2 m; generalize (H2 m).
    intros (k & H3 & H4); exists k; split; auto.
  Qed.
  
  Fact good_app R ll mm : good (R⇑mm) ll -> good R (ll ++ mm).
  Proof.
    revert R; induction mm as [ | x mm IHmm ] using list_snoc_ind; intros R; simpl.
    * rewrite <- app_nil_end; auto.
    * intros H.
      rewrite <- app_ass.
      apply good_snoc, IHmm.
      revert H; apply good_mono.
      rewrite rel_ulift_app; simpl; auto.
  Qed. 
  
  Fact good_app_left R l m : good R m -> good R (l++m).
  Proof.
    intros H p.
    destruct (H p) as (k & H1 & H2).
    exists k; split; auto.
    apply sl_trans with (1 := H1), sl_app_left.
  Qed.

  Fact good_cons R x l : good R l -> good R (x::l).
  Proof. apply good_app_left with (l := _::nil). Qed.

  Fact good_app_right R l m : good R l -> good R (l++m).
  Proof.
    intros H p.
    destruct (H p) as (k & H1 & H2).
    exists k; split; auto.
    apply sl_trans with (1 := H1), sl_app_right.
  Qed.

  Fact bar_good_nil R : bar (good R) nil <-> ∀l, bar (good R) l.
  Proof. apply bar_nil, good_cons. Qed.

  Section AF_bar.

    Let AF_bar_rec R : AF R -> ∀ l S, R ⊆ S⇑l -> bar (good S) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_0.
        apply good_app with (ll := nil), good_mono with (1 := HS), good_nil, HR.
      * apply in_bar_1; intros x.
        apply (IHR x (x::l)), up_lift_mono, HS.
    Qed.
  
    Let bar_AF R l : bar (good R) l -> AF (R⇑l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * constructor 1; apply good_rel_ulift_eq, Hl.
      * constructor 2; apply IHl.
    Qed.
  
    Theorem AF_bar_lift_eq R l : AF (R⇑l) <-> bar (good R) l.
    Proof.
      split.
      * intros H; apply AF_bar_rec with (1 := H); auto.
      * apply bar_AF.
    Qed.

  End AF_bar.
  
  Corollary AF_bar_eq R : AF R <-> bar (good R) nil.
  Proof. apply AF_bar_lift_eq with (l := nil). Qed.

  Corollary bar_rel_ulift R l : bar (good R) l <-> bar (good (R⇑l)) nil.
  Proof. rewrite <- AF_bar_lift_eq, AF_bar_eq; tauto. Qed.

  (* Homogeneous, what about homogeneous for strict k-ary relations ? *)

  Definition homo S l := ∃m, ∀x, x <sl l -> S (rev x++m).

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
 
End good.


