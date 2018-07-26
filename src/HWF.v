(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import base bar arity ramsey_paper.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "A ⊇ B" := (∀x, B x -> A x) (only parsing).
Local Notation "A ∩ B" := (fun z => A z /\ B z).
Local Notation "A ∪ B" := (fun z => A z \/ B z).

Local Notation "R ⋅ x" := (fun l => R (l++x::nil)).
Local Notation "R ↓ x" := (fun l => R l /\ R (l++x::nil)).

Section list_down.

  Variable X : Type.
  
  Implicit Type (R S : list X -> Prop).
  
  Fact one_reduce_mono R S : R ⊆ S -> forall x, R↓x ⊆ S↓x.
  Proof. intros H x l; generalize (H l) (H (l++x::nil)); tauto. Qed.

  Hint Resolve one_reduce_mono.

  Fixpoint list_reduce R l :=
    match l with
      | nil  => R
      | x::l => (R⇓l)↓x
    end
  where "R ⇓ l" := (list_reduce R l).

  Fact list_reduce_app R l m : R⇓(l++m) = R⇓m⇓l.
  Proof. induction l; simpl; auto; rewrite IHl; auto. Qed.
 
  Fact list_reduce_mono R S : R ⊆ S -> ∀l, R⇓l ⊆ S⇓l.
  Proof.
    intros H l; revert R S H; induction l; simpl; intros R S H; auto.
    apply one_reduce_mono, IHl; auto.
  Qed.
  
  Fact list_reduce_spec R l m : (R⇓l) m <-> ∀x, x <sl l -> R (m++x).
  Proof.
    revert m R.
    induction l as [ | x l IHl ]; intros m R; simpl.
    * split.
      + intros H k Hk.
        apply sl_nil_inv in Hk; subst; auto.
        simpl; rewrite <- app_nil_end; auto.
      + intros H; rewrite app_nil_end; apply (H nil); constructor.
    * do 2 rewrite IHl; split.
      + intros (H1 & H2) k Hk.
        apply sublist_cons_inv_rt in Hk.
        destruct Hk as [ Hk | (p & H3 & H4) ]; auto.
        subst; generalize (H2 _ H4); rewrite app_ass; auto.
      + intros H; split; intros k Hk.
        - apply H; constructor 3; auto.
        - rewrite app_ass; simpl; apply H.
          constructor; auto. 
  Qed.

  Fact list_reduce_spec_not R l m : ((fun x => ~ R x)⇓l) m <-> ~ ∃x, x <sl l /\ R (m++x).
  Proof.
    rewrite list_reduce_spec; split.
    + intros H (k & H1 & H2); revert H2; apply H; auto.
    + intros H k Hk; contradict H; exists k; auto.
  Qed.

End list_down.
  
Arguments list_reduce {X}.
Local Notation "R ⇓ l" := (list_reduce R l).

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
    * intros x; apply (IHR x), one_reduce_mono; auto.
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

  Definition HOMO R ll := ∃m, ∀x, x <sl ll -> R (m++x).

  Section HWF_bar_not_HOMO.

    Let HWF_bar_rec R : HWF R -> ∀ l S, S⇓l ⊆ R -> bar (fun x => ~ HOMO S x) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_0.
        assert (forall x, ~ (S⇓l) x) as H.
        { intros x Hx; apply (HR x); auto. }
        intros (m & Hm); apply (H m).
        rewrite list_reduce_spec; auto.
      * apply in_bar_1; intros x.
        apply (IHR x).
        intros m []; split; auto.
    Qed.

    Let bar_HWF R l : bar (fun x => ~ HOMO R x) l -> HWF (R⇓l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * constructor 1; intros x.
        contradict Hl.
        exists x; rewrite <- list_reduce_spec; auto.
      * constructor 2; intros; apply IHl.
    Qed.

    Theorem HWF_bar_reduce_eq R l : HWF (R⇓l) <-> bar (fun x => ~ HOMO R x) l.
    Proof.
      split; auto.
      intros H; apply HWF_bar_rec with (R := R⇓l); auto. 
    Qed.

  End HWF_bar_not_HOMO.

  (* HWF means bound to become non-homegeneous *)

  Corollary HWF_bar_eq R : HWF R <-> bar (fun x => ~ HOMO R x) nil.
  Proof. apply HWF_bar_reduce_eq with (l := nil). Qed.

  (* For a strict kary relation, we have a simpler (and bad?) definition of HOMO *)
      
  Theorem HOMO_kary_strict k R : 
      kary_strict k R -> ∀ ll, HOMO R ll <-> ∃m, R m.
  Proof.
    rewrite kary_strict_spec; intros H ll; split.
    * intros (l & Hl).
      specialize (Hl _ (in_sl_0 _)).
      rewrite <- app_nil_end in Hl.
      rewrite H in Hl.
      destruct Hl as (m & r & H1 & H2 & H3).
      exists m; auto.
    * intros (l & H1).
      apply H in H1.
      destruct H1 as (m & r & H1 & H2 & H3).
      exists m; intros x Hx.
      apply H; exists m, x; auto.
  Qed.
  
  (* For a kary-strict relation, the existence of a non homogeneous relations
     is possible only when the relation is empty *)
  
  Theorem HOMO_kary_strict_not k R ll : kary_strict k R -> ~ HOMO R ll -> ∀m, ~ R m.
  Proof.
    intros H; rewrite (HOMO_kary_strict _ _ H); clear H.
    intros H m Hm; apply H; exists m; auto.
  Qed.

End HWF.


