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
Local Notation "A ∩ B" := (fun z => A z /\ B z).
Local Notation "A ∪ B" := (fun z => A z \/ B z).

Local Notation "R ⋅ x" := (fun l => R (x::l)).
Local Notation "R ↑ x" := (fun l => R l \/ R (x::l)).

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section list_lift.

  Variable X : Type.
  
  Implicit Type (R S : list X -> Prop).
  
  Fact one_lift_mono R S : R ⊆ S -> forall x, R↑x ⊆ S↑x.
  Proof. intros H x l; generalize (H l) (H (x::l)); tauto. Qed.

  Hint Resolve one_lift_mono.

  Fixpoint list_lift R l :=
    match l with
      | nil  => R
      | x::l => (R⇑l)↑x
    end
  where "R ⇑ l" := (list_lift R l).

  Fact list_lift_app R l m : R⇑(l++m) = R⇑m⇑l.
  Proof. induction l; simpl; auto; rewrite IHl; auto. Qed.
 
  Fact list_lift_mono R S : R ⊆ S -> forall l, R⇑l ⊆ S⇑l.
  Proof.
    intros H l; revert R S H; induction l; simpl; intros R S H; auto.
    apply one_lift_mono, IHl; auto.
  Qed.
  
  Fact list_lift_spec R l m : (R⇑l) m <-> ∃k, k <sl l /\ R (rev k++m).
  Proof.
    revert m R.
    induction l as [ | x l IHl ]; intros m R; simpl.
    * split.
      + exists nil; split; auto; constructor.
      + intros (l & H1 & H2).
        rewrite sl_nil_inv in H1; subst; auto.
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

End list_lift.
  
Arguments list_lift {X}.
Local Notation "R ⇑ l" := (list_lift R l).

Hint Resolve one_lift_mono list_lift_mono.

Section AF.

  Variable (X : Type).

  Implicit Type (R S : list X -> Prop).

  (** AF is an inductive characterization Almost Full *)

  Inductive AF R : Prop := 
    | in_AF_0 : (∀x, R x)      -> AF R
    | in_AF_1 : (∀x, AF (R↑x)) -> AF R.

  Fact AF_mono R S : R ⊆ S -> AF R -> AF S.
  Proof.
    intros H1 H2; revert H2 S H1. 
    induction 1 as [ | R HR IHR ]; intros S HS; 
      [ constructor 1 | constructor 2 ]; auto.
    intros x; apply (IHR x), one_lift_mono; auto. 
  Qed.

  (* Almost Full is an instance of Ultimately Greatest (ie least for ⊇) *)

  Local Fact AF_UL R : AF R <-> UF (fun R S => R ⊆ S) (fun R S => R ∪ S) 
                                     (fun _ => True) (fun a R => R⋅a) R.
  Proof. 
    split; (induction 1 as [ ? H | ]; [ constructor 1 | constructor 2 ]; auto); 
      unfold lattice_eq in *; auto.
    intros; apply H; auto.
  Qed.
  
  (* This is Ramsey's theorem as in "Stop When you are almost full" but
     proved using the generic lattice based proof of Coquand *)
  
  Theorem AF_Ramsey R S : Ar R -> Ar S -> AF R -> AF S -> AF (R∩S).
  Proof.
    rewrite Ar_US, Ar_US, AF_UL, AF_UL, AF_UL.
    revert R S. 
    apply (@Ramsey_lattice) with (bot := fun _ => False); auto.
    * split; auto; intros [] ? [|]; auto.
    * split; auto; intros H; split; apply H; auto.
    * tauto.
    * tauto.
  Qed.

  (* This seems to be a good definition of good ?
     Is there an equivalent inductive characterization ? 
     
     It comes from list_lift_spec
   *)
  
  Definition GOOD R l := ∀m, ∃k, k <sl l /\ R (rev k++m).
  
  Fact GOOD_list_lift_eq R l : GOOD R l <-> ∀m, (R⇑l) m.
  Proof. split; intros H m; apply list_lift_spec; auto. Qed.
  
  Fact GOOD_nil R : (∀l, R l) -> GOOD R nil.
  Proof. rewrite GOOD_list_lift_eq; auto. Qed.
  
  Fact GOOD_snoc R x l : GOOD (R↑x) l -> GOOD R (l++x::nil).
  Proof.
    do 2 rewrite GOOD_list_lift_eq.
    intros H1 m.
    rewrite list_lift_app; apply H1.
  Qed.
  
  Fact GOOD_mono R S : R ⊆ S -> GOOD R ⊆ GOOD S.
  Proof.
    intros H1 l H2 m; generalize (H2 m).
    intros (k & H3 & H4); exists k; split; auto.
  Qed.
  
  Fact GOOD_app R ll mm : GOOD (R⇑mm) ll -> GOOD R (ll ++ mm).
  Proof.
    revert R; induction mm as [ | x mm IHmm ] using list_snoc_ind; intros R; simpl.
    * rewrite <- app_nil_end; auto.
    * intros H.
      rewrite <- app_ass.
      apply GOOD_snoc, IHmm.
      revert H; apply GOOD_mono.
      rewrite list_lift_app; simpl; auto.
  Qed. 
  
  Fact GOOD_app_left R l m : GOOD R m -> GOOD R (l++m).
  Proof.
    intros H p.
    destruct (H p) as (k & H1 & H2).
    exists k; split; auto.
    apply sl_trans with (1 := H1), sl_app_left.
  Qed.

  Fact GOOD_cons R x l : GOOD R l -> GOOD R (x::l).
  Proof. apply GOOD_app_left with (l := _::nil). Qed.

  Fact GOOD_app_right R l m : GOOD R l -> GOOD R (l++m).
  Proof.
    intros H p.
    destruct (H p) as (k & H1 & H2).
    exists k; split; auto.
    apply sl_trans with (1 := H1), sl_app_right.
  Qed.

  Fact bar_GOOD_nil R : bar (GOOD R) nil <-> ∀l, bar (GOOD R) l.
  Proof. apply bar_nil, GOOD_cons. Qed.

  Section AF_bar_GOOD.

    Let AF_bar_rec R : AF R -> ∀ l S, R ⊆ S⇑l -> bar (GOOD S) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_0.
        apply GOOD_app with (ll := nil), GOOD_mono with (1 := HS), GOOD_nil, HR.
      * apply in_bar_1; intros x.
        apply (IHR x (x::l)), one_lift_mono, HS.
    Qed.
  
    Let bar_AF R l : bar (GOOD R) l -> AF (R⇑l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * constructor 1; apply GOOD_list_lift_eq, Hl.
      * constructor 2; apply IHl.
    Qed.
  
    Theorem AF_bar_lift_eq R l : AF (R⇑l) <-> bar (GOOD R) l.
    Proof.
      split.
      * intros H; apply AF_bar_rec with (1 := H); auto.
      * apply bar_AF.
    Qed.

  End AF_bar_GOOD.

  Inductive subseq : (nat -> X) -> list X -> Prop :=
    | in_ss_0 : forall f, subseq f nil
    | in_ss_1 : forall f l, subseq (fun n => f (S n)) l -> subseq f l
    | in_ss_2 : forall f l, subseq (fun n => f (S n)) l -> subseq f (f 0::l).

  Fact sl_subseq f l m : l <sl m -> subseq f m -> subseq f l.
  Proof.
    intros H1 H2; revert H2 l H1.
    induction 1 as [ f | f m Hm IHm | f m Hm IHm ]; intros l Hl.
    + apply sl_nil_inv in Hl; subst; constructor 1.
    + constructor 2; auto.
    + apply sublist_cons_inv_rt in Hl.
      destruct Hl as [ Hl | (l' & -> & Hl) ].
      * constructor 2; auto.
      * constructor 3; auto.
  Qed.

  Fact pfx_subseq f n : subseq f (pfx f n).
  Proof.
    revert f; induction n; intros; simpl.
     + constructor.
     + constructor 3; auto.
  Qed. 

  Fact subseq_pfx_eq f l : subseq f l <-> exists n, l <sl pfx f n.
  Proof.
    split.
    + induction 1 as [ f | f l Hl IHl | f l Hl IHl ].
      * exists 0; constructor.
      * destruct IHl as (n & Hn).
        exists (S n); simpl; constructor 3; auto.
      * destruct IHl as (n & Hn).
        exists (S n); simpl; constructor 2; auto.
    + intros (n & Hn).
      apply sl_subseq with (1 := Hn).
      apply pfx_subseq.
  Qed.

  Fact bar_GOOD_seq R : bar (GOOD R) nil -> forall f, exists l, subseq f l /\ GOOD R (rev l).
  Proof.
    intros H f.
    apply bar_seq with (f := f) (n := 0) in H; auto.
    destruct H as (k & _ & Hk); exists (rev (pfx_rev f k)); split; auto.
    2: rewrite rev_involutive; auto.
    clear Hk.
    rewrite <- pfx_pfx_rev.
    revert f; induction k as [ | k IHk ]; intros f; simpl.
    + constructor.
    + constructor 3; auto.
  Qed.
  
  Corollary AF_bar_eq R : AF R <-> bar (GOOD R) nil.
  Proof. apply AF_bar_lift_eq with (l := nil). Qed.

  Fact AF_seq R f : AF R -> exists l, subseq f l /\ GOOD R (rev l).
  Proof.
    intros H.
    rewrite AF_bar_eq in H.
    revert H f.
    apply bar_GOOD_seq.
  Qed.

  Corollary bar_list_lift R l : bar (GOOD R) l <-> bar (GOOD (R⇑l)) nil.
  Proof. rewrite <- AF_bar_lift_eq, AF_bar_eq; tauto. Qed.

  (* For a strict kary relation, we have a simpler characterizatino of GOOD *)
      
  Theorem GOOD_kary_strict k R : 
      kary_strict k R -> ∀ll, GOOD R ll <-> ∃m, m <sl ll /\ R (rev m) /\ length m = k.
  Proof.
    rewrite kary_strict_spec; intros H ll; split.
    * intros H1.
      destruct (H1 nil) as (m & H2 & H3).
      rewrite <- app_nil_end in H3.
      rewrite H in H3.
      destruct H3 as (l & r & H3 & H4 & H5).
      exists (rev l).
      rewrite rev_involutive, rev_length; repeat split; auto.
      apply sl_trans with (2 := H2).
      rewrite <- (rev_involutive m), H4.
      apply sl_rev, sl_app_right.
    * intros (m & H1 & H2 & H3) p.
      exists m; split; auto.
      apply H; exists (rev m), p.
      rewrite rev_length; auto.
  Qed.

  Fact AF_seq_strict k R f : kary_strict k R -> AF R -> exists m, subseq f m /\ R m /\ length m = k.
  Proof.
    intros H1 H2.
    apply AF_seq with (f := f) in H2.
    destruct H2 as (l & H2 & H3).
    rewrite GOOD_kary_strict with (1 := H1) in H3.
    destruct H3 as (m & H3 & H4 & H5).
    exists (rev m); rewrite rev_length; repeat split; auto.
    revert H2; apply sl_subseq.
    rewrite <- (rev_involutive l).
    apply sl_rev; auto.
  Qed.

  Fact sl_pfx_cst (x : X) l n : l <sl pfx (fun _ => x) n -> Forall (eq x) l.
  Proof.
    revert l; induction n as [ | n IHn ]; intros l H.
    + apply sl_nil_inv in H; subst; constructor.
    + simpl in H.
      apply sublist_cons_inv_rt in H.
      destruct H as [ H | (l' & -> & H) ]; auto.
  Qed.

  (* There is ONLY ONE unary strict AF relation, up to extentionality of course *)

  Fact AF_unary_strict R : kary_strict 1 R -> AF R -> forall l, R l <-> l <> nil.
  Proof.
    intros H1 H2.
    assert (H3 : forall x, R (x::nil)).
    { intros x.
      destruct AF_seq_strict with (1 := H1) (2 := H2) (f := fun _ : nat => x)
        as (m & H3 & H4 & H5).
      rewrite subseq_pfx_eq in H3.
      destruct H3 as (n & Hn).
      destruct m as [ | u [ | ? ? ] ]; try discriminate.
      assert (E : u = x).
      { clear H4 H5.
        apply sl_pfx_cst in Hn.
        inversion Hn; auto. }
      subst; auto. }
    simpl in H1; destruct H1 as (H0 & H1).
    intros [ | x l ].
    + split; tauto.
    + rewrite H1; split; auto; discriminate.
  Qed.

  Fact AF_unary R : kary 1 R -> AF R -> forall x, R (x::nil).
  Proof.
    intros H1 H2 x.
    apply AF_seq with (f := fun _ => x) in H2.
    destruct H2 as (l & H2 & H3).
    simpl in H1.
    red in H3.
    destruct (H3 (x::nil)) as (k & H4 & H5); auto.
    clear H3.
    apply sl_rev in H4.
    rewrite rev_involutive in H4.
    revert H4 H5; generalize (rev k); clear k; intros k H4 H5.
    destruct k as [ | y k ]; auto.
    assert (Hy : y = x).
    { apply sl_subseq with (1 := H4) in H2.
      apply subseq_pfx_eq in H2.
      destruct H2 as (n & H2).
      apply sl_pfx_cst in H2.
      inversion H2; auto. }
    subst.
    simpl in H5; apply H1 in H5; auto.
  Qed.

End AF.


