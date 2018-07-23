(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded.

Require Import notations utils ramsey_paper.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "A ⊇ B" := (∀x, B x -> A x) (only parsing).
Local Notation "A ≃ B" := (A ⊆ B /\ B ⊆ A).

Local Notation "R ⋅ x" := (fun l => R (x::l)).
Local Notation "R ⋄ x" := (fun l => R (l++x::nil)).

Section constant.

  Variable (X : Type) (R : list X -> Prop).
  
  Fact constant_eq : ((∀ l m, R l -> R m) -> (∀ x l, R (x::l) <-> R l))
                  /\ ((∀ x l, R (x::l) <-> R l) -> (∀l, R l <-> R nil))
                  /\ ((∀l, R l <-> R nil) -> (∀ x l, R (l++x::nil) <-> R l))
                  /\ ((∀ x l, R (l++x::nil) <-> R l) -> (∀ l m, R l -> R m)).
                  
  Proof.
    split; [ | split; [ | split ] ]; intros H.
    + split; apply H.
    + intros l; induction l as [ | x l IHl ]; try tauto.
      rewrite H, IHl; tauto.
    + intros x l; rewrite (H l), H; tauto.
    + assert (∀l, R l <-> R nil) as H'.
      { intros l; induction l as [ | x l IHl ] using list_snoc_ind; try tauto.
        rewrite H, IHl; tauto. }
      intros l m; rewrite (H' l), (H' m); tauto.
  Qed.
  
End constant.

Section kary.

  Variable (X : Type).
  
  Implicit Types (R : list X -> Prop).

  Fixpoint kary k R :=
    match k with 
      | 0   => ∀x, R x <-> R nil
      | S k => ∀x, kary k (R⋅x)
    end.

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
  
End kary. 

Section Arity.

  Variable (X : Type).
  Implicit Type (R S : list X -> Prop).

  (** Ar(ity) means ultimately constant but in a non-uniform way contrary to k-ary *)
 
  Inductive Ar R : Prop :=
    | in_Ar_0 : (∀ x l, R (x::l) <-> R l) -> Ar R
    | in_Ar_1 : (∀ x, Ar (R⋅x)) -> Ar R.
    
  Fact Ar_eq R S : R ≃ S -> Ar R -> Ar S.
  Proof.
    intros H1 H2; revert H2 S H1.
    induction 1 as [ R HR | R HR IHR ]; intros S HS.
    + constructor 1; intros x l; split; intros H; apply HS; apply HS in H; revert H; apply HR.
    + constructor 2; intros x; apply (IHR x); split; intro; apply HS.
  Qed.
    
  Fact kary_Ar k R : kary k R -> Ar R.
  Proof.
    revert R; induction k as [ | k IHk ]; simpl; intros R HR.
    + constructor 1; do 3 apply constant_eq; trivial.
    + constructor 2; intro; apply IHk, HR.
  Qed.
    
  Inductive Ar_tail R : Prop :=
    | in_Ar_tail_0 : (∀ x l, R (l++x::nil) <-> R l) -> Ar_tail R
    | in_Ar_tail_1 : (∀ x, Ar_tail (R⋄x)) -> Ar_tail R.
    
  Fact Ar_tail_eq R S : R ≃ S -> Ar_tail R -> Ar_tail S.
  Proof.
    intros H1 H2; revert H2 S H1.
    induction 1 as [ R HR | R HR IHR ]; intros S HS.
    + constructor 1; intros x l; split; intros H; apply HS; apply HS in H; revert H; apply HR.
    + constructor 2; intros x; apply (IHR x); split; intro; apply HS.
  Qed.
  
  Section Ar_Ar_tail.
    
    Let Ar_Ar_tail_rec R : Ar R -> Ar_tail (fun l => R (rev l)).
    Proof.
      induction 1 as [ R HR | R HR IHR ].
      + constructor 1.
        intros x l; rewrite rev_app_distr; simpl; apply HR.
      + constructor 2; intros x.
        eapply Ar_tail_eq.
        2: apply (IHR x); auto.
        split; intro; rewrite rev_app_distr; simpl; auto.
    Qed.
    
    Let Ar_tail_Ar_rec R : Ar_tail R -> Ar (fun l => R (rev l)).
    Proof.
      induction 1 as [ R HR | R HR IHR ].
      + constructor 1.
        intros x l; apply HR.
      + constructor 2; intros x.
        eapply Ar_eq.
        2: apply (IHR x); auto.
        split; intro; simpl; auto.
    Qed.
    
    Fact Ar_Ar_tail R : Ar R <-> Ar_tail (fun l => R (rev l)).
    Proof.
      split; intros H; auto.
      apply Ar_tail_Ar_rec in H.
      revert H; apply Ar_eq.
      split; intro; rewrite rev_involutive; auto.
    Qed.
    
    Fact Ar_tail_Ar R : Ar_tail R <-> Ar (fun l => R (rev l)).
    Proof.
      split; intros H; auto.
      apply Ar_Ar_tail_rec in H.
      revert H; apply Ar_tail_eq.
      split; intro; rewrite rev_involutive; auto.
    Qed.
    
  End Ar_Ar_tail.

  (* Ar(ity) is an instance of Ultimately Stable *)

  Fact Ar_US R : Ar R <-> US (fun R S => R ⊆ S) (fun a R => R⋅a) R.
  Proof.
    split; (induction 1 as [ R HR | ];[ constructor 1; split; apply HR | constructor 2; auto ]).
  Qed.

  (* Ar(ity) is another instance of Ultimately Stable *)

  Fact Ar_US_rev R : Ar R <-> US (fun R S => R ⊇ S) (fun a R => R⋅a) R.
  Proof.
    split; (induction 1 as [ R HR | ];[ constructor 1; split; apply HR | constructor 2; auto ]).
  Qed.
  
  Fact Ar_tail_US_rev R : Ar_tail R <-> US (fun R S => R ⊇ S) (fun a R => R⋄a) R.
  Proof.
    split; (induction 1 as [ R HR | ];[ constructor 1; split; apply HR | constructor 2; auto ]).
  Qed.

End Arity.

