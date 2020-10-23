(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded.

Require Import notations ramsey_lattice af HWF.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x, A x -> B x).
Local Notation "A ⊇ B" := (∀x, B x -> A x).
Local Notation "A ∩ B" := (fun z => A z /\ B z).
Local Notation "A ∪ B" := (fun z => A z \/ B z).

(** Check theses defs ... there is a mess arround l++x::nil <~~> x::l **)

Local Notation "R ⋅ x" := (fun l => R (x::l)).
Local Notation "R ↓ x" := (fun l => R l /\ R (x::l)).
Local Notation "R ↑ x" := (fun l => R l \/ R (x::l)).

Section Ramsey_Berardi_Coquand.

  Variable (X : Type).
  Implicit Type (R S : list X -> Prop).

  (** Ar(ity) means ultimately constant but in a non-uniform way contrary to k-ary *)
 
  Inductive Ar R : Prop :=
    | in_Ar_0 : (∀ x l, R (x::l) <-> R l) -> Ar R
    | in_Ar_1 : (∀ x, Ar (R⋅x)) -> Ar R.

  (* Ar(ity) is an instance of Ultimately Stable *)

  Local Fact Ar_US R : Ar R <-> US (fun R S => R ⊆ S) (fun a R => R⋅a) R.
  Proof.
    split; (induction 1 as [ R HR | ];[ constructor 1; split; apply HR | constructor 2; auto ]).
  Qed.

  (* Ar(ity) is another instance of Ultimately Stable *)

  Local Fact Ar_US_rev R : Ar R <-> US (fun R S => R ⊇ S) (fun a R => R⋅a) R.
  Proof.
    split; (induction 1 as [ R HR | ];[ constructor 1; split; apply HR | constructor 2; auto ]).
  Qed.

  (* HWF is an instance of Ultimately Least *)

  Local Fact HWF_UL R : HWF R <-> UL (fun R S => R ⊇ S) (fun R S => R ∩ S) 
                                     (fun _ => False) (fun a R => R⋅a) R.
  Proof.
    split; (induction 1; [ constructor 1 | constructor 2 ]; auto); unfold lattice_eq in *; try tauto.
    + simpl; unfold lift.
  Qed.

  (* Almost Full is an instance of Ultimately Greatest (ie least for ⊇) *)

  Local Fact AF_UL R : AF R <-> UF (fun R S => R ⊆ S) (fun R S => R ∪ S) 
                                     (fun _ => True) (fun a R => R⋅a) R.
  Proof. 
    split; (induction 1 as [ ? H | ]; [ constructor 1 | constructor 2 ]; auto); 
      unfold lattice_eq in *; auto.
    intros; apply H; auto.
  Qed.

  (* We instanciate the result on the distrib. lattice ordered by ⊆ with join ∪, meet ∩ *)
 
  Theorem Ramsey_Berardi R S : Ar R -> Ar S -> HWF R -> HWF S -> HWF (R∪S).
  Proof.
    rewrite Ar_US_rev, Ar_US_rev, HWF_UL, HWF_UL, HWF_UL.
    revert R S. 
    apply (@Ramsey_lattice) with (bot := fun _ => True); auto.
    * split. 
      + intros H; split; intros ? ?; apply H; auto.
      + intros H; split; apply H; auto.
    * split; auto; intros [] ? [|]; auto.
    * tauto.
    * tauto.
  Qed.

  (* We instanciate the result on the distrib. lattice ordered by ⊇ with meet ∪, join ∩ *)

  Theorem Ramsey_Coquand R S : Ar R -> Ar S -> AF R -> AF S -> AF (R∩S).
  Proof.
    rewrite Ar_US, Ar_US, AF_UL, AF_UL, AF_UL.
    revert R S. 
    apply (@Ramsey_lattice) with (bot := fun _ => False); auto.
    * split; auto; intros [] ? [|]; auto.
    * split; auto; intros H; split; apply H; auto.
    * tauto.
    * tauto.
  Qed.

End Ramsey_Berardi_Coquand.

Print Ar.
Print HWF.
Print AF.

Check Ramsey_Berardi.
Print Assumptions Ramsey_Berardi.

Check Ramsey_Coquand.
Print Assumptions Ramsey_Coquand.
