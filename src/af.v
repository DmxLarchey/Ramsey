(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Wellfounded Relations.

Require Import base bar AF good.

Set Implicit Arguments.

Local Notation "A ⊆ B" := (∀x y, A x y -> B x y).
Local Notation "R ↑ x" := (fun a b => R a b \/ R x a).

Local Notation "A ∩ B" := (fun x y => A x y /\ B x y).
Local Notation "A ∪ B" := (fun x y => A x y \/ B x y).

(** Symbols for copy/paste: ∩ ∪ ⊆ ⊇ ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section af.

  Variable (X : Type).
  Implicit Type (R S : X -> X -> Prop).

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
  
  Section Ramsey.

    Let new R l := 
      match l with
        | a::b::_ => R a b
        | _ => False
      end.

    Let wen (T : list X -> Prop) a b := T (a::b::nil).

    Let wen_new R a b : wen (new R) a b <-> R a b.
    Proof. cbv; tauto. Qed.

    Let af_AF R : af R -> AF (new R).
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

    Let Ar2 (T : list X -> Prop) := ∀ a b l, T (a::b::nil) <-> T (a::b::l).

    Let AF_af T : AF T -> Ar2 T -> af (wen T).
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

    Let af_AF_eq R : af R <-> AF (new R).
    Proof.
      split.
      * apply af_AF.
      * intros H.
        eapply af_mono.
        2: apply AF_af with (1 := H).
        intros a b; apply wen_new.
        intros a b l; simpl; tauto.
    Qed.

    Theorem af_ramsey R S : af R -> af S -> af (R∩S).
    Proof.
      do 3 rewrite af_AF_eq; intros H1 H2.
      eapply AF_mono.
      2: apply AF_Ramsey with (3 := H1) (4 := H2).
      * intros [|?[|]]; cbv; tauto.
      * do 2 (constructor 2; intros ?); constructor 1; cbv; tauto.
      * do 2 (constructor 2; intros ?); constructor 1; cbv; tauto.
    Qed.
    
  End Ramsey.
  
  Fixpoint list_rel_lift R l :=
    match l with
      | nil  => R
      | x::l => (R⇑l)↑x
    end
  where "R ⇑ l" := (list_rel_lift R l).
  
  Fact one_lift_mono R S : R ⊆ S -> forall x, R↑x ⊆ S↑x.
  Proof. cbv; firstorder. Qed.
  
  Fact list_rel_lift_app R l m : R⇑(l++m) = R⇑m⇑l.
  Proof. induction l; simpl; auto; rewrite IHl; auto. Qed.
 
  Fact list_rel_lift_mono R S : R ⊆ S -> forall l, R⇑l ⊆ S⇑l.
  Proof.
    intros H l; revert R S H; induction l; simpl; intros R S H; auto.
    apply one_lift_mono, IHl; auto.
  Qed.
  
  Fact list_rel_lift_spec R l x y : (R⇑l) x y <-> R x y \/ (∃a, In a l /\ R a x) \/ good R l.
  Proof.
    revert x y; induction l as [ | a l IHl ]; intros x y; simpl.
    + rewrite good_nil_inv; firstorder.
    + do 2 rewrite IHl; split.
      * intros [ [ H | [ (b & H1 & H2) | H ] ] | [ H | [ (b & H1 & H2) | H ] ] ]; auto.
        - right; left; exists b; auto.
        - right; right; constructor 2; auto.
        - right; left; exists a; auto.
        - right; right; constructor 1 with b; auto.
        - right; right; constructor 2; auto.
      * intros [ H | [ (b & [ H1 | H1 ] & H2) | H ] ]; subst; auto.
        - left; right; left; exists b; auto.
        - rewrite good_cons_inv in H.
          destruct H as [ (b & H1 & H2) | ]; auto.
          right; right; left; exists b; auto.
  Qed.
  
  Fact good_lift R ll a : good (R↑a) ll -> good R (ll++a::nil).
  Proof.
    induction 1 as [ ll u v H1 [ H2 | H2 ] | ll u H IH ]; simpl.
    * constructor 1 with v; auto; apply in_or_app; auto.
    * apply in_split in H1.
      destruct H1 as (l & r & ?); subst.
      rewrite app_ass; simpl.
      constructor 2; apply good_app_left.
      constructor 1 with a; auto; apply in_or_app; simpl; auto.
    * constructor 2; auto.
  Qed.

  Fact good_list_rel_lift R mm ll : good (R⇑mm) ll -> good R (ll++mm).
  Proof.
    revert ll.
    induction mm as [ | a mm IH ]; simpl; intros ll.
    * rewrite <- app_nil_end; auto.
    * intros H.
      apply good_lift, IH in H.
      revert H.
      rewrite app_ass; simpl; auto.
  Qed.

  Fact good_snoc R ll a : good R (ll++a::nil) <-> good (R↑a) ll \/ ∃x, R a x /\ In x ll.
  Proof.
    split.
    * intros H2.
      apply good_app_inv in H2.
      destruct H2 as [ H2 | [ H2 | H2 ] ].
      - left; revert H2; apply good_mono; auto.
      - apply good_sg_inv in H2; destruct H2.
      - destruct H2 as (x & b & H2 & [ | [] ] & H3); subst b.
        right; exists x; auto.
   * intros [ H | (b & H1 & H2) ].
     - apply good_lift; auto.
     - apply in_split in H2.
       destruct H2 as (l & r & ?); subst.
       rewrite app_ass; simpl.
       apply good_app_left.
       constructor 1 with a; auto.
       apply in_or_app; simpl; auto.
  Qed.
  
  Section af_bar.

    Let af_bar_rec R : af R -> ∀ l S, R ⊆ S⇑l -> bar (good S) l.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros l S HS.
      * apply in_bar_1; intros b.
        apply in_bar_1; intros a.
        apply in_bar_0, good_list_rel_lift with (ll := a::b::nil).
        apply good_mono with (1 := HS).
        constructor 1 with b; simpl; auto.
      * apply in_bar_1; intros x.
        apply (IHR x (x::l)), one_lift_mono, HS.
    Qed.
  
    Let bar_af R l : bar (good R) l -> af (R⇑l).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ].
      * constructor 1; intros; apply list_rel_lift_spec; auto.
      * constructor 2; apply IHl.
    Qed.
  
    Theorem af_bar_lift_eq R l : af (R⇑l) <-> bar (good R) l.
    Proof.
      split.
      * intros H; apply af_bar_rec with (1 := H); auto.
      * apply bar_af.
    Qed.

  End af_bar.
  
  Corollary af_bar_eq R : af R <-> bar (good R) nil.
  Proof. apply af_bar_lift_eq with (l := nil). Qed.

  Corollary bar_rel_ulift R l : bar (good R) l <-> bar (good (R⇑l)) nil.
  Proof. rewrite <- af_bar_lift_eq, af_bar_eq; tauto. Qed.
  
End af.


  