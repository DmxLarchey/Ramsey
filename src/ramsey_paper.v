(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** This is a Coq implementation of the abstract intuitionistic proof 
    of Ramsey's theorem by Thierry Coquand
    
           http://www.cse.chalmers.se/~coquand/ramsey2.pdf 
           
    This implementation follows the argumentation and the notations
    of the paper as faithfully as possible, including the tailored 
    double induction principles which are used in the proofs, and
    upto the symbols chosen.
    
    However,
    
    We rename the Ar(ity) predicate into US (for Ultimately Stable)
    and the AF (Almost Full) predicate into UF (for Ultimately Full)
    
    For short/easy proofs of lattice (in)equations, we use Setoid 
    rewriting. Maybe some automation could be done here.
    
  *)

Require Import Wellfounded Coq.Setoids.Setoid.

Require Import base.

Set Implicit Arguments.

(** Symbols for copy/paste: ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section Ramsey.

  (** We start with some distributive lattice theory *)

  Variable (Σ : Type) (le : Σ -> Σ -> Prop) (lub glb : Σ -> Σ -> Σ) (bot top : Σ).
  
  Notation "x ⊑ y" := (le x y).

  Definition lattice_eq x y := x ⊑ y /\ y ⊑ x.
  
  Notation lat_eq := lattice_eq.

  Notation "x ≡ y" := (lattice_eq x y).
  Notation "x ⊓ y" := (glb x y).
  Notation "x ⊔ y" := (lub x y).
  
  Notation "⊥" := bot.
  Notation "⊤" := top.

  Hypothesis (le_refl : ∀x, x ⊑ x) (le_trans : ∀x y z, x ⊑ y -> y ⊑ z -> x ⊑ z).
  
  Hypothesis (lub_spec : ∀x y z, x ⊔ y ⊑ z <-> x ⊑ z /\ y ⊑ z)
             (glb_spec : ∀x y z, z ⊑ x ⊓ y <-> z ⊑ x /\ z ⊑ y)
             (bot_spec : ∀x, ⊥ ⊑ x)
             (top_spec : ∀x, x ⊑ ⊤).

 (* Notation least := (fun x => x ≡ ⊥). *)
  
  Hint Resolve le_refl.
  
  Fact lattice_eq_refl x : x ≡ x.
  Proof. split; auto. Qed.
  
  Fact lattice_eq_sym x y : x ≡ y -> y ≡ x.
  Proof. intros []; split; auto. Qed.
  
  Fact lattice_eq_trans x y z : x ≡ y -> y ≡ z -> x ≡ z.
  Proof. intros [] []; split; apply le_trans with y; auto. Qed.
  
  Hint Resolve lattice_eq_refl lattice_eq_sym.
             
  Add Parametric Relation: (Σ) (lattice_eq)
      reflexivity proved by lattice_eq_refl
      symmetry proved by lattice_eq_sym
      transitivity proved by lattice_eq_trans
    as lattice_eq_rst. 
    
  Tactic Notation "lat" "sym" := apply eq_sym.
    
  Tactic Notation "lat" "trans" constr(x) := 
    match goal with
      | |- _ ⊑ _ => apply le_trans with x
      | |- _ ≡ _ => apply eq_trans with x
    end; auto.

  Fact lub_inc_lft x y : x ⊑ x ⊔ y.
  Proof. apply (lub_spec x y (x ⊔ y)); auto. Qed.
  
  Fact lub_inc_rt x y : y ⊑ x ⊔ y.
  Proof. apply (lub_spec x y (x ⊔ y)); auto. Qed.
  
  Fact glb_dec_lft x y : x ⊓ y ⊑ x.
  Proof. apply (glb_spec x y (x ⊓ y)); auto. Qed.
  
  Fact glb_dec_rt x y : x ⊓ y ⊑ y.
  Proof. apply (glb_spec x y (x ⊓ y)); auto. Qed.
  
  Hint Resolve le_refl
               lub_inc_lft lub_inc_rt
               glb_dec_lft glb_dec_rt.
               
  Tactic Notation "lat" "left" :=
    match goal with
      | |- _ ⊑ _ ⊔ _ => apply le_trans with (2 := lub_inc_lft _ _)
      | |- _ ⊓ _ ⊑ _ => apply le_trans with (1 := glb_dec_lft _ _)
    end; auto.
    
  Tactic Notation "lat" "right" :=
    match goal with
      | |- _ ⊑ _ ⊔ _ => apply le_trans with (2 := lub_inc_rt _ _)
      | |- _ ⊓ _ ⊑ _ => apply le_trans with (1 := glb_dec_rt _ _)
    end; auto.

  Fact lub_mono x1 x2 y1 y2 : x1 ⊑ y1 -> x2 ⊑ y2 -> x1 ⊔ x2 ⊑ y1 ⊔ y2.
  Proof. intros; apply lub_spec; split; [ lat left | lat right ]. Qed.
  
  Fact glb_mono x1 x2 y1 y2 : x1 ⊑ y1 -> x2 ⊑ y2 -> x1 ⊓ x2 ⊑ y1 ⊓ y2.
  Proof. intros; apply glb_spec; split; [ lat left | lat right ]. Qed.

  Hint Resolve lub_mono glb_mono.

  Add Parametric Morphism: (lub) with signature (lat_eq) ==> (lat_eq) ==> (le) as lattice_le_lub.
  Proof. intros ? ? [] ? ? []; auto. Qed.

  Add Parametric Morphism: (glb) with signature (lat_eq) ==> (lat_eq) ==> (le) as lattice_le_glb.
  Proof. intros ? ? [] ? ? []; auto. Qed.
 
  Add Parametric Morphism: (lub) with signature (lat_eq) ==> (lat_eq) ==> (lat_eq) as lattice_eq_lub.
  Proof. intros ? ? [] ? ? []; split; auto. Qed.

  Add Parametric Morphism: (glb) with signature (lat_eq) ==> (lat_eq) ==> (lat_eq) as lattice_eq_glb.
  Proof. intros ? ? [] ? ? []; split; auto. Qed.

  Add Parametric Morphism: (le) with signature (lat_eq) ==> (lat_eq) ==> (iff) as lattice_eq_le_iff.
  Proof. 
    intros x1 y1 (H1 & H2) x2 y2 (H3 & H4); split; intros H5.
    + apply le_trans with (1 := H2), le_trans with (1 := H5); auto.
    + apply le_trans with (1 := H1), le_trans with (1 := H5); auto.
  Qed.
  
  Tactic Notation "lat" "mono" :=
    match goal with
      | |- _ ⊔ _ ⊑ _ ⊔ _ => apply lub_mono
      | |- _ ⊓ _ ⊑ _ ⊓ _ => apply glb_mono
      | |- _ ⊔ _ ≡ _ ⊔ _ => apply lattice_eq_lub
      | |- _ ⊓ _ ≡ _ ⊓ _ => apply lattice_eq_glb
    end; auto.
    
  Tactic Notation "lat" "spec" :=
    repeat (match goal with
      | |- _ ⊔ _ ⊑ _ => apply lub_spec
      | |- _ ⊑ _ ⊓ _ => apply glb_spec
    end; split; auto).
    
  Tactic Notation "lat" "absurd" := apply le_trans with ⊥; auto.

  Fact lub_comm_le x y : x ⊔ y ⊑ y ⊔ x.    Proof. rewrite lub_spec; split; auto. Qed.
  Fact glb_comm_le x y : x ⊓ y ⊑ y ⊓ x.    Proof. rewrite glb_spec; split; auto. Qed.

  Hint Resolve lub_comm_le glb_comm_le.

  Fact lub_comm x y : x ⊔ y ≡ y ⊔ x.       Proof. split; auto. Qed.
  Fact glb_comm x y : x ⊓ y ≡ y ⊓ x.       Proof. split; auto. Qed.
  
  Hint Immediate lub_comm glb_comm.

  Section idempotent.

    Let lub_idem_le x : x ⊔ x ⊑ x.    Proof. apply lub_spec; auto. Qed.
    Let glb_idem_le x : x ⊑ x ⊓ x.    Proof. apply glb_spec; auto. Qed.
  
    Fact lub_idem x : x ⊔ x ≡ x.      Proof. split; auto. Qed.
    Fact glb_idem x : x ⊓ x ≡ x.      Proof. split; auto. Qed.

  End idempotent.  

  Fact le_lub_bot x y : x ⊑ ⊥ -> y ⊑ ⊥ -> x ⊔ y ⊑ ⊥.
  Proof. intros; rewrite <- (lub_idem ⊥); auto. Qed.
  
  Fact le_top_glb x y : ⊤ ⊑ x -> ⊤ ⊑ y -> ⊤ ⊑ x ⊓ y.
  Proof. intros; rewrite <- (glb_idem ⊤); auto. Qed.

  Section assoc.
  
    Let lub_assoc_1 x y z : x⊔(y⊔z) ⊑ (x⊔y)⊔z.
    Proof.
      apply lub_spec; split; auto.
      apply le_trans with (2 := lub_inc_lft _ _); auto.
    Qed.
    
    Let glb_assoc_1 x y z : x⊓(y⊓z) ⊑ (x⊓y)⊓z.
    Proof.
      apply glb_spec; split; auto.
      apply le_trans with (1 := glb_dec_rt _ _); auto.
    Qed.
  
    Fact lub_assoc x y z : x⊔(y⊔z) ≡ (x⊔y)⊔z.
    Proof.
      split; auto.
      rewrite lub_comm, (lub_comm x), (lub_comm x (y ⊔ z)), (lub_comm y z); auto.
    Qed.

    Fact glb_assoc x y z : x⊓(y⊓z) ≡ (x⊓y)⊓z.
    Proof.
      split; auto.
      rewrite glb_comm, (glb_comm x), (glb_comm x (y ⊓ z)), (glb_comm y z); auto.
    Qed.
 
  End assoc.

  Fact le_glb_eq x y : x ⊑ y <-> x ≡ x ⊓ y.
  Proof.
    split.
    + split; auto; lat spec.
    + intros (H & _); apply le_trans with (1 := H); auto.
  Qed.
  
  Fact le_lub_eq x y : x ⊑ y <-> y ≡ x ⊔ y.
  Proof.
    split.
    + split; auto; lat spec.
    + intros (_ & H); apply le_trans with (2 := H); auto.
  Qed.
  
  Fact glb_lub_eq x y : x ≡ x ⊓ (x ⊔ y).
  Proof. apply le_glb_eq; auto. Qed.

  Fact lub_glb_eq x y : x ≡ x ⊔ (x ⊓ y).
  Proof. rewrite lub_comm; apply le_lub_eq; auto. Qed.

  Fact lub_bot x : ⊥ ⊔ x ≡ x.      Proof. split; auto; lat spec. Qed.
  Fact glb_bot x : ⊥ ⊓ x ≡ ⊥.      Proof. split; auto. Qed.
  Fact lub_top x : ⊤ ⊔ x ≡ ⊤.      Proof. split; auto. Qed.
  Fact glb_top x : ⊤ ⊓ x ≡ x.      Proof. split; auto; lat spec. Qed.

  Fact le_glb_simpl x y : x ⊑ y -> x ⊓ y ≡ x.    Proof. symmetry; apply le_glb_eq; auto. Qed.
  Fact le_lub_simpl x y : x ⊑ y -> x ⊔ y ≡ y.    Proof. symmetry; apply le_lub_eq; auto. Qed.

  Fact le_bot_eq x : x ⊑ ⊥ -> x ≡ ⊥.        Proof. split; auto. Qed.
  Fact le_top_eq x : ⊤ ⊑ x -> x ≡ ⊤.        Proof. split; auto. Qed.

  Hypothesis (distrib : ∀x y z, (x ⊔ y) ⊓ z ⊑ (x ⊓ z) ⊔ (y ⊓ z)).
  
  Fact glb_distrib x y z : (x ⊔ y) ⊓ z ≡ (x ⊓ z) ⊔ (y ⊓ z).
  Proof. split; auto; lat spec. Qed.
  
  Fact lub_distrib x y z : (x ⊓ y) ⊔ z ≡ (x ⊔ z) ⊓ (y ⊔ z).
  Proof. 
    rewrite glb_distrib.
    rewrite (glb_comm x (_ ⊔ _)).
    rewrite (glb_comm z (_ ⊔ _)).
    repeat rewrite glb_distrib.
    rewrite glb_idem, (@le_lub_simpl (y ⊓ z) z); auto.
    rewrite <- lub_assoc, (@le_lub_simpl (z ⊓ x) z); auto.
    rewrite glb_comm; auto.
  Qed.

  Fact distrib_glb_rt x y z : z ⊓ (x ⊔ y) ≡ (z ⊓ x) ⊔ (z ⊓ y).
  Proof. rewrite glb_comm, glb_distrib, glb_comm, (glb_comm _ y); auto. Qed.
  
  Fact distrib_lub_rt x y z : z ⊔ (x ⊓ y) ≡ (z ⊔ x) ⊓ (z ⊔ y).
  Proof. rewrite lub_comm, lub_distrib, lub_comm, (lub_comm _ y); auto. Qed.

  (** Now we come to the abstract proof of Ramsey by Th. Coquand 
      Notation that we now denotes a,b,r,s for elements of type Σ
      whereas lifts are denoted by a[x] where x : X, as done in 
      the paper proof
  *)
 
  Variables (X : Type) (op : X -> Σ -> Σ).
  
  Notation "a ⋅ x" := (op x a).
  Hypothesis op_mono : ∀ a b x, a ⊑ b -> a⋅x ⊑ b⋅x.
  Hypothesis op_glb  : ∀ a b x, a⋅x ⊓ b⋅x ⊑ (a⊓b)⋅x.
  Hypothesis op_lub  : ∀ a b x, (a⊔b)⋅x ⊑ a⋅x ⊔ b⋅x.
  Hypothesis op_bot  : ∀ x, ⊥⋅x ⊑ ⊥.

  Add Parametric Morphism (x : X): (op x) with signature (lat_eq) ==> (lat_eq) as eq_op.
  Proof. intros ? ? []; split; auto. Qed.
  
  Fact lub_op a b x : (a⊔b)⋅x ≡ a⋅x ⊔ b⋅x.
  Proof. split; auto; lat spec. Qed.
  
  Fact glb_op a b x : (a⊓b)⋅x ≡ a⋅x ⊓ b⋅x.
  Proof. split; auto; lat spec. Qed.
  
  Fact bot_op x : ⊥⋅x ≡ ⊥.
  Proof. split; auto. Qed.
  
  Fact least_op a : a ≡ ⊥ -> ∀x, a⋅x ≡ ⊥.
  Proof. intros H x; simpl; rewrite <- (bot_op x), H; auto. Qed.
  
  Notation stable := (fun a => ∀x, a⋅x ≡ a).
  
  Add Parametric Morphism: (stable) with signature (lat_eq) ==> (iff) as stable_eq.
  Proof. 
    intros x y E; split; intros. 
    + rewrite <- E; auto.
    + rewrite E; auto. 
  Qed.
    
  (** Ultimately stable: lifting x with _⋅a, it ultimately becomes stable 
  
      this corresponds to Ar in the paper 
    *)

  Inductive US a : Prop :=
    | in_US_0 : stable a       -> US a
    | in_US_1 : (∀x, US (a⋅x)) -> US a.

  Section Ramsey_1st_induction.

    (** A double/simultaneous induction principle on US r & US s 
    
        First induction principle used in the proof of Theorem 0.4
    *)

    Variables (P : Σ -> Σ -> Prop)
              (HP0 : ∀ r s, stable r -> P r s)
              (HP1 : ∀ r s, stable s -> P r s)
              (HP2 : ∀ r s, (∀x, P (r⋅x) (s⋅x)) -> P r s).

    Theorem Ramsey_1st_induction r s : US r -> US s -> P r s.
    Proof.
      intros H1 H2; revert r H1 s H2.
      induction 1.
      * intros ? _; apply HP0; auto.
      * induction 1.
        + apply HP1; auto.
        + apply HP2; auto.
    Qed.
 
  End Ramsey_1st_induction.

  Definition lift x a := a ⊔ a⋅x.

  Notation "a '[' x ']'" := (lift x a) (at level 11, format "a [ x ]", left associativity).
  
  Fact lift_mono a b : a ⊑ b -> forall x, a[x] ⊑ b[x].
  Proof. intros H x; cbv; lat mono. Qed.

  Hint Resolve lift_mono.

  Add Parametric Morphism (x : X): (lift x) with signature (lat_eq) ==> (lat_eq) as lift_morphism.
  Proof. intros ? ? []; split; auto. Qed.
  
  Fact lift_le a x : a ⊑ a[x] .
  Proof. cbv; auto. Qed.
  
  Hint Resolve lift_le.
  
  Fact lub_lift a b x : (a⊔b)[x] ≡ a[x] ⊔ b[x].
  Proof. cbv; split; lat spec; rewrite lub_op; auto. Qed.
  
  Fact stable_lift_eq a x : stable a -> a[x] ≡ a.
  Proof. intros Hx; simpl in Hx; unfold lift; rewrite Hx, lub_idem; auto. Qed.
    
  Hint Resolve stable_lift_eq.
      
  Fact stable_lift_stable a : stable a -> ∀x, stable (a[x]).
  Proof. simpl; intros Hr x y; unfold lift; rewrite Hr, lub_idem, Hr; auto. Qed.

  Fact stable_op_glb a b x : stable a -> (a⊓b)⋅x ≡ a⊓b⋅x.
  Proof. simpl; intros Hx; rewrite glb_op, Hx; auto. Qed.

  Hint Resolve stable_op_glb stable_lift_stable.

  Fact stable_lift_glb a b x : stable a -> (a⊓b)[x] ≡ a⊓b[x].
  Proof.
    simpl; intros Hx; unfold lift.
    rewrite glb_op, Hx, glb_comm, (glb_comm a), <- glb_distrib, glb_comm; auto.
  Qed. 

  Hint Resolve stable_lift_glb.

  (** Ultimately Full: lifting x with [a], it ultimately becomes ⊤ 
  
      this corresponds to AF in the paper 
   *)

  Inductive UF a : Prop := 
    | in_UF_0 : a ≡ ⊤           -> UF a
    | in_UF_1 : (∀x, UF (a[x])) -> UF a.

  (* UF is monotone *)

  Proposition UF_mono a b : UF a -> a ⊑ b -> UF b.
  Proof.
    intros H1; revert H1 b.
    induction 1 as [ a Ha | ? ? IHa ]; intros ? ?.
    * constructor 1; apply le_top_eq; rewrite <- Ha; auto.
    * constructor 2; intros x; apply IHa with x; auto.
  Qed.

  Corollary UF_mono_alt a b : a ⊑ b -> UF a -> UF b.
  Proof. intros ? H; apply UF_mono with (1 := H); auto. Qed.

  Section UF_lub_ind.
  
    (* This one does not appear directly in the paper but it
       is usefull to show more complicated induction principles,
       typically double inductions on UF (_⊔_) *)

    Variables (P : Σ -> Σ -> Prop)
              (HP0 : ∀ a b, a⊔b ≡ ⊤ -> P a b)
              (HP1 : ∀ a b, (∀x, UF ((a⊔b)[x]))
                         -> (∀x, P (a[x]) (b[x]))
                         -> P a b).

    Let UF_lub_rec a : UF a -> ∀ b c, a ⊑ b⊔c -> P b c.
    Proof.
      induction 1 as [ a Ha | a Ha IHa ]; intros b c Hbc.
      * apply HP0; apply le_top_eq; rewrite <- Ha; auto.
      * generalize (lift_mono Hbc); intros H.
        apply HP1.
        - intros x; apply UF_mono with (2 := H x); auto.
        - intros x; apply IHa with x.
          apply le_trans with (1 := H x), lub_lift.
    Qed.
    
    Theorem UF_lub_ind a b : UF (a⊔b) -> P a b.
    Proof. intros H; apply UF_lub_rec with (1 := H); auto. Qed.

  End UF_lub_ind.
  
  Check UF_lub_ind.
 
  Section UF_lub_induction.
  
    (* This one is used more or less implicitely in the paper
       as a justification for the upcomming UF_double_lub_induction
    
       Notice the condition on P where r[a] is replaced by r⋅a 
       
     *)

    Variables (r : Σ)
              (P : Σ -> Prop)
              (HP1 : ∀a, a⊔r ≡ ⊤ -> P a)
              (HP2 : ∀a,   (∀x, UF (a[x]⊔r[x]))
                        -> (∀x, P  (a[x]⊔r⋅x))
                        -> P a).

    Let UF_lub_rec a : UF a -> forall b, a ⊑ b⊔r -> P b.
    Proof.
      induction 1 as [ a Ha | a Ha IHa ]; intros b Hb.
      * apply HP1; apply le_top_eq; rewrite <- Ha; auto.
      * generalize (lift_mono Hb); intros H.
        apply HP2.
        + intros x; eapply UF_mono.
          apply (Ha x).
          apply le_trans with (1 := H x), lub_lift. 
        + intros x; apply IHa with x.
          apply le_trans with (1 := H x).
          rewrite lub_lift, <- lub_assoc, (lub_comm _ r); auto. 
    Qed.

    Theorem UF_lub_induction a : UF (a⊔r) -> P a.
    Proof. intros H; apply UF_lub_rec with (1 := H); auto. Qed.

  End UF_lub_induction.
  
  Check UF_lub_induction.

  Section UF_double_lub_induction.
  
    (* This one is the most important induction principle of the
       paper. Notice the extensionality condition on P which
       holds when P is UF *)

    Variables (r s : Σ)
              (P : Σ -> Prop)
              (HP0 : ∀ a b, a ≡ b -> P a -> P b)
              (HP1 : ∀ a b, a⊔r ≡ ⊤ -> UF (b⊔s) -> P (a⊔b))
              (HP2 : ∀ a b, b⊔s ≡ ⊤ -> UF (a⊔r) -> P (a⊔b))
              (HP3 : ∀ a b, (∀x, P (a[x] ⊔ b ⊔ r⋅x))
                         -> (∀x, P (a ⊔ b[x] ⊔ s⋅x))
                         -> P (a⊔b)).

    Theorem UF_double_lub_induction a b : UF (a⊔r) -> UF (b⊔s) -> P (a⊔b).
    Proof.
      intros H1; revert b.
      pattern a; revert a H1.
      apply UF_lub_induction; auto.
      intros a Ha IHa b Hb.
      pattern b; revert b Hb.
      apply UF_lub_induction.
      + intros b Hb; apply HP2; auto.
        constructor 2; intros x.
        apply UF_mono with (1 := Ha x).
        rewrite lub_lift; auto.
      + intros b Hb IHb.
        apply HP3.
        * intros x.
          eapply HP0.
          2: apply (IHa x b).
          - rewrite <- lub_assoc, (lub_comm _ b), lub_assoc; auto.
          - constructor 2; intros y.
            apply UF_mono with (1 := Hb y). 
            rewrite lub_lift; auto.
        * intros x. 
          eapply HP0.
          2: apply (IHb x).
          rewrite lub_assoc; auto.
    Qed.

  End UF_double_lub_induction.
  
  Check UF_double_lub_induction.

  Section Ramsey_2nd_induction.
  
    (** This is the instance of UF_double_lub_induction that is
        actually used in the paper, after Ramsey_1st_induction *)

    Variables (r s : Σ)
              (HP1 : ∀ a b, a⊔r ≡ ⊤ -> UF (b⊔s) -> UF (a⊔b⊔(r⊓s)))
              (HP2 : ∀ a b, b⊔s ≡ ⊤ -> UF (a⊔r) -> UF (a⊔b⊔(r⊓s)))
              (HP3 : ∀ a b, (∀x, UF (a[x] ⊔ b ⊔ (r⊓s) ⊔ r⋅x))
                         -> (∀x, UF (a ⊔ b[x] ⊔ (r⊓s) ⊔ s⋅x))
                         -> UF (a⊔b⊔(r⊓s))).
                         
    Theorem Ramsey_2nd_induction : ∀ a b, UF (a⊔r) -> UF (b⊔s) -> UF (a⊔b⊔(r⊓s)).
    Proof.
      apply UF_double_lub_induction with (P := fun u => UF (u⊔(r⊓s))); auto.
      * intros ? ? []; apply UF_mono_alt; auto.
      * intros a b Ha Hb.
        eapply UF_mono.
        apply (@HP3 a b).
        3: auto.
        + intros x; apply UF_mono with (1 := Ha x).
          do 2 rewrite <- (lub_assoc (_[_] ⊔ _)); lat mono.
        + intros x; apply UF_mono with (1 := Hb x).
          do 2 rewrite <- (lub_assoc (_ ⊔ _[_])); lat mono.
    Qed.

  End Ramsey_2nd_induction.
  
  Check Ramsey_2nd_induction.

  Section Ramsey_a_la_Coquand.

    Local Definition lemma_01 := UF_mono_alt.
    
    Hint Resolve least_op.

    Section lemma_02.
    
      (* The next three are somewhat easy with setoid rewriting ... 
         much less with handwritten congruence proofs *)
         
      Let le_02_00 a b r s : a⊔b⊔(r⊓s) ≡ (a⊔r⊔b)⊓(a⊔(b⊔s)).
      Proof.
        rewrite lub_comm, lub_distrib, lub_assoc, (lub_comm r a); lat mono.
        rewrite (lub_comm a), lub_assoc, lub_comm; lat mono.
      Qed.
      
      Let le_02_01 a b r s : a⊔r ≡ ⊤ -> b⊔s ≡ ⊤ -> a⊔b⊔(r⊓s) ≡ ⊤.
      Proof.
        intros H1 H2.
        rewrite le_02_00, H1, H2, lub_top, glb_top, lub_comm, lub_top; auto.
      Qed.

      Let le_02_02 a b r s x : a⊔r ≡ ⊤ -> a ⊔ b[x] ⊔ (r ⊓ s[x]) ⊑ (a ⊔ b ⊔ (r ⊓ s))[x].
      Proof.
        intros H1.
        rewrite (lub_comm a b), <- (lub_assoc b a), (lub_comm a (_⊓_)),
                lub_distrib, (lub_comm r a), H1, glb_top,
                (lub_comm s a), (lub_assoc b), (lub_comm b a),
                lub_lift, lub_lift.
        lat mono.
      Qed.

      (* By induction over UF (b⊔s) with fixed a r *)

      Local Lemma lemma_02 a b r s : a⊔r ≡ ⊤ -> UF (b⊔s) -> UF (a⊔b⊔(r⊓s)).
      Proof.
        intros H1 H2; pattern b, s; revert b s H2.
        apply UF_lub_ind.
        * intros; constructor 1; auto.
        * intros ? ? ? H3; constructor 2; intros x.
          apply UF_mono with (1 := H3 x); auto.
      Qed.

    End lemma_02.
 
    (* The symmetric version by monotonicity *)
   
    Hint Resolve lemma_02.

    Local Corollary lemma_02_sym a b r s : b⊔s ≡ ⊤ -> UF (a⊔r) -> UF (a⊔b⊔(r⊓s)).
    Proof. intros; apply UF_mono with (b⊔a⊔(s⊓r)); auto. Qed.

    (* By induction over UF (a⊔r) *)

    Local Lemma lemma_03 a b r s : stable r -> UF (a⊔r) -> UF (b⊔s) -> UF (a⊔b⊔(r⊓s)).
    Proof.
      intros H1 H2 H3; revert H1; pattern a, r; revert a r H2.
      apply UF_lub_ind. 
      * intros; auto.
      * intros a r H1 H2 H4; constructor 2; intros x.
        eapply UF_mono.
        apply (H2 x); auto.
        rewrite lub_lift, lub_lift; lat mono.
        rewrite (@stable_lift_eq r); unfold lift; auto.
    Qed.

    Hint Resolve lemma_03.

    (* The symmetric version by monotonicity *)

    Local Corollary lemma_03_sym a b r s : stable s -> UF (a⊔r) -> UF (b⊔s) -> UF (a⊔b⊔(r⊓s)).
    Proof. intros; apply UF_mono with (b⊔a⊔(s⊓r)); auto. Qed.
    
    Hint Resolve lemma_02_sym lemma_03_sym.
    
    (** By double induction on US r & US s using Ramsey_1st_induction
        then for fixed r&s, by double induction UF (x⊔r) & UF (y⊔s) using Ramsey_2nd_induction
        
        I did not think it could work this way, but indeed it does, thanks to these
        tailored induction principles.
      *)
    
    Local Theorem theorem_04 a b r s : US r -> US s -> UF (a⊔r) -> UF (b⊔s) -> UF (a⊔b⊔(r⊓s)).
    Proof.
      intros H1 H2; revert a b.
      pattern r, s; revert r s H1 H2.
      apply Ramsey_1st_induction; intros r s IH; auto.
      apply Ramsey_2nd_induction; intros a b IHa IHb; auto.
      constructor 2; intros x.
      eapply UF_mono.
      apply IH with (1 := IHa x) (2 := IHb x).
      do 2 rewrite lub_lift.
      lat spec; lat right.
      unfold lift; rewrite glb_op; auto.
    Qed.

    Theorem Ramsey_lattice r s : US r -> US s -> UF r -> UF s -> UF (r⊓s).
    Proof.
      intros H1 H2 H3 H4.
      eapply UF_mono.
      apply (@theorem_04 ⊥ ⊥ _ _ H1 H2).
      revert H3; apply UF_mono_alt; auto.
      revert H4; apply UF_mono_alt; auto.
      repeat rewrite lub_bot; auto.
    Qed.

  End Ramsey_a_la_Coquand.
  
  Check Ramsey_lattice.

End Ramsey.




  

