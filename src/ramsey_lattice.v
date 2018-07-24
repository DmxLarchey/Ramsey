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
    double induction principles which are used in the proofs.
    
    We rename the Ar(ity) predicate into US (for Ultimately Stable)
    and the AF (Almost Full) predicate into UF (for Ultimately Full)
    
    For short/easy proofs of lattice (in)equations, we use Setoid 
    rewriting. Maybe some automation could be done here.
    
  *)

Require Import Wellfounded Coq.Setoids.Setoid.

Require Import notations.

Set Implicit Arguments.

(** Symbols for copy/paste: ⊔ ⊓ ⊑ ≡  ⋅ ↑ ↓ ⇑ ⇓ ∀ ∃ *)

Section Ramsey.

  (** We start with some distributive lattice theory *)

  Variable (X : Type) (le : X -> X -> Prop) (lub glb : X -> X -> X) (bot top : X).
  
  Notation "x ⊑ y" := (le x y).

  Definition lattice_eq x y := x ⊑ y /\ y ⊑ x.

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
             
  Add Parametric Relation: (X) (lattice_eq)
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

  Notation lat_eq := lattice_eq.

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

  Fact le_glb_simpl x y : x ⊑ y -> x ⊓ y ≡ x.
  Proof. symmetry; apply le_glb_eq; auto. Qed.

  Fact le_lub_simpl x y : x ⊑ y -> x ⊔ y ≡ y.
  Proof. symmetry; apply le_lub_eq; auto. Qed.

  Fact le_bot_eq x : x ⊑ ⊥ -> x ≡ ⊥.
  Proof. split; auto. Qed.

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

  (* Now we come to the abstract proof of Ramsey by Th. Coquand *)
 
  Variables (A : Type) (op : A -> X -> X).
  
  Notation "x ⋅ a" := (op a x).
  Hypothesis op_mono : ∀ x y a, x ⊑ y -> x⋅a ⊑ y⋅a.
  Hypothesis op_glb  : ∀ x y a, x⋅a ⊓ y⋅a ⊑ (x⊓y)⋅a.
  Hypothesis op_lub  : ∀ x y a, (x⊔y)⋅a ⊑ x⋅a ⊔ y⋅a.
  Hypothesis op_bot  : ∀ a, ⊥⋅a ⊑ ⊥.

  Add Parametric Morphism (a : A): (op a) with signature (lat_eq) ==> (lat_eq) as eq_op.
  Proof. intros ? ? []; split; auto. Qed.
  
  Fact lub_op x y a : (x⊔y)⋅a ≡ x⋅a ⊔ y⋅a.
  Proof. split; auto; lat spec. Qed.
  
  Fact glb_op x y a : (x⊓y)⋅a ≡ x⋅a ⊓ y⋅a.
  Proof. split; auto; lat spec. Qed.
  
  Fact bot_op a : ⊥⋅a ≡ ⊥.
  Proof. split; auto. Qed.
  
  Fact least_op x : x ≡ ⊥ -> ∀a, x⋅a ≡ ⊥.
  Proof. intros H a; simpl; rewrite <- (bot_op a), H; auto. Qed.
  
  Notation stable := (fun x => ∀a, x⋅a ≡ x).
  
  Add Parametric Morphism: (stable) with signature (lat_eq) ==> (iff) as stable_eq.
    Proof. 
      intros x y E; split; intros. 
      + rewrite <- E; auto.
      + rewrite E; auto. 
    Qed.
    
  (** Ultimately stable: lifting x with _⋅a, it ultimately becomes stable *)

  Inductive US x : Prop :=
    | in_US_0 : stable x  -> US x
    | in_US_1 : (∀a, US (x⋅a)) -> US x.

  Section Ramsey_1st_induction.

    (** A double/simultaneous induction principle on US x & US y *)

    Variables (P : X -> X -> Prop)
              (HP0 : ∀ x y, stable x -> P x y)
              (HP1 : ∀ x y, stable y -> P x y)
              (HP2 : ∀ x y, (∀a, P (x⋅a) (y⋅a)) -> P x y).

    Theorem Ramsey_1st_induction x y : US x -> US y -> P x y.
    Proof.
      intros Hx Hy; revert x Hx y Hy.
      induction 1.
      * intros ? _; apply HP0; auto.
      * induction 1.
        + apply HP1; auto.
        + apply HP2; auto.
    Qed.
 
  End Ramsey_1st_induction.

  Definition lift a x := x ⊓ x⋅a.

  Notation "x ↓ a" := (lift a x).
  
  Fact lift_mono x y a : x ⊑ y -> x↓a ⊑ y↓a.
  Proof. intros H; cbv; lat mono. Qed.

  Hint Resolve lift_mono.

  Add Parametric Morphism (a : A): (lift a) with signature (lat_eq) ==> (lat_eq) as lift_morphism.
  Proof. intros ? ? []; split; auto. Qed.
  
  Fact lift_le x a : x↓a ⊑ x.
  Proof. cbv; auto. Qed.
  
  Hint Resolve lift_mono lift_le.
  
  Fact glb_lift x y a : (x⊓y)↓a ≡ x↓a ⊓ y↓a.
  Proof. cbv; split; lat spec; rewrite glb_op; auto. Qed.

  (* Ultimately least: lifting x with ↓a, it ultimately becomes ⊥ *)

  Inductive UL x : Prop := 
    | in_UL_0 : x ≡ ⊥          -> UL x
    | in_UL_1 : (∀a, UL (x↓a)) -> UL x.

  (* UL is antitone *)

  Fact UL_anti x y : UL x -> y ⊑ x -> UL y.
  Proof.
    intros H1; revert H1 y.
    induction 1 as [ x | ? ? IHx ]; intros ? ?.
    * constructor 1; apply le_bot_eq; rewrite <- H; auto.
    * constructor 2; intros a; apply IHx with a; auto.
  Qed.

  Fact UL_anti_alt x y : y ⊑ x -> UL x -> UL y.
  Proof. intros ? H; apply UL_anti with (1 := H); auto. Qed.

 
  Section UL_glb_ind.

    Variables (P : X -> X -> Prop)
              (HP0 : ∀ x y, x⊓y ≡ ⊥ -> P x y)
              (HP1 : ∀ x y, (∀a, UL ((x⊓y)↓a))
                         -> (∀a, P (x↓a) (y↓a))
                         -> P x y).

    Let UL_glb_rec x : UL x -> ∀ y z, y⊓z ⊑ x -> P y z.
    Proof.
      induction 1 as [ x Hx | x Hx IHx ]; intros y z Hyz.
      * apply HP0; apply le_bot_eq; rewrite <- Hx; auto.
      * assert (forall a, (y⊓z)↓a ⊑ x↓a) as H by auto.
        apply HP1.
        - intros a; apply UL_anti with (1 := Hx a); auto.
        - intros a; apply IHx with a.
          apply le_trans with (2 := H a), glb_lift.
    Qed.
    
    Theorem UL_glb_ind : ∀x y, UL (x⊓y) -> P x y.
    Proof. intros ? ? H; apply UL_glb_rec with (1 := H); auto. Qed.

  End UL_glb_ind.
 
  Section UL_glb_induction.

    Variables (r : X)
              (P : X -> Prop)
              (HP1 : ∀x, x⊓r ≡ ⊥ -> P x)
              (HP2 : ∀x,   (∀a, UL (x↓a⊓r↓a))
                        -> (∀a, P  (x↓a⊓r⋅a))
                        -> P x).

    Let UL_glb_rec y : UL y -> forall x, x⊓r ⊑ y -> P x.
    Proof.
      induction 1 as [ y Hy | y Hy IHy ]; intros x Hx.
      * apply HP1; apply le_bot_eq; rewrite <- Hy; auto.
      * assert (forall a, (x⊓r)↓a ⊑ y↓a) as H by auto.
        apply HP2.
        + intros a; eapply UL_anti.
          apply (Hy a).
          apply le_trans with (2 := H a). 
          rewrite glb_lift; auto.
        + intros a; apply IHy with a.
          apply le_trans with (2 := H a).
          rewrite glb_lift, <- glb_assoc, (glb_comm _ r); auto. 
    Qed.

    Theorem UL_glb_induction : ∀x, UL (x⊓r) -> P x.
    Proof. intros ? H; apply UL_glb_rec with (1 := H); auto. Qed.

  End UL_glb_induction.

  Section UL_double_glb_induction.

    Variables (r s : X)
              (P : X -> Prop)
              (HP0 : ∀ x y, x ≡ y -> P x -> P y)
              (HP1 : ∀ x y, x⊓r ≡ ⊥ -> UL (y⊓s) -> P (x⊓y))
              (HP2 : ∀ x y, y⊓s ≡ ⊥ -> UL (x⊓r) -> P (x⊓y))
              (HP3 : ∀ x y, (∀a, P (x↓a ⊓ y ⊓ r⋅a))
                         -> (∀a, P (x ⊓ y↓a ⊓ s⋅a))
                         -> P (x⊓y)).

    Theorem UL_double_glb_induction x y : UL (x⊓r) -> UL (y⊓s) -> P (x⊓y).
    Proof.
      intros Hx; revert y.
      pattern x; revert x Hx.
      apply UL_glb_induction.
      + intros; apply HP1; auto.
      + intros x Hx IHx y Hy.
        pattern y; revert y Hy.
        apply UL_glb_induction.
        - intros y Hy; apply HP2; auto.
          constructor 2; intros a.
          apply UL_anti with (1 := Hx a). 
          rewrite glb_lift; auto.
        - intros y Hy IHy.
          apply HP3.
          * intros a.
            eapply HP0.
            2: apply (IHx a y).
            ++ rewrite <- glb_assoc, (glb_comm _ y), glb_assoc; auto.
            ++ constructor 2; intros b.
               apply UL_anti with (1 := Hy b). 
               rewrite glb_lift; auto.
          * intros a. 
            eapply HP0.
            2: apply (IHy a).
            rewrite glb_assoc; auto.
    Qed.

  End UL_double_glb_induction.

  Section Ramsey_2nd_induction.

    Variables (r s : X)
              (HP1 : ∀ x y, x⊓r ≡ ⊥ -> UL (y⊓s) -> UL (x⊓y⊓(r⊔s)))
              (HP2 : ∀ x y, y⊓s ≡ ⊥ -> UL (x⊓r) -> UL (x⊓y⊓(r⊔s)))
              (HP3 : ∀ x y, (∀a, UL (x↓a ⊓ y ⊓ (r⊔s) ⊓ r⋅a))
                         -> (∀a, UL (x ⊓ y↓a ⊓ (r⊔s) ⊓ s⋅a))
                         -> UL (x⊓y⊓(r⊔s))).

    Let le_01 x y a : x↓a ⊓ y ⊓ (r ⊔ s) ⊓ r⋅a ⊑ x↓a ⊓ y ⊓ r⋅a ⊓ (r ⊔ s).
    Proof. do 2 rewrite <- (glb_assoc (_↓a ⊓ _)); lat mono. Qed.

    Let le_02 x y a : x ⊓ y↓a ⊓ (r ⊔ s) ⊓ s⋅a ⊑ x ⊓ y↓a ⊓ s⋅a ⊓ (r ⊔ s).
    Proof. do 2 rewrite <- (glb_assoc (_ ⊓ _↓a)); lat mono. Qed.

    Theorem Ramsey_2nd_induction : ∀ x y, UL (x⊓r) -> UL (y⊓s) -> UL (x⊓y⊓(r⊔s)).
    Proof.
      apply UL_double_glb_induction with (P := fun u => UL (u⊓(r⊔s))); auto.
      * intros ? ? []; apply UL_anti_alt; auto.
      * intros x y Hx Hy.
        eapply UL_anti.
        apply (@HP3 x y).
        3: auto.
        + intros a; apply UL_anti with (1 := Hx a); auto.
        + intros a; apply UL_anti with (1 := Hy a); auto.
    Qed.

  End Ramsey_2nd_induction.

  Section Ramsey_a_la_Coquand.

    Local Definition lemma_01 := UL_anti_alt.
    
    (* By induction over UL (y⊓s) with fixed x r *)
    
    Hint Resolve least_op.

    Section lemma_02.

      Let le_02_01 x y r s : x ⊓ r ≡ ⊥ -> y ⊓ s ≡ ⊥ -> x ⊓ y ⊓ (r ⊔ s) ≡ ⊥.
      Proof.
        intros H1 H2.
        rewrite glb_comm, glb_distrib, glb_assoc,
                (glb_comm r x), H1, glb_bot, lub_bot, 
                (glb_comm _ y), glb_assoc, 
                (glb_comm _ y), H2, glb_bot; auto.
      Qed.

      Let le_02_02 x y r s a : x ⊓ r ≡ ⊥ -> (x ⊓ y ⊓ (r ⊔ s))↓a ⊑ x ⊓ y↓a ⊓ (r ⊔ s↓a).
      Proof.
        intros H1.
        rewrite (glb_comm x y), <- glb_assoc, (glb_comm x), glb_distrib,
                (glb_comm _ x), H1, lub_bot, glb_lift, glb_lift, 
                (glb_comm (_↓_) (_↓_)), glb_assoc.
        lat mono; rewrite glb_comm; lat mono.
      Qed.

      Local Lemma lemma_02 x y r s : x⊓r ≡ ⊥ -> UL (y⊓s) -> UL (x⊓y⊓(r⊔s)).
      Proof.
        intros H1 H2; pattern y, s; revert y s H2.
        apply UL_glb_ind.
        * intros; constructor 1; auto.
        * intros ? ? ? H3; constructor 2; intros a.
          apply UL_anti with (1 := H3 a); auto.
      Qed.

    End lemma_02.
 
    (* The symmetric version by monotonicity *)
   
    Hint Resolve lemma_02.

    Let lemma_02_sym x y r s : y⊓s ≡ ⊥ -> UL (x⊓r) -> UL (x⊓y⊓(r⊔s)).
    Proof. intros; apply UL_anti with (y⊓x⊓(s⊔r)); auto. Qed.

    (* By induction over UL (A⨅R) *)


    Fact stable_lift_eq x a : stable x -> x↓a ≡ x.
    Proof.
      intros Hx; simpl in Hx.
      unfold lift; rewrite Hx, glb_idem; auto.
    Qed.
    
    Hint Resolve stable_lift_eq.
      
    Fact stable_lift_stable x : stable x -> ∀a, stable (x↓a).
    Proof.
      simpl; intros Hr a b; unfold lift.
      rewrite Hr, glb_idem, Hr; auto.
    Qed.

    Fact stable_op_lub x y a : stable x -> (x⊔y)⋅a ≡ x⊔y⋅a.
    Proof.
      simpl; intros Hx.
      rewrite lub_op, Hx; auto.
    Qed.

    Hint Resolve stable_op_lub stable_lift_stable.

    Fact stable_lift_lub x y a : stable x -> (x⊔y)↓a ≡ x⊔y↓a.
    Proof.
      simpl; intros Hx; unfold lift.
      rewrite lub_op, Hx, lub_comm, (lub_comm x), <- lub_distrib, lub_comm; auto.
    Qed. 

    Hint Resolve stable_lift_lub.

    Section lemma_03.

      Let le_03 x y r s a : stable r -> (x ⊓ y ⊓ (r ⊔ s))↓a ⊑ x↓a ⊓ y ⊓ (r↓a ⊔ s).
      Proof.
        simpl; intros Hr; rewrite glb_lift, glb_lift.
        lat mono.
        rewrite (@stable_lift_eq r); unfold lift; auto.
      Qed.

      Local Lemma lemma_03 x y r s : stable r -> UL (x⊓r) -> UL (y⊓s) -> UL (x⊓y⊓(r⊔s)).
      Proof.
        intros H1 H2 H3; revert H1; pattern x, r; revert x r H2.
        apply UL_glb_ind. 
        * intros; apply lemma_02; auto.
        * intros x r H1 H2 H4; constructor 2; intros a.
          eapply UL_anti.
          apply (H2 a); auto.
          apply le_03; auto.
      Qed.

    End lemma_03.

    Hint Resolve lemma_03.

    (* The symmetric version by monotonicity *)

    Let lemma_03_sym x y r s : stable s -> UL (x⊓r) -> UL (y⊓s) -> UL (x⊓y⊓(r⊔s)). 
    Proof. intros; apply UL_anti with (y⊓x⊓(s⊔r)); auto. Qed.

    Section theorem_04.
    
      Let le_04 x y r s a : (x ⊓ y ⊓ (r ⊔ s))↓a ⊑ x↓a ⊓ y ⊓ (r ⊔ s) ⊓ (x ⊓ y↓a ⊓ (r ⊔ s)) ⊓ (r⋅a ⊔ s⋅a).
      Proof.
        do 2 rewrite glb_lift.
        unfold lift at 3.
        rewrite glb_assoc.
        lat mono.
        rewrite (glb_comm (x ⊓ _)).
        rewrite glb_assoc.
        lat spec; repeat lat left.
      Qed.

      Local Theorem theorem_04 x y r s : US r -> US s -> UL (x⊓r) -> UL (y⊓s) -> UL (x⊓y⊓(r⊔s)).
      Proof.
        intros H1 H2; revert x y.
        pattern r, s; revert r s H1 H2.
        apply Ramsey_1st_induction; intros r s IH; auto.
        apply Ramsey_2nd_induction; intros x y IHx IHy; auto.
        constructor 2; intros a.
        eapply UL_anti.
        apply IH with (1 := IHx a) (2 := IHy a).
        auto.
      Qed.

    End theorem_04.

    Theorem Ramsey_lattice r s : US r -> US s -> UL r -> UL s -> UL (r⊔s).
    Proof.
      intros H1 H2 H3 H4.
      eapply UL_anti.
      apply (@theorem_04 top top _ _ H1 H2).
      revert H3; apply UL_anti_alt; auto.
      revert H4; apply UL_anti_alt; auto.
      repeat rewrite glb_top; auto.
    Qed.

  End Ramsey_a_la_Coquand.

End Ramsey.


  

