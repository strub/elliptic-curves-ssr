(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect eqtype ssrbool ssrnat ssrfun ssralg.
Require Import choice bigop generic_quotient fraction.

(* -------------------------------------------------------------------- *)
Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Import GRing.
Import FracField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Local Notation simp := Monoid.simpm.

Reserved Notation "x // y" (at level 50, no associativity).

(* -------------------------------------------------------------------- *)
Notation "x %:F"  := (tofrac x).
Notation "x // y" := (x%:F / y%:F).

Lemma addr_cross:
  forall (R : zmodType) (x1 x2 y1 y2 : R),
    (x1 - y2 == x2 - y1) = (x1 + y1 == x2 + y2).
Proof.
  move=> R x1 x2 y1 y2.
  by rewrite subr_eq addrAC eq_sym subr_eq eq_sym.
Qed.

Section FieldFracProps.
  Variable K : fieldType.

  Lemma mulf_cross (x1 x2 y1 y2 : K):
    (x1 * x2) * (y1 * y2) = (x1 * y1) * (x2 * y2).
  Proof.
    by rewrite -!mulrA; congr (_ * _); rewrite mulrCA.
  Qed.

  Lemma mulfE (x1 x2 y1 y2 : K) :
    (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2).
  Proof.
    by rewrite invfM !mulrA [x1 / y1 * x2]mulrAC.
  Qed.

  Lemma invfE (x y : K) : (x / y)^-1 = y / x.
  Proof. by rewrite invfM invrK mulrC. Qed.

  Lemma divf_exp (x y : K) n : (x / y) ^+ n = (x ^+ n / y ^+ n).
  Proof. by rewrite exprMn exprVn. Qed.

  Lemma divf_mull (x y z : K) :
    z != 0 -> (z * x) / (z * y) = x / y.
  Proof.
    move=> nz_z; rewrite invfM mulrAC !mulrA.
    by rewrite divff // !simp mulrC.
  Qed.

  Lemma divf_mulr (x y z : K) :
    z != 0 -> (x * z) / (y * z) = x / y.
  Proof.
    by move=> nz_z; rewrite ![_ * z]mulrC divf_mull.
  Qed.

  Lemma divff_eq (n1 n2 d1 d2 : K) :
    d1 * d2 != 0 -> (n1 / d1 == n2 / d2) = (n1 * d2 == n2 * d1).
  Proof.
    rewrite mulf_eq0; case/norP => nz_d1 nz_d2.
    rewrite -subr_eq0 -mulNr addf_div // mulNr.
    rewrite mulf_eq0 invr_eq0 [d1*d2 == 0]mulf_eq0.
    by rewrite (negbTE nz_d1) (negbTE nz_d2) !orbF subr_eq0.
  Qed.

  Lemma divf_neq0 : forall (K : fieldType) (x y : K),
    (x / y != 0) = (x != 0) && (y != 0).
  Proof.
    by move=> K' x y; rewrite mulf_eq0 invr_eq0 negb_or.
  Qed.
End FieldFracProps.

(* -------------------------------------------------------------------- *)
Module FracField.
  Section Props.
    Variable R : idomainType.

    Import fraction.FracField.

    Lemma embed_Ratio (n d : R):
      n // d = \pi_{fraction R} (Ratio n d).
    Proof.
      case: RatioP=> [_|nz_d].
      + rewrite invr0 mulr0 /GRing.zero /=; unlock tofrac.
        by apply/eqP; rewrite -numer0 numden_Ratio // oner_eq0.
      unlock tofrac; rewrite /GRing.inv /GRing.mul /= -pi_inv -pi_mul.
      rewrite /invf /mulf /= !numden_Ratio ?oner_neq0 //.
      by rewrite !simp /Ratio /insubd insubT.
    Qed.

    Definition piE := (@equal_toE, embed_Ratio).

    Lemma Ratio0r: forall x, Ratio 0 x = ratio0 R %[mod {fraction R}].
    Proof.
      move=> x; case: RatioP=> [|nz_x] //=.
      by apply/eqmodP; rewrite /= equivfE /= !simp.
    Qed.

    Lemma fracW:
      forall (P : {fraction R} -> Type),
           (forall (n d : R), d != 0 -> P (n // d))
        -> forall f : {fraction R}, P f.
    Proof.
      move=> P H; elim/quotW=> [[[n d] /= nz_d]].
      move: (H n d nz_d); rewrite piE /=.
      by unlock Ratio; rewrite /insubd insubT.
    Qed.

    Lemma frac_eq:
      forall (x1 x2 y1 y2 : R), y1 * y2 != 0 ->
        ((x1 // y1) == (x2 // y2)) = (x1 * y2 == x2 * y1).
    Proof.
      move=> x1 x2 y1 y2 nz_y; rewrite divff_eq.
      + by rewrite -!rmorphM /= tofrac_eq.
      + by rewrite -!rmorphM /= tofrac_eq0.
    Qed.

    Lemma frac_eq0 (n d : R): (n // d == 0) = (n == 0) || (d == 0).
    Proof. by rewrite mulf_eq0 invr_eq0 !tofrac_eq0. Qed.

    Lemma frac_mull (p q r : R): r != 0 -> (r * p) // (r * q) = p // q.
    Proof.
      by move=> nz_r; rewrite !tofracM divf_mull ?tofrac_eq0.
    Qed.
  End Props.
End FracField.

Import FracField.

(* -------------------------------------------------------------------- *)
Module InjRMorphism.
  Section ClassDef.
    Variable R S : ringType.

    Definition mixin_of (f : R -> S) := injective f.

    Record class_of f : Prop := Class {
      base  : rmorphism f;
      mixin : mixin_of f
    }.

    Local Coercion base : class_of >-> rmorphism.

    Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.
    Local Coercion apply : map >-> Funclass.

    Variables (phRS : phant (R -> S)) (f g : R -> S) (cF : map phRS).

    Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

    Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
      @Pack phRS f fM.

    Definition pack (fI : mixin_of f) :=
      fun (bF : RMorphism.map phRS) fM & phant_id (RMorphism.class bF) fM =>
        Pack phRS (Class fM fI).

    Canonical rmorphism := RMorphism.Pack phRS class.
  End ClassDef.

  Module Exports.
    Notation injrmorphism f := (class_of f).

    Coercion base  : injrmorphism >-> RMorphism.class_of.
    Coercion mixin : injrmorphism >-> mixin_of.
    Coercion apply : map >-> Funclass.

    Notation InjRMorphism fI := (Pack (Phant _) fI).
    Notation AddInjRMorphism fI := (pack fI id).

    Notation "{ 'rimorphism' fR }" := (map (Phant fR))
      (at level 0, format "{ 'rimorphism'  fR }") : ring_scope.

    Coercion rmorphism : map >-> RMorphism.map.
    Canonical rmorphism.
  End Exports.
End InjRMorphism.

Export InjRMorphism.Exports.

Section InjRMorphismTheory.
  Variable R S : ringType.
  Variable f   : {rimorphism R -> S}.

  Lemma rimorph_inj: injective f.
  Proof. by case: f=> fa []. Qed.

  Lemma rimorph_eq0 (x : R): (f x == 0) = (x == 0).
  Proof.
    apply/eqP/eqP; last by move=> ->; rewrite rmorph0.
    by rewrite -{1}[0](rmorph0 f); move/rimorph_inj.
  Qed.
End InjRMorphismTheory.

(* -------------------------------------------------------------------- *)
Section RatioLiftDef.
  Variable R S : idomainType.
  Variable f : R -> S.

  Definition rliftf (r : {ratio R}) : {ratio S} :=
    Ratio (f \n_r) (f \d_r).

  Definition rlift :=
    lift_op11 {fraction R} {fraction S} rliftf.
End RatioLiftDef.

(* -------------------------------------------------------------------- *)
Section RatioLiftMorph.
  Variable R S : idomainType.
  Variable f : R -> S.

  Hypothesis fM : multiplicative f.
  Hypothesis f_eq0 : forall x, (f x == 0) = (x == 0).

  Local Notation rliftf := (rliftf f).
  Local Notation rlift  := (rlift  f).

  Lemma pi_M_rlift:
    forall x, \pi_{fraction S} (rliftf x) = rlift (\pi_{fraction R} x).
  Proof.
    move=> x2; unlock rlift; set x1 := (repr _).
    have: (x1 = x2 %[mod {fraction _}]) by rewrite reprK.
    case: x2 x1 => [[n2 d2] /= nz_d2] [[n1 d1] /= nz_d1] /=.
    move/eqmodP => /=; rewrite equivfE /= => /eqP eqE.
    rewrite /rliftf /=; apply/eqmodP=> /=; rewrite equivfE.
    by rewrite !numden_Ratio ?f_eq0 // -!fM mulrC -eqE mulrC.
  Qed.

  Canonical pi_M_rlift_morph := PiMorph11 pi_M_rlift.

  Lemma M_rliftF (r : R): rlift (r%:F) = (f r)%:F.
  Proof.
    by rewrite !piE /rliftf /= !numden_Ratio ?oner_neq0 ?fM.
  Qed.

  Lemma M_rliftE (n d : R): rlift (n // d) = (f n) // (f d).
  Proof.
    have f0: f 0 = 0 by (apply/eqP; rewrite f_eq0 eqxx).
    rewrite !piE /rliftf /=; case: (RatioP n d).
    + by move=> z_d; rewrite !(f0, Ratio0) Ratio0r.
    + by move=> nz_d; rewrite !numden_Ratio.
  Qed.

  Lemma M_rlift_is_multiplicative: multiplicative rlift.
  Proof.
    split; last by rewrite -tofrac1 M_rliftF fM.
    elim/fracW=> n1 d1 nz_d1; elim/fracW=> n2 d2 nz_d2.
    by rewrite !M_rliftE !mulf_div -!tofracM -!fM M_rliftE.
  Qed.
End RatioLiftMorph.

(* -------------------------------------------------------------------- *)
Section RatioLiftTheory.
  Variable R S : idomainType.
  Variable f : {rimorphism R -> S}.

  Local Notation rliftf := (rliftf f).
  Local Notation rlift  := (rlift  f).

  Lemma pi_rlift:
    forall x,
      \pi_{fraction S} (rliftf x) = rlift (\pi_{fraction R} x).
  Proof. by apply: pi_M_rlift; [apply: rmorphismMP | apply: rimorph_eq0]. Qed.

  Canonical pi_rlift_morph := PiMorph11 pi_rlift.

  Lemma rliftF (r : R): rlift (r%:F) = (f r)%:F.
  Proof. by apply: M_rliftF; [apply: rmorphismMP | apply: rimorph_eq0]. Qed.

  Lemma rliftE (n d : R): rlift (n // d) = (f n) // (f d).
  Proof. by apply: M_rliftE; [apply: rmorphismMP | apply: rimorph_eq0]. Qed.

  Lemma rlift_is_additive: additive rlift.
  Proof.
    elim/fracW=> n1 d1 nz_d1; elim/fracW=> n2 d2 nz_d2.
    rewrite !rliftE -!mulNr !addf_div ?tofrac_eq0 ?rimorph_eq0 //.
    by rewrite -!(rmorphM, rmorphD, rmorphN) /= !mulNr rliftE.
  Qed.
  Canonical rlift_additive := Additive rlift_is_additive.

  Lemma rlift_is_multiplicative: multiplicative rlift.
  Proof.
    by apply: M_rlift_is_multiplicative;
      [apply: rmorphismMP | apply: rimorph_eq0].
  Qed.
  Canonical rlift_rmorphism := AddRMorphism rlift_is_multiplicative.

  Lemma rlift0     : 0%:F = 0 :> {fraction R}.    Proof. exact: rmorph0. Qed.
  Lemma rliftN     : {morph rlift: x / - x}.      Proof. exact: rmorphN. Qed.
  Lemma rliftD     : {morph rlift: x y / x + y}.  Proof. exact: rmorphD. Qed.
  Lemma rliftB     : {morph rlift: x y / x - y}.  Proof. exact: rmorphB. Qed.
  Lemma rliftMn  n : {morph rlift: x / x *+ n}.   Proof. exact: rmorphMn. Qed.
  Lemma rliftMNn n : {morph rlift: x / x *- n}.   Proof. exact: rmorphMNn. Qed.
  Lemma rlift1     : 1%:F = 1 :> {fraction R}.    Proof. exact: rmorph1. Qed.
  Lemma rliftM     : {morph rlift: x y  / x * y}. Proof. exact: rmorphM. Qed.
  Lemma rliftX   n : {morph rlift: x / x ^+ n}.   Proof. exact: rmorphX. Qed.
End RatioLiftTheory.

(* -------------------------------------------------------------------- *)
Section FracOfField.
  Variable K : fieldType.

  Lemma tofracrV (R : idomainType):
    {in GRing.unit, {morph (@tofrac R) : x / x^-1 >-> x^-1}}.
  Proof.
    move=> x unit_x /=; have nz_x: x != 0.
      by apply/eqP=> z_x; rewrite z_x unitr0 in unit_x.
    rewrite !piE -[X in _ = X]pi_inv /invf.
    rewrite !numden_Ratio ?oner_eq0 //; apply/eqmodP => /=.
    by rewrite equivfE !numden_Ratio ?oner_eq0 // mulVr // mulr1.
  Qed.

  Lemma tofracfV: {morph (@tofrac K) : x / x^-1 >-> x^-1}.
  Proof.
    move=> x /=; have [->|nz_x] := altP (x =P 0).
      by rewrite !invr0 tofrac0.
    by rewrite tofracrV // unitfE.
  Qed.
End FracOfField.
