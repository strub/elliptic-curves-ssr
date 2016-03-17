(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq.
From mathcomp Require Import fintype choice ssrfun bigop poly ssralg.
From mathcomp Require Import ssrint finalg fingroup mxpoly countalg.

Require Import SsrMultinomials.freeg.
Require Import ec ecpoly eceval ecorder ecdiv ecrr ecdivlr.

(* -------------------------------------------------------------------- *)
Import GRing.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Section ECGroup.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Hypothesis closedK : GRing.ClosedField.axiom K.

  Import PreClosedField.

  Hint Resolve closedK.

  Local Notation "\- x"   := (@ECGroup.neg _ x).
  Local Notation "x \+ y" := (@ECGroup.add _ E x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Lemma addeA: associative (@ECGroup.addec K E).
  Proof.
    move=> [p oncve_p] [q oncve_q] [r oncve_r] /=.
    apply/eqP; rewrite !eqE /=; apply/eqP.
    rewrite -[p](lrpi _ oncve_p) // -[q](lrpi _ oncve_q) // -[r](lrpi _ oncve_r) //.
    have oncveD (D1 D2 : {freeg (point K)}):
      all oncurve (dom D1) -> all oncurve (dom D2) -> all oncurve (dom (D1 + D2)).
      move=> oncveD1 oncveD2; apply/allP=> s /domD_subset.
      rewrite mem_cat => /orP [];
        by [move/allP/(_ s): oncveD1 | move/allP/(_ s): oncveD2].
    rewrite -!lrD ?(degD, degN, degU, subrr) //;
      try by solve [ by apply: oncurve_lrpi
                   | by apply: oncveD; apply: oncurve_lrpi].
    by rewrite addrA.
  Qed.

  Definition ec_zmodMixin := 
    (ZmodMixin
       addeA (ECGroup.addeC (E := E))
       (ECGroup.add0e (E := E)) (ECGroup.addNe (E := E))).

  Definition ec_zmodType := ZmodType (ec E) ec_zmodMixin.
End ECGroup.

(* -------------------------------------------------------------------- *)
Section ECLift.
  Variable K   : ecuFieldType.
  Variable L   : fieldType.
  Variable E   : ecuType K.
  Variable f   : {rmorphism K -> L}.

  Local Notation "\- x"   := (@ECGroup.negec _ x).
  Local Notation "x \+ y" := (@ECGroup.addec _ _ x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Local Notation rmorphE :=
    (rmorph0, rmorph1, rmorphMn,rmorphX,
     fmorphV, rmorphM, rmorphB, rmorphD, rmorphN).

  Lemma eclift_inj: injective f.
  Proof. by apply/fmorph_inj. Qed.

  Lemma eclift_chi2: 2%:R != 0 :> L.
  Proof. by move: (ecu_chi2 K); rewrite -(inj_eq eclift_inj) !rmorphE. Qed.

  Lemma eclift_chi3: 3%:R != 0 :> L.
  Proof. by move: (ecu_chi3 K); rewrite -(inj_eq eclift_inj) !rmorphE. Qed.

  Lemma eclift_DN0: 4%:R * (f (E#a))^+3 + 27%:R * (f (E#b))^+2 != 0.
  Proof. by case: E=> a b /=; rewrite -(inj_eq eclift_inj) !rmorphE. Qed.

 (* curve parameters in the extension L *)
  Definition eclift : ecuType L := locked (Build_ecuType eclift_DN0).

  Lemma ecliftA: eclift#a = f (E#a).
  Proof. by rewrite /eclift; unlock. Qed.

  Lemma ecliftB: eclift#b = f (E#b).
  Proof. by rewrite /eclift; unlock. Qed.

  Definition eclift_point (p : point K) : point L :=
    if p is (|x, y|) then (|f x, f y|) else ∞.

  Lemma eclift_point_inj: injective eclift_point.
  Proof.
    case=> [|x1 y1]; case=> [|x2 y2] //= [].
    by move=> /eclift_inj -> /eclift_inj ->.
  Qed.

  Lemma eclift_oncurve (p : point K):
    oncurve E p = oncurve eclift (eclift_point p).
  Proof.
    case: p=> [|x y] //=; rewrite -(inj_eq eclift_inj).
    by rewrite !rmorphE -ecliftA -ecliftB.
  Qed.

  Lemma oncurve_eclift (p : point K):
    oncurve E p -> oncurve eclift (eclift_point p).
  Proof. by rewrite eclift_oncurve. Qed.

  (* takes a point of E(K) and uses oncurve_eclift to construct the
     proof that is also on E(L) and finally returns a point of E(L) *)
  Definition eclift_ec (p : ec E): ec eclift := locked (
    let: EC _ oncve := p in EC (oncurve_eclift oncve)).

  Lemma eclift_ecE (p : ec E): eclift_ec p = eclift_point p :> point L.
  Proof. by rewrite /eclift_ec; unlock; case: p. Qed.

  Lemma eclift_ec_inj: injective eclift_ec.
  Proof.
    move=> p1 p2 /eqP; rewrite eqE /= !eclift_ecE.
    move/eqP=> /eclift_point_inj eq; apply/eqP.
    by rewrite eqE /= eq.
  Qed.

  Lemma eclift_oncurve_ec (p : ec E):
    oncurve E p = oncurve eclift (eclift_ec p).
  Proof. by case: p=> p oncve /=; rewrite eclift_ecE /= eclift_oncurve. Qed.

  Definition ECULiftFieldMixin := ECUFieldMixin (eclift_chi2) (eclift_chi3).
  Definition ECULiftFieldType  := ECUFieldType L ECULiftFieldMixin.

  Local Notation LC := ECULiftFieldType.

  Lemma eclift_ec_add:
    {morph eclift_ec : p1 p2 / p1 \+ p2 >-> @ECGroup.addec LC eclift p1 p2}.
  Proof.
    move=> p1 p2 /=; apply/eqP; rewrite eqE /=.
    rewrite !eclift_ecE /= /ECGroup.add /=.
    rewrite -!eclift_oncurve !oncurve_ec.
    case: p1 p2=> [[|x1 y1]] oncve1 [[|x2 y2]] oncve2 //=.
    rewrite -[X in f y1 != X](rmorph0 f) !(inj_eq eclift_inj).
    case: (x1 == x2)=> /=; first case: (_ && _); move=> //=.
    + by rewrite !rmorphE -?(ecliftA, ecliftB) eqxx.
    + by rewrite !rmorphE -?(ecliftA, ecliftB) eqxx.
  Qed.
End ECLift.

(* -------------------------------------------------------------------- *)
Section ECGroupOfFin.
  Variable K : finECUFieldType.
  Variable E : ecuType K.

  Local Notation "\- x"   := (@ECGroup.negec _ x).
  Local Notation "x \+ y" := (@ECGroup.addec _ _ x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Lemma addeA_fin: associative (@ECGroup.addec K E).
  Proof.
    case (countable_algebraic_closure [countFieldType of K]) => L /= [i ir].
    have closedL: GRing.ClosedField.axiom L by apply/solve_monicpoly.
    pose LFT := ECULiftFieldType i.
    pose LDM := closed_field.closed_fields_QEMixin closedL.
    pose LDT := EcuDecFieldType LFT LDM.
    have h := (@addeA LDT (eclift E i) closedL) => p1 p2 p3.
    pose q1 := eclift_ec i p1; pose q2 := eclift_ec i p2; pose q3 := eclift_ec i p3.
    have {h}/eqP := (h q1 q2 q3); rewrite -!eclift_ec_add.
    by rewrite (inj_eq (eclift_ec_inj (f := i))) => /eqP ->.
  Qed.

  Definition finec_zmodMixin := 
    (ZmodMixin
       addeA_fin (ECGroup.addeC (E := E))
       (ECGroup.add0e (E := E)) (ECGroup.addNe (E := E))).

  Canonical finec_zmodType := Eval hnf in (ZmodType (@ec K E) finec_zmodMixin).
End ECGroupOfFin.

(* -------------------------------------------------------------------- *)
Section ECFinZModType.
  Variable K : finECUFieldType.
  Variable E : ecuType K.

  Canonical ec_finZmodType := Eval hnf in [finZmodType of ec E].
End ECFinZModType.

(* -------------------------------------------------------------------- *)
Section ECFinGroup.
  Variable K : finECUFieldType.
  Variable E : ecuType K.

  Canonical ec_baseFinGroupType := [baseFinGroupType of (ec E) for +%R].
  Canonical ec_finGroupType := [finGroupType of (ec E) for +%R].
End ECFinGroup.
