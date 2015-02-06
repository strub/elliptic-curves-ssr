(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype.
Require Import fintype ssralg ssrfun choice xseq bigop ssrint.
Require Import generic_quotient fraction fracfield polyall polydec ec.
Require Import ssrring.

Import GRing.Theory.
Import fraction.FracField.
Import fracfield.FracField.

Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* -------------------------------------------------------------------- *)
Local Notation simp := Monoid.simpm.
Local Notation sizep := (size : {poly _} -> _).

Local Hint Extern 0 (is_true (Xpoly _ != 0)) => exact: XpolyN0.

(* -------------------------------------------------------------------- *)
Reserved Notation "[ 'ecp' a *Y + b ]"
  (at level 0, format "[ 'ecp'  a  *Y  +  b ]").

Reserved Notation "[ 'ecp' a *Y - b ]"
  (at level 0, format "[ 'ecp'  a  *Y  -  b ]").

Reserved Notation "p %:E" (at level 2, format "p %:E").

Reserved Notation "p .[ x , y ]" (at level 2, format "p .[ x ,  y ]").

Reserved Notation "{ 'ecpoly' E }"   (at level 0, format "{ 'ecpoly'  E }").

Section ECPolySub.
  Variable K : ringType.

  Inductive ecpoly (E : ecuType K) : predArgType := ECPoly of {poly K} * {poly K}.

  Coercion pair_val E (p : ecpoly E) := let: ECPoly p := p in p.

  Coercion poly_val E (p : ecpoly E) :=
    let: ECPoly p := p in (p.1 *: 'X + p.2%:P : {poly {poly K}}).

  Canonical ecpoly_subType E := Eval hnf in [newType for (@pair_val E) by (@ecpoly_rect E)].

  Definition ecpoly_eqMixin E := [eqMixin of ecpoly E by <:].
  Canonical  ecpoly_eqType  E := Eval hnf in EqType (ecpoly E) (ecpoly_eqMixin E).

  Variable E : ecuType K.

  Definition ecpoly_of of phant K := ecpoly E.
  Identity Coercion type_ecpoly_of : ecpoly_of >-> ecpoly.
End ECPolySub.

Notation "{ 'ecpoly' E }" := (@ecpoly_of _ E (Phant _)).

(* -------------------------------------------------------------------- *)
Section ECPolySubTheory.
  Variable K : idomainType.
  Variable E : ecuType K.

  Local Notation a := (E#a).
  Local Notation b := (E#b).

  Definition ecpoly_code (p : {ecpoly E}) :=
    let: ECPoly (p1, p2) := p in [:: p1; p2].

  Definition ecpoly_decode (p: seq {poly K}) : option {ecpoly E} :=
    if p is [:: p1; p2] then Some (ECPoly E (p1, p2)) else None.

  Definition ecpoly_codeK : pcancel ecpoly_code ecpoly_decode.
  Proof. by case=> [[]]. Qed.

  Definition ecpoly_choiceMixin := PcanChoiceMixin ecpoly_codeK.
  Canonical  ecpoly_choiceType  := Eval hnf in ChoiceType (ecpoly E) ecpoly_choiceMixin.

  Notation "[ 'ecp' a *Y + b ]" := (ECPoly E (a,  b) : {ecpoly E}).
  Notation "[ 'ecp' a *Y - b ]" := [ecp a *Y + (-b)].

  Definition ecX p := [ecp 0 *Y + p].

  Notation "p %:E" := (ecX p).

  Implicit Types p q r : {ecpoly E}.

  Lemma ecpolyE: forall p, [ecp p.1 *Y + p.2] = p.
  Proof. by case=> [[p1 p2]] /=. Qed.

  Definition zero := [ecp 0 *Y + 0].

  Definition opp  p   := locked [ecp -p.1 *Y - p.2].
  Definition add  p q := locked [ecp (p.1 + q.1) *Y + (p.2 + q.2)].

  Lemma eczeroE : zero = [ecp 0 *Y + 0].
  Proof. by rewrite /zero; unlock. Qed.

  Lemma ecoppE p : opp p = [ecp -p.1 *Y - p.2].
  Proof. by rewrite /opp; unlock. Qed.

  Lemma ecaddE p q : add p q = [ecp (p.1 + q.1) *Y + (p.2 + q.2)].
  Proof. by rewrite /add; unlock. Qed.

  Lemma addC: commutative add.
  Proof.
    case=> [[p1 p2]] [[q1 q2]].
    by rewrite !ecaddE /= [p1 + _]addrC [p2 + _]addrC.
  Qed.

  Lemma addA: associative add.
  Proof.
    case=> [[p1 p2]] [[q1 q2]] [[r1 r2]].
    by rewrite !ecaddE !addrA.
  Qed.

  Lemma add0p: left_id zero add.
  Proof.
    by case=> [[p1 p2]]; rewrite !(ecaddE, eczeroE, add0r).
  Qed.

  Lemma addNp: left_inverse zero opp add.
  Proof.
    by case=> [[p1 p2]]; rewrite !(ecaddE, ecoppE, eczeroE, addNr).
  Qed.

  Definition ecpoly_zmodMixin := ZmodMixin addA addC add0p addNp.
  Canonical  ecpoly_zmodType  := Eval hnf in ZmodType (ecpoly E) ecpoly_zmodMixin.

  Lemma zeroE: 0 = [ecp 0 *Y + 0] :> ecpoly E.
  Proof. by rewrite /GRing.zero /= eczeroE. Qed.

  Lemma oppE: forall p, -p = [ecp -p.1 *Y - p.2].
  Proof. by move=> p; rewrite /GRing.opp /= ecoppE. Qed.

  Lemma addE: forall p q, p + q = [ecp (p.1 + q.1) *Y + (p.2 + q.2)].
  Proof. by move=> p q; rewrite /GRing.add /= ecaddE. Qed.

  Definition dotp p q : {poly K} := p.2 * q.2 + (p.1 * q.1) * (Xpoly E).

  Definition one := [ecp 0 *Y + 1].

  Definition mul p q := locked [ecp (p.1 * q.2 + p.2 * q.1) *Y + (dotp p q)].

  Lemma econeE : one = [ecp 0 *Y + 1].
  Proof. by rewrite /one; unlock. Qed.

  Lemma ecmulE p q :
    mul p q = [ecp (p.1 * q.2 + p.2 * q.1) *Y + (dotp p q)].
  Proof. by rewrite /mul; unlock. Qed.

  Definition mulC: commutative mul.
  Proof.
    case=> [[p1 p2]] [[q1 q2]]; rewrite !ecmulE /dotp /=.
    congr (ECPoly _ (_, _)); rewrite ![q2 * _]mulrC ![p2 * _]mulrC.
    by rewrite addrC. by rewrite [p1 * _]mulrC.
  Qed.

  Lemma mulA: associative mul.
  Proof.
    case=> [[p1 p2]] [[q1 q2]] [[r1 r2]].
    rewrite !ecmulE /dotp /=; congr (ECPoly _ (_, _)).
    * rewrite !mulrDr !mulrDl -!mulrA -!addrA.
      by rewrite [X in _ + X]addrCA [X in _ + (_ + X)]addrC [(Xpoly _) * _]mulrC.
    * rewrite !mulrDr !mulrDl -!mulrA -!addrA.
      by rewrite [X in _ + X]addrCA [X in _ + (_ + X)]addrC [(Xpoly _) * _]mulrC.
  Qed.

  Lemma mul1p: left_id one mul.
  Proof.
    case=> [[p1 p2]]; rewrite !(econeE, ecmulE) /dotp /=.
    by rewrite !mul0r !mul1r addr0 add0r.
  Qed.

  Lemma mul_addl: left_distributive mul +%R.
  Proof.
    case=> [[p1 p2]] [[q1 q2]] [[r1 r2]].
    rewrite !addE /= !ecmulE /dotp /= !mulrDl.
    congr (ECPoly _ (_, _)); by rewrite addrAC !addrA addrAC //.
  Qed.

  Lemma nonzero1p: (one != 0).
  Proof.
    by rewrite econeE /= !eqE /= negb_and oner_neq0 orbT.
  Qed.

  Definition ecq_comRingMixin :=
    ComRingMixin mulA mulC mul1p mul_addl nonzero1p.

  Canonical ecq_Ring    := Eval hnf in RingType (ecpoly E)  ecq_comRingMixin.
  Canonical ecq_comRing := Eval hnf in ComRingType (ecpoly E) mulC.

  Lemma oneE: 1 = [ecp 0 *Y + 1] :> ecpoly E.
  Proof. by rewrite /GRing.one /= econeE. Qed.

  Lemma mulE: forall p q, p * q = [ecp (p.1 * q.2 + p.2 * q.1) *Y + (dotp p q)].
  Proof. by move=> p q; rewrite /GRing.mul /= ecmulE. Qed.

  Lemma mul_eqpolyC:
    forall (p1 q1 p2 q2 : {poly K}) c,
         p1 * q2 + p2 * q1 = 0
      -> p2 * q2 + p1 * q1 * (Xpoly E) = c%:P
      -> (p2 * q2 == c%:P) && (p1 * q1 == 0).
  Proof.
    move=> p1 q1 p2 q2 c.
    have [-> | nz_p1] := eqVneq p1 0; first by rewrite !simp eqxx simp=> _ /eqP.
    have [-> | nz_q1] := eqVneq q1 0; first by rewrite !simp eqxx simp=> _ /eqP.
    have [-> | nz_p2] := eqVneq p2 0.
    + move/eqP; rewrite !simp mulf_eq0 (negbTE nz_p1) /= => _.
      move/(congr1 sizep); rewrite !size_proper_mul;
        try by rewrite ?(mulf_neq0, lead_coef_eq0).
      by rewrite size_Xpoly addnC /= size_polyC; case: (c == 0).
    have [-> | nz_q2] := eqVneq q2 0.
    + move/eqP; rewrite !simp mulf_eq0 (negbTE nz_p2) /= => _.
      move/(congr1 sizep); rewrite !size_proper_mul;
        try by rewrite ?(mulf_neq0, lead_coef_eq0).
      by rewrite size_Xpoly addnC /= size_polyC; case: (c == 0).
    move/eqP; rewrite addr_eq0 => /eqP; move/(congr1 sizep).
    move/eqP; rewrite size_opp !size_proper_mul;
      try by rewrite ?(mulf_neq0, lead_coef_eq0).
    rewrite -eqSS !prednK ?lt0n; first last.
    + by rewrite addn_eq0 !size_poly_eq0 (negbTE nz_p1) (negbTE nz_q2).
    + by rewrite addn_eq0 !size_poly_eq0 (negbTE nz_p2) (negbTE nz_q1).
    move/eqP=> Hsz1 H; have Hsz2: size (p2 * q2) = size (p1 * q1 * Xpoly E).
    + apply size_addr; rewrite H size_polyC.
      rewrite !size_proper_mul ?(mulf_neq0, lead_coef_eq0) //.
      by rewrite size_Xpoly addnC /=; case: (c != 0).
    move: {H} Hsz2; rewrite !size_proper_mul ?(mulf_neq0, lead_coef_eq0) //.
    rewrite size_Xpoly [(_ + 4)%N]addnC /= prednK; last first.
    + by rewrite lt0n addn_eq0 !size_poly_eq0 (negbTE nz_p1) (negbTE nz_q1).
    move/eqP; rewrite -eqSS prednK ?lt0n; last first.
      by rewrite addn_eq0 !size_poly_eq0 (negbTE nz_p2) (negbTE nz_q2).
    rewrite -(eqn_add2r (size p1 + size q2)%N) {2}Hsz1.
    rewrite /= [(_.+3 + _)%N]addnC -!addnA eqn_add2l.
    rewrite addnCA -!addnS [(size q1 + _)%N]addnCA eqn_add2l.
    move/eqP; move/(congr1 odd); rewrite !addnS !addnn.
    by rewrite /= !odd_double.
  Qed.

  Lemma idomainAxiom: forall p q, p * q = 0 -> (p == 0) || (q == 0).
  Proof.
    move=> [[p1 p2]] [[q1 q2]] /eqP; rewrite mulE /= /dotp /=.
    move/eqP; case; rewrite !eqE /= !eqE /= => H1 H2.
    move: (mul_eqpolyC H1 H2); rewrite !mulf_eq0; case/andP.
    case/orP=> Hx2; case/orP=> Hx1; rewrite Hx1 Hx2 !simp //=.
    + by move/eqP: H1; rewrite (eqP Hx1) !simp mulf_eq0.
    + by move/eqP: H1; rewrite (eqP Hx1) !simp mulf_eq0.
  Qed.

  Definition unit : pred _ := fun p => (p.1 == 0) && (p.2 \is a GRing.unit).

  Definition inv p := if unit p then [ecp 0 *Y + p.2^-1] else p.

  Lemma mulVp : {in unit, left_inverse 1 inv *%R}.
  Proof.
    move=> [[p1 p2]]; rewrite /unit {1}/in_mem /=; case/andP.
    move/eqP=> -> Hp2; rewrite /inv /= /unit /= eqxx Hp2 /=.
    by rewrite mulE /= /dotp /= !simp mulVr.
  Qed.

  Lemma intro_unit : forall p q, q * p = 1 -> unit p.
  Proof.
    move=> [[p1 p2]] [[q1 q2]]; rewrite mulE /= /dotp /=; case=> H1 H2.
    move: (mul_eqpolyC H1 H2); case/andP=> H.
    have Hnz0: q2 * p2 != 0 by rewrite (eqP H) oner_neq0.
    move: Hnz0; rewrite mulf_eq0; case/norP=> Hq2N0 Hp2N0 Hpq1.
    apply/andP; split=> //=; last first.
    + by apply/unitrP; exists q2; split; rewrite ?[p2 * q2]mulrC (eqP H).
    move: Hpq1; rewrite mulf_eq0; case/orP=> //.
    move/eqP=> Hq1; move/eqP: H1; rewrite Hq1 !simp mulf_eq0.
    by rewrite (negbTE Hq2N0) /= => Hp1.
  Qed.

  Lemma inv_out : {in predC unit, inv =1 id}.
  Proof. by rewrite /inv => p /negbTE->. Qed.

  Definition ecq_comUnitMixin :=
    ComUnitRingMixin mulVp intro_unit inv_out.

  Canonical ecq_unitRingType :=
    Eval hnf in UnitRingType (ecpoly E) ecq_comUnitMixin.

  Canonical ecq_comUnitRingType :=
    Eval hnf in [comUnitRingType of ecpoly E].

  Canonical ecq_idomainType :=
    Eval hnf in IdomainType (ecpoly E) idomainAxiom.

  (* ---------------------------------------------------------------------- *)
  (* FIXME: L-module ? *)
  Lemma ec_scalel:
    forall (p q r : {poly K}), r%:E * [ecp p *Y + q] = [ecp r * p *Y + r * q].
  Proof.
    by move=> p q r; rewrite mulE /dotp /= !simp.
  Qed.

  Lemma ec_scaler:
    forall (p q r : {poly K}), r%:E * [ecp p *Y + q] = [ecp p * r *Y + q * r].
  Proof.
    by move=> p q r; rewrite ![_ * r]mulrC ec_scalel.
  Qed.

  Lemma ec_eq0 : forall p, (p == 0) = (p.1 == 0) && (p.2 == 0).
  Proof. by case. Qed.

  Lemma ec_neq0 : forall p, (p != 0) = (p.1 != 0) || (p.2 != 0).
  Proof. by move=> p; rewrite ec_eq0 negb_and. Qed.

  Lemma ecX_eq0 : forall (p : {poly K}), (p%:E == 0) = (p == 0).
  Proof. by move=> p; rewrite ec_eq0 /= eqxx. Qed.

  Lemma ecX_neq0: 'X%:E != 0.
  Proof. by rewrite ecX_eq0 polyX_eq0. Qed.

  Lemma ecY_neq0: [ecp 1 *Y + 0] != 0.
  Proof. by rewrite ec_eq0 /= oner_eq0. Qed.

  Lemma ecX_additive: additive ecX.
  Proof. by move=> p q; rewrite /ecX oppE addE /= subrr. Qed.

  Canonical ecX_is_additive := Additive ecX_additive.

  Lemma ecX_multiplicative: multiplicative ecX.
  Proof. by split=> // p q; rewrite /ecX mulE /dotp /= !simp. Qed.

  Canonical ecX_rmorphism := AddRMorphism ecX_multiplicative.

  Lemma ecX0     : 0%:E = 0. Proof. exact: rmorph0. Qed.
  Lemma ecXN     : {morph ecX: x / - x}. Proof. exact: rmorphN. Qed.
  Lemma ecXD     : {morph ecX: x y / x + y}. Proof. exact: rmorphD. Qed.
  Lemma ecXB     : {morph ecX: x y / x - y}. Proof. exact: rmorphB. Qed.
  Lemma ecXMn  n : {morph ecX: x / x *+ n}. Proof. exact: rmorphMn. Qed.
  Lemma ecXMNn n : {morph ecX: x / x *- n}. Proof. exact: rmorphMNn. Qed.
  Lemma ecX1     : 1%:E = 1. Proof. exact: rmorph1. Qed.
  Lemma ecXM     : {morph ecX: x y  / x * y}. Proof. exact: rmorphM. Qed.
  Lemma ecXX   n : {morph ecX: x / x ^+ n}. Proof. exact: rmorphX. Qed.

  Lemma ecX_inj: injective ecX.
  Proof. by move=> p1 p2 []. Qed.

  Canonical ecX_rimorphism := AddInjRMorphism ecX_inj.

  Lemma ecX_natr: forall n, n%:R = n%:R%:E.
  Proof.
    by elim=> [|n IH] //=; rewrite -addn1 !natrD IH ecXD.
  Qed.

  Lemma ecY_sqr:
    forall (p : {poly K}),
      [ecp p *Y + 0]^+2 = (p^+2 * (Xpoly E))%:E.
  Proof.
    by move=> p; rewrite expr2 mulE /dotp /= !simp expr2.
  Qed.

  Lemma ecY_exp_double:
    forall (p : {poly K}) n,
      [ecp p *Y + 0]^+n.*2 = ((p^+n.*2) * (Xpoly E)^+n)%:E.
  Proof.
    move=> p n; rewrite -!mul2n !exprM ecY_sqr.
    by rewrite -ecXX exprMn.
  Qed.

  Lemma ecY_exp_doubleS:
    forall (p : {poly K}) n,
      [ecp p *Y + 0]^+(n.*2.+1) = [ecp ((p^+n.*2.+1) * (Xpoly E)^+n) *Y + 0].
  Proof.
    move=> p n; rewrite !exprS ecY_exp_double mulE.
    by rewrite /dotp /= !simp /=.
  Qed.

  Lemma ecY_ecX_mul:
    forall (p q : {poly K}), [ecp p *Y + 0] * q%:E = [ecp p * q *Y + 0].
  Proof. by move=> p q; rewrite mulE /dotp /= !simp. Qed.

  (* ---------------------------------------------------------------------- *)
  Definition eceval p (x y : K) := p.1.[x] * y + p.2.[x].

  Notation "p .[ x , y ]" := (eceval p x y).

  Lemma ecevalE: forall p x y, p.[x, y] = p.[y%:P].[x].
  Proof.
    case=> [[p1 p2]] x y; rewrite /eceval //=.
    rewrite hornerD hornerC hornerZ hornerX.
    by rewrite hornerD hornerM hornerC.
  Qed.

  Lemma ecX_eceval :
    forall (p : {poly K}) x y, [ecp 0 *Y + p].[x, y] = p.[x].
  Proof.
    by move=> p x y; rewrite /eceval /= horner0 !simp.
  Qed.

  Lemma ecY_eceval :
    forall (p : {poly K}) x y, [ecp p *Y + 0].[x, y] = y * p.[x].
  Proof.
    by move=> p x y; rewrite /eceval /= horner0 !simp mulrC.
  Qed.

  Lemma eceval0 : forall x y, (0 : ecpoly E).[x, y] = 0.
  Proof.
    by move=> x y; rewrite ecevalE /= !simp scale0r !horner0.
  Qed.

  Lemma eceval1 : forall x y, (1 : ecpoly E).[x, y] = 1.
  Proof.
    by move=> x y; rewrite ecevalE /= !hornerE.
  Qed.

  Lemma eceval_neq0:
    forall p x y, p.[x, y] != 0 -> p != 0 :> ecpoly E.
  Proof.
    move=> p x y nz_pxy; apply/negP=> /eqP z_p.
    by rewrite z_p eceval0 eqxx in nz_pxy.
  Qed.

  Lemma eceval_add:
    forall (p q : ecpoly E) x y,
      (p + q).[x, y] = p.[x, y] + q.[x, y].
  Proof.
    move=> [[p1 p2]] [[q1 q2]] x y ; rewrite addE /=.
    rewrite /eceval /= !hornerD mulrDl.
    by rewrite addrAC addrA [q1.[x]*y + q2.[x]]addrC addrA.
  Qed.

  Lemma eceval_opp (p : ecpoly E) x y: (- p).[x, y] = - p.[x, y].
  Proof.
    case: p => [[p1 p2]]; rewrite oppE /= /eceval /=.
    by rewrite !hornerE opprD mulNr.
  Qed.

  Lemma eceval_mul:
    forall (p q : ecpoly E) x y, oncurve E (| x, y |) ->
      (p * q).[x, y] = p.[x, y] * q.[x, y].
  Proof.
    move=> [[p1 p2]] [[q1 q2]] x y cv; rewrite mulE /dotp /=.
    rewrite /eceval /= !(hornerM, hornerE) /= ![_ * y + _]addrC.
    move: cv; rewrite /oncurve -horner_Xpoly => /eqP <-.
    rewrite !(mulrDr, mulrDl) !addrA !mulrA.
    by rewrite ![(_ * y) * _]mulrAC.
  Qed.

  Lemma eceval_prod:
    forall (ps : seq (ecpoly E)) x y, oncurve E (|x, y|) ->
      (\prod_(p <- ps) p).[x, y] = \prod_(p <- ps) (p.[x, y]).
  Proof.
    move=> ps x y oncve; elim: ps => [|p ps IH].
    + by rewrite !big_nil eceval1.
    + by rewrite !big_cons eceval_mul // IH.
  Qed.

  Lemma eceval_exp :
    forall (p : ecpoly E) x y n,  oncurve E (| x, y |) ->
      (p ^+ n).[x, y] = p.[x, y] ^+ n.
  Proof.
    move=> p x y n cve; elim: n => [|n IH].
    + by rewrite !expr0 eceval1.
    by rewrite !exprS eceval_mul // IH.
  Qed.

  Definition ecmap (f : {poly K} -> {poly K}) :=
    fun p => [ecp (f p.1) *Y + (f p.2)].

  Local Notation "p %// r" := (ecmap (divp^~ r) p) (at level 40).

  (* ---------------------------------------------------------------------- *)
  Definition conjp p : {ecpoly E} := [ecp -p.1 *Y + p.2].
  Definition normp p : {poly   K} := dotp p (conjp p).

  Lemma conjp_normp:
    forall p, p * (conjp p) = [ecp 0 *Y + (normp p)].
  Proof.
    case=> [[p1 p2]]; rewrite mulE /normp /dotp /=.
    by rewrite mulrN mulrC subrr !mulrN mulNr addrC.
  Qed.

  Lemma normp_conjp:
    forall p, normp p = (p * (conjp p)).2.
  Proof. by move=> p; rewrite conjp_normp. Qed.

  Lemma conjp_is_additive: additive conjp.
  Proof.
    move=> p q; rewrite /conjp !(addE, oppE) /=.
    by rewrite opprK opprB addrC.
  Qed.

  Canonical conjp_additive := Additive conjp_is_additive.

  Lemma conjp_is_multiplicative: multiplicative conjp.
  Proof.
    split; last by rewrite /conjp oppr0.
    move=> p q; rewrite /conjp !mulE /dotp /=.
    by rewrite mulrNN mulrN opprD mulNr.
  Qed.

  Canonical conjp_rmorphism := AddRMorphism conjp_is_multiplicative.

  Lemma conjp0     : conjp 0 = 0                . Proof. exact: rmorph0. Qed.
  Lemma conjpN     : {morph conjp: x / - x}     . Proof. exact: rmorphN. Qed.
  Lemma conjpD     : {morph conjp: x y / x + y} . Proof. exact: rmorphD. Qed.
  Lemma conjpB     : {morph conjp: x y / x - y} . Proof. exact: rmorphB. Qed.
  Lemma conjpMn  n : {morph conjp: x / x *+ n}  . Proof. exact: rmorphMn. Qed.
  Lemma conjpMNn n : {morph conjp: x / x *- n}  . Proof. exact: rmorphMNn. Qed.
  Lemma conjp1     : conjp 1 = 1                . Proof. exact: rmorph1. Qed.
  Lemma conjpM     : {morph conjp: x y  / x * y}. Proof. exact: rmorphM. Qed.
  Lemma conjpX   n : {morph conjp: x / x ^+ n}  . Proof. exact: rmorphX. Qed.

  Lemma conjp_inj: injective conjp.
  Proof.
    case=> [[p1 p2]] [[q1 q2]] /=; rewrite /conjp /=.
    by case=> /eqP; rewrite eqr_opp=> /eqP -> ->.
  Qed.

  Canonical conjp_rimorphism := AddInjRMorphism conjp_inj.

  Lemma conjp_eq0: forall p, (conjp p == 0) = (p == 0).
  Proof.
    move=> p; apply/eqP/eqP; last by move=> ->; rewrite conjp0.
    by rewrite -{1}[0]conjp0=> /conjp_inj.
  Qed.

  Lemma conjpK: involutive conjp.
  Proof. by move=> p; rewrite /conjp /= opprK ecpolyE. Qed.

  Lemma conjp1E: forall p, (conjp p).1 = -p.1.
  Proof. by case. Qed.

  Lemma conjp2E: forall p, (conjp p).2 = p.2.
  Proof. by case. Qed.

  Definition conjpE := (conjp1E, conjp2E).

  Lemma conjp_ecX:
    forall (p : {poly K}), conjp p%:E = p%:E.
  Proof. by move=> p; rewrite /conjp oppr0. Qed.

  Lemma conjp_ecY:
    forall (p : {poly K}), conjp [ecp p *Y + 0] = -[ecp p *Y + 0].
  Proof. by move=> p; rewrite /conjp oppE oppr0. Qed.

  Lemma eceval_conjp (p : ecpoly E) x y: (conjp p).[x, -y] = p.[x, y].
  Proof.
    case: p=> [[p1 p2]]; rewrite /conjp /= /eceval /=.
    by rewrite hornerN mulrNN.
  Qed.

  Lemma dotpC: forall p q, dotp p q = dotp q p.
  Proof.
    by move=> p q; rewrite /dotp /= [p.1 * _]mulrC [p.2 * _]mulrC.
  Qed.

  Lemma dotp_addl: forall r, {morph (dotp^~ r) : p q / p + q}.
  Proof.
    move=> r p q; rewrite addE /dotp /= !mulrDl.
    by rewrite addrAC !addrA addrAC.
  Qed.

  Lemma dotp_addr: forall r, {morph (dotp r) : p q / p + q}.
  Proof.
    by move=> r ??; rewrite dotpC dotp_addl ![dotp _ r]dotpC.
  Qed.

  Lemma dotp_conjp: forall p q, dotp (conjp p) (conjp q) = (dotp p q).
  Proof.
    by move=> p q; rewrite /dotp !conjpE mulNr mulrN opprK.
  Qed.

  Lemma norm0: normp 0 = 0.
  Proof.
    by rewrite /normp /dotp /= !mul0r add0r.
  Qed.

  Lemma norm1 : normp 1 = 1.
  Proof. by rewrite /normp /dotp /= !simp. Qed.


  Lemma normpE: forall p, normp p = (p.2)^+2 - (p.1)^+2 * (Xpoly E).
  Proof.
    by case=> [[p1 p2]] /=; rewrite /normp /dotp /= mulrN mulNr.
  Qed.

  Lemma normp_conjp_eq: forall p, normp (conjp p) = normp p.
  Proof.
    by move=> p; rewrite /normp conjpK dotpC.
  Qed.

  Lemma normpM: {morph normp : p q / p * q}.
  Proof.
    move=> p q; rewrite normp_conjp conjpM mulrCA.
    rewrite -mulrA conjp_normp mulrA [_ * p]mulrC conjp_normp.
    by rewrite mulE /= /dotp /= !mul0r addr0.
  Qed.

  Lemma normpX: forall p k, normp (p^+k) =  (normp p)^+k.
  Proof.
    move=> p; elim=> [|k IH].
    + by rewrite !expr0 norm1.
    + by rewrite !exprS normpM IH.
  Qed.

  Lemma norm_eq0:
    forall p, (normp p == 0) = (p == 0).
  Proof.
    move=> p; apply: (sameP idP); apply: (iffP idP).
    + by move/eqP=> ->; rewrite norm0.
    case: p => [[p q]]; rewrite /normp /dotp /= => /eqP.
    have [-> | nz_p] := eqVneq p 0; rewrite ?simp.
    + by move/eqP; rewrite mulf_eq0; case/orP=> /eqP ->.
    move/eqP; rewrite mulrN mulNr subr_eq0.
    have [-> | nz_q] := eqVneq q 0; rewrite ?simp.
    + by rewrite eq_sym !mulf_eq0 (negbTE nz_p) // ?(negbTE (XpolyN0 _)).
    move/eqP=> /(congr1 sizep).
    rewrite [size (_ * Xpoly _)]size_proper_mul; last first.
    + by rewrite mulf_neq0 // lead_coef_eq0 // mulf_neq0.
    rewrite size_Xpoly addnC /=; move/(congr1 odd).
    by rewrite -!expr2 /= !odd_size_id_exp.
  Qed.

  Lemma normp_ecX (p : {poly K}): normp p%:E = p ^+ 2.
  Proof.
    by rewrite normp_conjp conjp_ecX -ecXM.
  Qed.

  (* ---------------------------------------------------------------------- *)
  Definition degree p := size (normp p).

  Lemma degree0: degree 0 = 0%N.
  Proof. by rewrite /degree norm0 size_poly0. Qed.

  Lemma degree_eq0: forall p, (degree p == 0%N) = (p == 0).
  Proof.
    by move=> p; rewrite /degree size_poly_eq0 norm_eq0.
  Qed.

  Lemma degree_pX:
    forall (p : {poly K}), degree (p%:E) = (2 * (size p)).-1.
  Proof.
    move=> p; have [->|nz_p] := eqVneq p 0.
    + by rewrite degree0 size_poly0 muln0.
    rewrite /degree normpE /= !expr2 !simp subr0.
    rewrite size_proper_mul ?(mul2n, addnn) //.
    + by rewrite mulf_neq0 // lead_coef_eq0.
  Qed.

  Lemma degree_pY:
    forall (p : {poly K}),
      p != 0 -> degree [ecp p *Y + 0] = (2 * (size p).+1)%N.
  Proof.
    move=> p nz_p; rewrite /degree normpE /= expr2 !simp size_opp.
    rewrite size_proper_mul ?(mulf_neq0, lead_coef_eq0) // size_Xpoly.
    rewrite addnC /= expr2 size_proper_mul ?addnn //; last first.
    + by rewrite mulf_neq0 // lead_coef_eq0.
    rewrite prednK ?(double_gt0, lt0n, size_poly_eq0) //.
    by rewrite mul2n doubleS.
  Qed.

  Lemma degreeC (c : K): c != 0 -> degree ((c%:P)%:E) = 1%N.
  Proof.
    by move=> cnz; rewrite degree_pX size_polyC cnz.
  Qed.

  Lemma degree_exp:
    forall p k, p != 0 -> degree (p ^+ k) = ((degree p).-1 * k).+1.
  Proof.
    move=> p k nz_p; rewrite /degree normpX size_id_exp ?norm_eq0 //.
    by rewrite -subn1 mulnBl mul1n [(k * _)%N]mulnC.
  Qed.

  Lemma degree_mul_id:
    forall p q, p * q != 0 -> degree (p * q) = (degree p + degree q).-1.
  Proof.
    move=> p q; rewrite mulf_eq0 => /norP [nz_p nz_q].
    rewrite /degree normpM size_proper_mul //.
    by rewrite mulf_neq0 // lead_coef_eq0 norm_eq0.
  Qed.

  Lemma degreeX : degree 'X%:E = 3.
  Proof. by rewrite degree_pX size_polyX. Qed.

  Lemma degreeY : degree [ecp 1 *Y + 0] = 4.
  Proof. by rewrite degree_pY ?(size_polyC, oner_neq0). Qed.

  Lemma degree_expX : forall k, degree (('X%:E)^+k) = (2 * k).+1.
  Proof.
    move=> k; rewrite degree_exp ?degreeX //.
    by rewrite ecX_eq0 -size_poly_eq0 size_polyX.
  Qed.

  Lemma degree_expY : forall k, degree ([ecp 1 *Y + 0]^+k) = (3 * k).+1.
  Proof.
    move=> k; rewrite degree_exp ?degreeY //.
    by rewrite ec_neq0 /= oner_neq0.
  Qed.

  Lemma degree_conjp : forall p, degree (conjp p) = degree p .
  Proof.
    by move=> p; rewrite /degree normp_conjp_eq.
  Qed.

  Lemma degree_opp : forall p, degree (-p) = degree p.
  Proof.
    by move=> p; rewrite /degree normpE oppE !sqrrN -normpE.
  Qed.

  Lemma degree_normp:
    forall p, degree (normp p)%:E = (2 * (degree p)).-1%N.
  Proof. by move=> p; rewrite degree_pX. Qed.

  Lemma degreeE (p : ecpoly E) :
    degree p = (maxn (2 * size p.2).-1 ((2 * (size p.1).+1) * (p.1 != 0))).
  Proof.
    case: p => [[p1 p2]] /=; have [->|nz_p1] := eqVneq p1 0.
      by rewrite eqxx muln0 maxn0 degree_pX.
    rewrite nz_p1 muln1; have [->|nz_p2] := eqVneq p2 0.
      by rewrite degree_pY // size_poly0 muln0 max0n.
    rewrite /degree /normp /dotp /= size_add_max; last first.
      rewrite mulrN mulNr size_opp !size_mul ?mulf_neq0 ?XpolyN0 //.
      rewrite !addnn size_Xpoly addn4 /= prednK; last first.
        by rewrite lt0n double_eq0 size_poly_eq0.
      apply/negP=> /eqP /(congr1 S); rewrite prednK; last first.
        by rewrite lt0n double_eq0 size_poly_eq0.
      by move/(congr1 odd); rewrite /= !odd_double.
    rewrite mulrN mulNr size_opp !size_mul ?mulf_neq0 ?XpolyN0 //.
    rewrite !addnn -!mul2n size_Xpoly addn4 /= prednK; last first.
      by rewrite lt0n muln_eq0 /= size_poly_eq0.
    by rewrite -[(size p1).+1]addn1 mulnDr muln1 addn2.
  Qed.

  Lemma degree_add_max (p q : ecpoly E):
    degree p != degree q -> degree (p + q) = maxn (degree p) (degree q).
  Proof.
    have maxn_neqR_le n m1 m2:
      maxn n m1 != maxn n m2 -> (n < maxn m1 m2).
    + rewrite leq_max /maxn;
        case: (ltnP n m1); case: (ltnP n m2) => //;
        by rewrite eqxx.
    wlog: p q / (size q.1 <= size p.1).
      move=> wlog ne_deg_pq; case: (leqP (size q.1) (size p.1)).
        by move=> le_sz_qp; apply: wlog.
      move=> lt_sz_pq; rewrite addrC maxnC; apply: wlog => //.
        by apply: ltnW. by rewrite eq_sym.
    move=> leq_piq; rewrite !degreeE !addE /=.
    have [z_p1|nz_p1] := eqVneq p.1 0.
      have z_q1: q.1 = 0.
        apply/eqP; rewrite -size_poly_eq0 -leqn0 (leq_trans leq_piq) //.
        by rewrite leqn0 z_p1 size_poly0.
      rewrite z_q1 z_p1 // addr0 eqxx !muln0 !maxn0.
      rewrite maxn_pred !mul2n -map_maxn; last exact: leq_double.
      have predn_neq n m: n.-1 != m.-1 -> n != m.
        by case: n m => [|n] [|m].
      move/predn_neq; rewrite (inj_eq double_inj)=> ne_sz_pq2.
      by rewrite -size_add_max.
    have [z_q1|nz_q1] := eqVneq q.1 0.
      rewrite z_q1 addr0 nz_p1 !eqxx !(muln1, muln0) !maxn0.
      rewrite maxnAC maxn_pred !mul2n -map_maxn; last exact: leq_double.
      case: (size p.2 =P size q.2); last first.
        by move=> /eqP ne_sz_pq2 _; rewrite -size_add_max.
      move=> eq_sz_pq2; rewrite eq_sz_pq2 maxnn {1}/maxn.
      case: ltnP; last (by rewrite eqxx); rewrite {2}/maxn=> lt.
      move=> ne; rewrite lt; apply/maxn_idPr; rewrite (leq_trans _ lt) //.
      have ltn_pred n m: n <= m -> n.-1 <= m.-1.
        by case: n m => [|n] [|m].
      apply: ltnW; rewrite ltnS ltn_pred // leq_double.
      by rewrite (leq_trans (size_add _ _)) // eq_sz_pq2 maxnn.
    rewrite nz_p1 nz_q1 !muln1; move: leq_piq; rewrite leq_eqVlt; case/orP.
      move/eqP=> eq_sz_pq1; rewrite eq_sz_pq1 2![maxn _.-1 _]maxnC.
      rewrite !mul2n => ne; have/eqP/(_ (congr1 _ _)) := ne => /eqP.
      have predn_neq n m: n.-1 != m.-1 -> n != m.
        by case: n m => [|n] [|m].
      move/predn_neq; rewrite (inj_eq double_inj) => ne_sz_pq2.
      rewrite maxnACA maxnn maxnC maxn_pred -map_maxn; last first.
        by exact: leq_double.
      rewrite -size_add_max //; have/maxn_neqR_le := ne.
      rewrite maxn_pred -(map_maxn _); last exact: leq_double.
      rewrite -size_add_max // {2}/maxn => le; rewrite le.
      apply/maxn_idPr; apply: (leq_trans _ (ltnW le)).
      case: (_ != 0); last by rewrite muln0 leq0n.
      rewrite muln1 leq_double ltnS -[X in _ <= X]maxnn.
      by rewrite -{2}eq_sz_pq1; apply: size_add.
    move=>lt_sz_qp1; have nz_pDq1: p.1 + q.1 != 0.
      rewrite -size_poly_eq0 size_add_max; last first.
        by move: lt_sz_qp1; rewrite ltn_neqAle eq_sym; case/andP.
      by rewrite maxnC /maxn lt_sz_qp1 size_poly_eq0.
    rewrite nz_pDq1 muln1 => ne; apply/esym; rewrite maxnACA maxnC.
    rewrite !mul2n -map_maxn; last exact: leq_double.
    rewrite maxnSS -size_add_max; last first.
      by move: lt_sz_qp1; rewrite ltn_neqAle eq_sym; case/andP.
    rewrite maxnC; case: (eqVneq (size p.2) (size q.2)); last first.
      move=> ne_sz_pq2; rewrite maxn_pred -map_maxn; last first.
        exact: leq_double.
      by rewrite -size_add_max.
    move=> eq_sz_pq2; move: ne; rewrite eq_sz_pq2 maxnn.
    rewrite !mul2n => /maxn_neqR_le; rewrite -map_maxn; last first.
      exact: leq_double.
    rewrite maxnSS -size_add_max; last first.
      by move: lt_sz_qp1; rewrite ltn_neqAle eq_sym; case/andP.
    move=> lt; rewrite {1}/maxn lt; apply/esym/maxn_idPr.
    apply: (leq_trans _ (ltnW lt)); rewrite -!subn1 leq_sub2r //.
    rewrite leq_double -[X in _ <= X]maxnn -{2}eq_sz_pq2.
    by rewrite maxnC size_add.
  Qed.

  Lemma degree_add (p q : {ecpoly E}):
    degree (p + q) <= maxn (degree p) (degree q).
  Proof.
    have leq_predn n m: n <= m -> n.-1 <= m.-1.
      by case: n m => [|n] [|m].
    wlog: p q / (size q.1 <= size p.1).
      move=> wlog; case: (leqP (size q.1) (size p.1)).
        by move=> le_sz_qp; apply: wlog.
      move=> lt_sz_pq; rewrite addrC maxnC; apply: wlog => //.
        by apply: ltnW.
    move=> leq_piq; rewrite !degreeE !addE /=.
    have [z_p1|nz_p1] := eqVneq p.1 0.
      have z_q1: q.1 = 0.
        apply/eqP; rewrite -size_poly_eq0 -leqn0 (leq_trans leq_piq) //.
        by rewrite leqn0 z_p1 size_poly0.
      rewrite z_q1 z_p1 // addr0 eqxx !muln0 !maxn0.
      rewrite maxn_pred !mul2n -map_maxn; last exact: leq_double.
      by apply: leq_predn; rewrite leq_double size_add.
    have [z_q1|nz_q1] := eqVneq q.1 0.
      rewrite z_q1 addr0 nz_p1 !eqxx !(muln1, muln0) !maxn0.
      rewrite maxnAC maxn_pred !mul2n -map_maxn; last exact: leq_double.
      rewrite geq_max [X in _&&X]leq_max leqnn orbT andbT.
      rewrite leq_max; apply/orP; left; apply/leq_predn.
      by rewrite leq_double size_add.
    rewrite nz_p1 nz_q1 !muln1; set n := maxn _ _.
    have: n <= maxn (2 * size (p.2 + q.2)).-1 (2 * (size (p.1 + q.1)).+1).
      rewrite {}/n; case: (_ =P 0); rewrite !(muln0, muln1) //.
      by rewrite maxn0 leq_maxl.
    move=> le; apply/(leq_trans le); rewrite !mul2n.
    rewrite maxnA [X in _<= maxn X _]maxnAC -[X in _<= X]maxnA.
    rewrite geq_max; apply/andP; split; rewrite leq_max;
      apply/orP; [left | right]; rewrite ?maxn_pred.
    + apply/leq_predn; rewrite -map_maxn; last exact: leq_double.
      by rewrite leq_double size_add.
    + rewrite -map_maxn; last exact: leq_double; rewrite leq_double.
      by rewrite maxnSS ltnS size_add.
  Qed.

  Lemma degree_addl (p q : ecpoly E):
    degree q < degree p -> degree (p + q) = degree p.
  Proof.
    move=> lt; rewrite degree_add_max; last first.
      by move: lt; rewrite ltn_neqAle eq_sym; case/andP.
    by rewrite maxnC /maxn lt.
  Qed.

  Lemma odd_degree_lt (p : ecpoly E): p.1 != 0 -> p.2 != 0 ->
    odd (degree p) = ~~ (size p.2 <= (size p.1).+1)%N.
  Proof.
    move=> nz_p1 nz_p2; rewrite degreeE nz_p1 muln1.
    have <-: forall n, ~~ odd n.+1 = odd n by move=> ?; rewrite negbK.
    rewrite -maxnSS prednK ?muln_gt0 /= ?lt0n ?size_poly_eq0 //.
    rewrite maxnC /maxn ltnNge; case: leqP.
    + rewrite !mul2n /= odd_double /= leq_eqVlt; case/orP.
        by move/eqP/(congr1 odd); rewrite /= !odd_double.
      by rewrite ltnS leq_double => ->.
    + rewrite !mul2n odd_double -doubleS leq_double /=.
      by rewrite ltnNge => ->.
  Qed.

  Lemma degree_odd_nzpX (p : ecpoly E): odd (degree p) -> p.2 != 0.
  Proof.
    rewrite degreeE /maxn; case: ltnP => _.
    + rewrite mul2n; case: eqP; first by rewrite muln0.
      by rewrite muln1 doubleS /= odd_double.
    + rewrite -size_poly_eq0; case: (size p.2) => [//|n].
      by rewrite mul2n doubleS /= odd_double.
  Qed.

  Lemma degree_even_nzpY (p : ecpoly E):
    p != 0 -> ~~ odd (degree p) -> p.1 != 0.
  Proof.
    case: p => [[p1 p2]]; do 2! rewrite eqE /=.
    case/nandP => // nz_p2; rewrite degreeE /=.
    case: eqP => [->|//]; rewrite size_poly0 !Monoid.simpm.
    move: nz_p2; rewrite -size_poly_eq0; case: (size p2) => [//|n] _.
    by rewrite mul2n doubleS /= odd_double.
  Qed.

  Lemma odd_degreeE (n : ecpoly E):
    odd (degree n) -> degree n = (2 * (size n.2)).-1.
  Proof.
    rewrite degreeE /maxn; case: ltnP => //=.
    by move=> _; rewrite -mulnA mul2n odd_double.
  Qed.

  Lemma even_degreeE (n : ecpoly E):
    ~~ (odd (degree n)) -> degree n = (2 * (size n.1).+1 * (n.1 != 0%R))%N.
  Proof.
    rewrite degreeE; have [->|nz_n2] := eqVneq n.2 0.
      by move=> _; rewrite size_poly0 max0n.
    rewrite /maxn; case: ltnP => //=.
    move=> _; case sz: (size n.2) => [|k].
    + by move/eqP: sz; rewrite size_poly_eq0 (negbTE nz_n2).
    + by rewrite mul2n /= odd_double.
  Qed.

  (* ------------------------------------------------------------------ *)
  Definition fdegree_r (f : {ratio {ecpoly E}}) :=
    if \n_f == 0 then 0 else (degree \n_f)%:Z - (degree \d_f)%:Z.

  Definition fdegree :=
    lift_fun1 {fraction {ecpoly E}} fdegree_r.

  Lemma pi_fdegree:
    {mono \pi_{fraction {ecpoly E}} : f / fdegree_r f >-> fdegree f}.
  Proof.
    move=> f2; unlock fdegree; set f1 := (repr _).
    have: (f1 = f2 %[mod {fraction _}]) by rewrite reprK.
    case: f2 f1 => [[n2 d2] /= nz_d2] [[n1 d1] /= nz_d1] /=.
    move/eqmodP => /=; rewrite FracField.equivfE /= => eqE.
    have/eqP/(congr1 (fun x => x == 0)) := eqE.
      rewrite !mulf_eq0 (negbTE nz_d1) (negbTE nz_d2) !(orbF, orFb) => nz.
    rewrite /fdegree_r /= -nz; case: (n1 =P 0) => [//|/eqP nz_n1].
    have := nz_n1; rewrite nz => {nz} nz_n2.
    move/eqP/(congr1 degree): eqE; rewrite !degree_mul_id ?mulf_neq0 // => /eqP.
    rewrite -eqSS !prednK ?lt0n ?addn_eq0 1?negb_and; first last.
      by rewrite !degree_eq0 nz_n1. by rewrite !degree_eq0 nz_d1.
    by rewrite -eqz_nat !PoszD [X in _==X]addrC -addr_cross => /eqP ->.
  Qed.

  Canonical pi_fdegree_morph := PiMono1 pi_fdegree.

  Lemma fdegreeF (f : {ecpoly E}): fdegree f%:F = (degree f).-1.
  Proof.
    rewrite !piE /fdegree_r !numden_Ratio ?oner_neq0 //.
    have [->|nz_f] := eqVneq f 0; first by rewrite eqxx degree0.
    rewrite (negbTE nz_f) degreeC ?oner_eq0 // predn_int //.
    by rewrite lt0n degree_eq0.
  Qed.

  Lemma fdegreeE (n d : {ecpoly E}): n * d != 0 ->
    fdegree (n // d) = (degree n)%:Z - (degree d)%:Z.
  Proof.
    rewrite mulf_eq0 => /norP [nz_n nz_d].
    rewrite !piE /fdegree_r !numden_Ratio //.
    by rewrite (negbTE nz_n).
  Qed.

  Lemma fdegreeM (f g : {fraction {ecpoly E}}): f * g != 0 ->
    fdegree (f * g) = (fdegree f) + (fdegree g).
  Proof.
    elim/fracW: f => [nf df nz_df]; elim/fracW: g => [ng dg nz_dg].
    rewrite !mulf_eq0 !invr_eq0 !tofrac_eq0 !negb_or -!andbA.
    case/and4P => nz_nf _ nz_ng _; rewrite mulf_div -!tofracM.
    rewrite !fdegreeE ?degree_mul_id ?mulf_neq0 //.
    rewrite !predn_int ?(lt0n, addn_eq0) ?degree_eq0;
      try by rewrite negb_and; apply/orP; left.
    by rewrite !PoszD addrAC !opprD -!addrA opprK subrr; ssring.
  Qed.

  Lemma fdegreeC (c : K): fdegree ((c%:P)%:E)%:F = 0.
  Proof.
    rewrite fdegreeF; have [->|nz_c] := eqVneq c 0.
      by rewrite degree0. by rewrite degreeC.
  Qed.

  Lemma fdegreeXn (f : {fraction {ecpoly E}}) n:
    fdegree (f ^+ n) = (fdegree f) *+ n.
  Proof.
    have [->|nz_f] := eqVneq f 0.
      rewrite expr0n fdegreeC mul0rn;
        by case: (_ == _); rewrite fdegreeC.
    elim: n => [|n IH]; first by rewrite expr0 fdegreeC mulr0n.
    by rewrite exprS fdegreeM ?(mulf_neq0, expf_neq0) // IH mulrS.
  Qed.

  Lemma fdegreeV (f : {fraction {ecpoly E}}): fdegree f^-1 = -(fdegree f).
  Proof.
    have [->|nz_f] := eqVneq f 0; first by rewrite invr0 fdegreeC oppr0.
    elim/fracW: f nz_f => n d nz_d; rewrite mulf_eq0 tofrac_eq0.
    by case/norP=> nz_n _; rewrite invfE !fdegreeE ?mulf_neq0 // opprB.
  Qed.
End ECPolySubTheory.

(* -------------------------------------------------------------------- *)
Notation "[ 'ecp' a *Y + b ]" := (ECPoly _ (a, b)).
Notation "[ 'ecp' a *Y - b ]" := (ECPoly _ (a, -b)).
Notation "p %:E" := (ECPoly _ (0, p)).

(* -------------------------------------------------------------------- *)
Section ECPolyMorph.
  Variable K : ecuFieldType.
  Variable E : ecuType K.

  Variable L : fieldType.
  Variable f : {rmorphism K -> L}.

  Lemma chi2: 2%:R != 0 :> L.
  Proof.
    rewrite -[0](rmorph0 f) eq_sym rmorph_eq_nat 1?eq_sym.
      by rewrite ecu_chi2. by apply: fmorph_inj.
  Qed.

  Lemma chi3: 3%:R != 0 :> L.
  Proof.
    rewrite -[0](rmorph0 f) eq_sym rmorph_eq_nat 1?eq_sym.
      by rewrite ecu_chi3. by apply: fmorph_inj.
  Qed.

  Definition ecmorph_ECUFieldMixin := ECUFieldMixin chi2 chi3.
  Canonical ecmorph_ECUFieldType := Eval hnf in (ECUFieldType _ ecmorph_ECUFieldMixin).

  Local Notation pA := (f (E #a)).
  Local Notation pB := (f (E #b)).

  Lemma discr_neq0: 4%:R * pA ^+ 3 + 27%:R * pB ^+ 2 != 0 :> L.
  Proof.
    move: (ecu_DN0 E); rewrite -(inj_eq (fmorph_inj (F := K) f)).
    pose R := (rmorphMn, rmorphX, rmorphM, rmorphD).
    by rewrite !(rmorph0, rmorph1, R).
  Qed.

  Definition ec_of_ecmorph := Build_ecuType discr_neq0.
End ECPolyMorph.

(* -------------------------------------------------------------------- *)
Section ECPolyChi.
  Variable K : ecuFieldType.
  Variable E : ecuType K.

  Import GRing FracField.

  (* ------------------------------------------------------------------ *)
  Definition embed := (@tofrac _ \o ((ecX E) \o polyC)).

  Definition embed_rmorphism :=
    comp_rmorphism
      (comp_rmorphism (tofrac_rmorphism _) (ecX_rmorphism E))
      (polyC_rmorphism _).

  Canonical ecfrac_ECUFieldType := (ecmorph_ECUFieldType embed_rmorphism).
End ECPolyChi.
