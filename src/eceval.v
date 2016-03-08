(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp
Require Import ssreflect ssrnat ssrbool eqtype generic_quotient.
From mathcomp
Require Import fintype choice bigop ssralg ssrfun ssrint ssrnum.
Require Import fraction fracfield xseq ssrring.
Require Import polyall polyfrac polydec ec ecpoly ecorder.

Import GRing.Theory.
Import Num.Theory.
Import fraction.FracField.
Import fracfield.FracField.
Import FracInterp.

Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation simpm := Monoid.simpm.

Local Notation "\- x"   := (FracInterp.opp x).
Local Notation "x \+ y" := (FracInterp.add x y).
Local Notation "x \* y" := (FracInterp.mul x y) (at level 30).
Local Notation "x \^-1" := (FracInterp.gginv x) (at level 20).

(* -------------------------------------------------------------------- *)
Section ECEval.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Local Notation "[ 'ecp' a *Y + b ]" := (ECPoly E (a, b)).
  Local Notation "[ 'ecp' a *Y - b ]" := (ECPoly E (a, -b)).
  Local Notation "'Y" := [ecp 1 *Y + 0].
  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ecX E p).

  Implicit Types f : {fraction ecpoly}.

  (* ------------------------------------------------------------------ *)
  Definition leadc (p : ecpoly) :=
    if   (degree [ecp p.1 *Y + 0%R] > degree [ecp 0%R *Y + p.2])%N
    then lead_coef p.1
    else lead_coef p.2.

  Definition ecreval p ecp :=
    if oncurve ecp then
      match ecp with
      | (|x, y|) => p.[x, y]
      | ∞        => leadc p
      end
    else 0.

  Definition eval (f : {fraction ecpoly}) ecp : {pp K} :=
    match order f ecp with
    | Posz (S _) => 0%:PP
    | Negz _     => [inf]
    | Posz 0     => (ecreval (decomp f ecp).1 ecp / ecreval (decomp f ecp).2 ecp)%:PP
    end.

  Definition evalK ecp (f : {fraction ecpoly}) : K :=
    if eval f ecp is x%:PP then x else 0.

  (* ------------------------------------------------------------------ *)
  Lemma leadc0: leadc 0 = 0.
  Proof.
    by rewrite /leadc; case: (_ < _)%N; rewrite lead_coef0.
  Qed.

  Lemma leadc_eq0 p: (leadc p == 0) = (p == 0).
  Proof.
    apply/idP/eqP; last by move=> ->; rewrite leadc0.
    case: p => [[p1 p2]]; rewrite /leadc /=; have [->|nz_p1] := eqVneq p1 0.
      by rewrite degree0 ltn0 lead_coef_eq0 => /eqP ->.
    rewrite degree_pX degree_pY //; case cmp: (_ < _)%N.
      by rewrite lead_coef_eq0 (negbTE nz_p1).
    rewrite lead_coef_eq0 => /eqP z_p2; move: cmp.
    rewrite !z_p2 size_poly0 muln0 /= => /negbT.
    by rewrite -leqNgt.
  Qed.

  Lemma leadc_pX p: leadc p%:E = lead_coef p.
  Proof. by rewrite /leadc /= degree0 ltn0. Qed.

  Lemma leadc_pY p: leadc [ecp p *Y + 0] = lead_coef p.
  Proof.
    have [->|nz_p] := eqVneq p 0; first by rewrite leadc0 lead_coef0.
    by rewrite /leadc /= degree0 degree_pY.
  Qed.

  Lemma leadcC c: leadc (c%:P)%:E = c.
  Proof. by rewrite leadc_pX lead_coefC. Qed.

  Lemma degree_odd_leadc (p : {ecpoly E}):
    odd (degree p) -> leadc p = lead_coef p.2.
  Proof.
    case: p => [[p1 p2]]; have [->|nz_p1] := eqVneq p1 0.
      by move=> _; rewrite /leadc /= degree0 ltn0.
    rewrite /leadc !(degree_pX, degree_pY) //=.
    rewrite degreeE /= nz_p1 muln1 /maxn; case: ltnP=> //.
    by move=> _; rewrite mul2n odd_double.
  Qed.

  Lemma degree_even_leadc (p : {ecpoly E}):
    ~~ odd (degree p) -> leadc p = lead_coef p.1.
  Proof.
    case: p => [[p1 p2]]; have [->|nz_p1] := eqVneq p1 0.
      have [->|nz_p2] := eqVneq p2 0; first by rewrite leadc0 lead_coef0.
      move: nz_p2; rewrite -size_poly_eq0 degree_pX.
      by case: (size p2) => [//|n] _; rewrite mul2n doubleS /= odd_double.
    rewrite /leadc !(degree_pX, degree_pY) //= degreeE.
    rewrite /maxn nz_p1 muln1 /=; case: ltnP => //.
    have [->|nz_p2] := eqVneq p2 0; first by rewrite size_poly0 muln0.
    move: nz_p2; rewrite -size_poly_eq0; case: (size p2) => [//|n] _.
    by move=> _; rewrite mul2n doubleS /= odd_double.
  Qed.

  Lemma leadcM p q: (leadc (p * q)) = (leadc p) * (leadc q).
  Proof.
    have [ho he] := (degree_odd_leadc, degree_even_leadc).
    have [->|nz_p] := eqVneq p 0; first by rewrite !(leadc0, simpm).
    have [->|nz_q] := eqVneq q 0; first by rewrite !(leadc0, simpm).
    have hodd: odd (degree (p * q)) = ~~ (odd (degree p) (+) odd (degree q)).
      rewrite degree_mul_id ?mulf_neq0 //.
      have := nz_p; rewrite -degree_eq0; case: (degree p) => [//|n] _.
      by rewrite addSn /= odd_add addNb negbK.
    case: (boolP (odd (degree p))); case: (boolP (odd (degree q))).
    + move=> qo po; rewrite (ho _ qo) (ho _ po) -lead_coefM.
      move: hodd; rewrite qo po => /= /degree_odd_leadc ->.
      rewrite mulE /dotp /= lead_coefDl //.
      have/degree_odd_nzpX nz_q2 := qo; have/degree_odd_nzpX nz_p2 := po.
      have [->|nz_p1] := eqVneq p.1 0.
        by rewrite !simpm size_poly0 lt0n size_poly_eq0 ?mulf_neq0.
      have [->|nz_q1] := eqVneq q.1 0.
        by rewrite !simpm size_poly0 lt0n size_poly_eq0 ?mulf_neq0.
      rewrite !size_mul ?mulf_neq0 ?XpolyN0 // size_Xpoly.
      rewrite addn4 /= prednK; last first.
        by rewrite lt0n addn_eq0 negb_and size_poly_eq0 nz_p1.
      rewrite -addSn -addnS -ltnS prednK; last first.
        by rewrite lt0n addn_eq0 negb_and size_poly_eq0 nz_p2.
      move: po; rewrite odd_degree_lt // -ltnNge => ltp.
      move: qo; rewrite odd_degree_lt // -ltnNge => ltq.
      by rewrite -addSn -addnS; apply: leq_add.
    + move=> qe po; rewrite (he _ qe) (ho _ po) -lead_coefM.
      move: hodd; rewrite (negbTE qe) po => /= /negbT /degree_even_leadc ->.
      rewrite mulE /dotp /= addrC; have/degree_odd_nzpX nz_p2 := po.
      have [->|nz_p1] := eqVneq p.1 0; first by rewrite !simpm.
      have [->|nz_q2] := eqVneq q.2 0; first by rewrite !simpm.
      have/degree_even_nzpY := qe => /(_ nz_q) nz_q1; rewrite lead_coefDl //.
      move: po; rewrite odd_degree_lt // -ltnNge => ltp.
      move: qe; rewrite odd_degree_lt // negbK => leq.
      rewrite !size_mul // -[size q.2]prednK ?(lt0n, size_poly_eq0) //.
      rewrite addnS /= -[size p.2]prednK ?(lt0n, size_poly_eq0) //.
      rewrite addSn /= -addSn; apply: leq_add.
      * by rewrite -ltnS prednK ?(lt0n, size_poly_eq0).
      * by rewrite -ltnS prednK // lt0n size_poly_eq0.
    + move=> qo pe; rewrite (ho _ qo) (he _ pe) -lead_coefM.
      move: hodd; rewrite (negbTE pe) qo => /= /negbT /degree_even_leadc ->.
      rewrite mulE /dotp /=; have/degree_odd_nzpX nz_q2 := qo.
      have [->|nz_q1] := eqVneq q.1 0; first by rewrite !simpm.
      have [->|nz_p2] := eqVneq p.2 0; first by rewrite !simpm.
      have/degree_even_nzpY := pe => /(_ nz_p) nz_p1 ; rewrite lead_coefDl //.
      move: qo; rewrite odd_degree_lt // -ltnNge => ltn.
      move: pe; rewrite odd_degree_lt // negbK => leq.
      rewrite !size_mul // -[size p.2]prednK ?(lt0n, size_poly_eq0) //.
      rewrite addSn /= -[size q.2]prednK ?(lt0n, size_poly_eq0) //.
      rewrite addnS /= -addnS; apply: leq_add.
      * by rewrite -ltnS prednK ?(lt0n, size_poly_eq0).
      * by rewrite -ltnS prednK // lt0n size_poly_eq0.
    + move=> qe pe; rewrite (he _ qe) (he _ pe) -lead_coefM.
      move: hodd; rewrite (negbTE qe) (negbTE pe) => /= /degree_odd_leadc ->.
      rewrite mulE /dotp /= addrC.
      have [->|nz_p2] := eqVneq p.2 0.
        by rewrite !simpm !lead_coefM (eqP (Xpoly_monic _)) mulr1.
      have [->|nz_q2] := eqVneq q.2 0.
        by rewrite !simpm !lead_coefM (eqP (Xpoly_monic _)) mulr1.
      have/degree_even_nzpY := pe => /(_ nz_p) nz_p1.
      have/degree_even_nzpY := qe => /(_ nz_q) nz_q1.
      rewrite lead_coefDl ?(lead_coefM) ?(eqP (Xpoly_monic _), simpm) //.
      move: pe; rewrite odd_degree_lt // negbK => leq1.
      move: qe; rewrite odd_degree_lt // negbK => leq2.
      rewrite !size_mul ?XpolyN0 ?mulf_neq0 // size_Xpoly.
      rewrite addn4 /= prednK; last first.
        by rewrite lt0n addn_eq0 size_poly_eq0 negb_and nz_p2.
      rewrite prednK; last first.
        by rewrite lt0n addn_eq0 size_poly_eq0 negb_and nz_p1.
      by rewrite -addSn -addnS; apply: leq_add.
  Qed.

  Lemma leadcX p n: (leadc (p ^+ n)) = (leadc p) ^+ n.
  Proof.
    elim: n => [|n IH]; first by rewrite !expr0 leadcC.
    by rewrite !exprS leadcM IH.
  Qed.      

  Lemma leadc_eqF n1 d1 n2 d2:
       n1 // d1 = n2 // d2
    -> leadc n1 / leadc d1 = leadc n2 / leadc d2.
  Proof.
    have [->/esym/eqP|nz_d1] := eqVneq d1 0.
      rewrite invr0 mulr0 mulf_eq0 invr_eq0 !tofrac_eq0.
      by case/orP=> /eqP->; rewrite !leadc0 ?(invr0, mulr0, mul0r).
    have [->/eqP|nz_d2] := eqVneq d2 0.
      rewrite invr0 mulr0 mulf_eq0 invr_eq0 !tofrac_eq0.
      by case/orP=> /eqP->; rewrite !leadc0 ?(invr0, mulr0, mul0r).
    move/eqP; rewrite divff_eq ?(mulf_neq0, tofrac_eq0) //.
    rewrite -!tofracM tofrac_eq => /eqP /(congr1 leadc) /eqP.
    by rewrite !leadcM -divff_eq ?(mulf_neq0, leadc_eq0) // => /eqP.
  Qed.

  Lemma leadc_addl n1 n2: (degree n2 < degree n1)%N -> leadc (n1 + n2) = leadc n1.
  Proof.
    have [->|nz_n1] := eqVneq n1 0; first by rewrite degree0 ltn0.
    have [->|nz_n2] := eqVneq n2 0; first by rewrite addr0.
    move=> lt; have/degree_addl := lt => eq;
      have [h|h] := (boolP (odd (degree (n1 + n2))));
      have := h; rewrite eq => h1.
    + have nz_n12: n1.2 != 0.
        apply/negP => /eqP z_n12; move: lt; rewrite (@odd_degreeE _ _ n1) //.
        by rewrite z_n12 size_poly0 ltn0.
      rewrite (degree_odd_leadc h) (degree_odd_leadc h1) addE /=.
      rewrite lead_coefDl //; case: (boolP (odd (degree n2))).
      * move=> h2; move: lt; do 2! rewrite odd_degreeE //.
        by move/ltn_pred; rewrite ltn_mul2l.
      * have [->|nz_n22] := eqVneq n2.2 0.
          by rewrite size_poly0 lt0n size_poly_eq0.
        move=> odd_degn2; have nz_n21: n2.1 != 0.
          apply/eqP=> z_n21; move: odd_degn2; rewrite degreeE.
          rewrite z_n21 eqxx !muln0 maxn0; case sz: (size n2.2) => [|n].
          + by move/eqP: sz; rewrite size_poly_eq0 (negbTE nz_n22).
          + by rewrite mul2n /= odd_double.
        have := odd_degn2; rewrite odd_degree_lt // negbK.
        rewrite -(@leq_pmul2l 2) // => le1.
        have := lt; rewrite even_degreeE // odd_degreeE //.
        rewrite (negbTE nz_n21) muln1; move/(leq_ltn_trans le1).
        have := nz_n12; rewrite -size_poly_eq0; case: (size n1.2) => [//|k] _.
        by rewrite mulnS /= !ltnS leq_mul2l.
    + rewrite !degree_even_leadc // addE /= lead_coefDl //.
      have := lt; rewrite !degreeE leq_max; case/orP.
      * rewrite gtn_max; case/andP=> _; have [->|nz_n21] := eqVneq n2.1 0.
          move=> _; rewrite size_poly0 lt0n size_poly_eq0.
          by rewrite (degree_even_nzpY nz_n1 h1).
        rewrite nz_n21 muln1; have [->|nz_n12] := eqVneq n1.2 0.
          by rewrite size_poly0.
        have := h1; rewrite degreeE; have [->|nz_n11] := eqVneq n1.1 0.
          rewrite size_poly0 eqxx maxn0 -[size _]prednK; last first.
            by rewrite lt0n size_poly_eq0.
          by rewrite mulnS /= mul2n odd_double.
        move=> _; move: h1; rewrite odd_degree_lt // negbK.
        rewrite -{2}[size n1.2]prednK ?(size_poly_eq0, lt0n) //.
        rewrite [(2 * _.-1.+1)%N]mulnS /= ltnS leq_mul2l /=.
        move=> le1 le2; apply: (@leq_trans (size n1.2).-1) => //.
        by case: (size n1.2) le1.
      * rewrite gtn_max; case/andP=> _; have [->|nz_n11] := eqVneq n1.1 0.
          by rewrite eqxx !muln0.
        rewrite nz_n11 muln1; have [->|nz_n21] := eqVneq n2.1 0.
          by move=> _; rewrite size_poly0 lt0n size_poly_eq0.
        by rewrite nz_n21 muln1 ltn_mul2l /= ltnS.
  Qed.

  Lemma leadcD_eq0 (f g : ecpoly): 
       degree f = degree g
    -> (degree (f + g)%R < degree f)%N
    -> leadc f + leadc g = 0.
  Proof.
    have hpoly (p q : {poly K}): 
         size p = size q
      -> (size (p + q)%R < size p)%N
      -> lead_coef p + lead_coef q = 0.
    + move=> eqsz ltsz; rewrite !lead_coefE -eqsz -coefD.
      apply/(leq_sizeP (p + q) (size (p + q)))=> //.
      by rewrite -ltnS (ltn_predK ltsz).
    move=> eq; have/(congr1 odd) := eq; case: (boolP (odd _)).
    + move=> oddf /esym oddg lt; rewrite !degree_odd_leadc //.
      have nz_f2 := degree_odd_nzpX oddf.
      have nz_g2 := degree_odd_nzpX oddg.
      move: eq; do 2! rewrite odd_degreeE //.
      move/eqP; rewrite -eqSS !prednK ?(lt0n, muln_eq0, size_poly_eq0) //.
      rewrite eqn_mul2l /= => /eqP eq; apply: hpoly => //.
      move: lt; rewrite (degreeE (f+g)) !addE /= gtn_max.
      case/andP; rewrite odd_degreeE // => h _; move: h.
      by move/ltn_pred; rewrite ltn_mul2l /=.
    + move=> Noddf /esym /negbT Noddg; have [->|nz_f] := eqVneq f 0.
        by rewrite degree0 ltn0.
      have [->|nz_g] := eqVneq g 0; first by rewrite addr0 ltnn.
      have := degree_even_nzpY nz_f Noddf => nz_f1.
      have := degree_even_nzpY nz_g Noddg => nz_g1.
      rewrite !degree_even_leadc //; move: eq.
      do 2! (rewrite even_degreeE //); rewrite nz_f1 nz_g1.
      move/eqP; rewrite !muln1 eqn_mul2l /= eqSS => /eqP eq.
      rewrite degreeE gtn_max; case/andP=> _ h.
      have: (size (f.1 + g.1)%R < size f.1)%N.
        have [->|nz_f1Dg1] := eqVneq (f.1 + g.1) 0.
          by rewrite size_poly0 lt0n size_poly_eq0.
        move: h; rewrite !addE /= nz_f1Dg1 muln1.
        by rewrite ltn_mul2l /= ltnS.
      by apply: hpoly.
  Qed.

  Lemma leadcD (f g : ecpoly): 
       degree f = degree g
    -> degree f = degree (f + g)
    -> leadc (f + g) = leadc f + leadc g.
  Proof.
    move=> eq1 eq2; have hpoly (p q : {poly K}):
         size p = size q
      -> size p = size (p + q)
      -> lead_coef (p + q) = lead_coef p + lead_coef q.
    + by move=> eqsz eqszD; rewrite !lead_coefE -eqsz -eqszD -coefD.
    have/(congr1 odd) := eq1 => h1; have/(congr1 odd) := eq2 => h2.
    move: h1 h2; case: (boolP (odd (degree f))).
    + move=> oddf /esym oddg /esym oddfDg.
      rewrite !degree_odd_leadc // addE /=.
      have nz_f2 := degree_odd_nzpX oddf.
      have nz_g2 := degree_odd_nzpX oddg.
      have nz_f2Dg2 := degree_odd_nzpX oddfDg.
      apply: hpoly.
      + move: eq1; do 2! (rewrite odd_degreeE //); move/eqP.
        rewrite -eqSS !prednK ?(lt0n, muln_eq0, size_poly_eq0) //.
        by rewrite eqn_mul2l /= => /eqP eq1.
      + move: eq2; do 2! (rewrite odd_degreeE //); move/eqP.
        rewrite -eqSS !prednK ?(lt0n, muln_eq0, size_poly_eq0) //.
        by rewrite addE eqn_mul2l /= => /eqP eq2.
    + move=> Noddf /esym /negbT Noddg /esym /negbT NoddfDg.
      rewrite !degree_even_leadc // addE /=.
      have [->|nz_f] := eqVneq f 0.
        by rewrite lead_coef0 !(addr0, add0r).
      have nz_g: g != 0 by rewrite -degree_eq0 -eq1 degree_eq0.
      have nz_fDg: f + g != 0 by rewrite -degree_eq0 -eq2 degree_eq0.
      have nz_f1 := degree_even_nzpY nz_f Noddf.
      have nz_g1 := degree_even_nzpY nz_g Noddg.
      have nz_f1Dg1 := degree_even_nzpY nz_fDg NoddfDg.
      apply: hpoly.
      + move: eq1; do 2! (rewrite even_degreeE //); move/eqP.
        by rewrite nz_f1 nz_g1 !muln1 eqn_mul2l /= eqSS => /eqP.
      + move: eq2; do 2! (rewrite even_degreeE //); move/eqP.
        by rewrite nz_f1 nz_f1Dg1 !muln1 eqn_mul2l /= eqSS addE => /eqP.
  Qed.

  Lemma ecreval0 p: ecreval 0 p = 0.
  Proof.
    rewrite /ecreval; case: (oncurve _) => //.
    by case: p=> [|x y] /=; [rewrite leadc0|rewrite eceval0].
  Qed.

  Lemma ecreval_outcve p ecp:
    ~~(oncurve ecp) -> ecreval p ecp = 0.
  Proof.
    by move=> outcve; rewrite /ecreval (negbTE outcve).
  Qed.

  Lemma ecrevalM (f g : ecpoly) p:
    ecreval (f * g) p = (ecreval f p) * (ecreval g p).
  Proof.
    rewrite /ecreval; case oncve: (oncurve p); last first.
      by rewrite mulr0.
    case: p oncve => [|x y] oncve.
    + by rewrite leadcM.
    + by rewrite eceval_mul.
  Qed.

  Lemma ecreval_num_decomp_neq0 f p:
    oncurve p -> f != 0 -> ecreval (decomp f p).1 p != 0.
  Proof.
    move=> oncve nz_f; rewrite /ecreval oncve.
    move: (decomp_correct nz_f oncve); case: {oncve} p => [|x y] uk.
    + by rewrite leadc_eq0 (uniok_nz_num uk).
    + by rewrite (uniok_fin_num_eval_neq0 uk).
  Qed.

  Lemma ecreval_den_decomp_neq0 f p:
    oncurve p -> f != 0 -> ecreval (decomp f p).2 p != 0.
  Proof.
    move=> oncve nz_f; rewrite /ecreval oncve.
    move: (decomp_correct nz_f oncve); case: {oncve} p => [|x y] uk.
    + by rewrite leadc_eq0 (uniok_nz_den uk).
    + by rewrite (uniok_fin_den_eval_neq0 uk).
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma eval_outcve f p:
    ~~(oncurve p) -> eval f p = 0%:PP.
  Proof.
    by move=> outcve; rewrite /eval order_outcve ?ecreval_outcve ?mul0r.
  Qed.

  Lemma eval0 p: eval 0 p = 0%:PP.
  Proof.
    by rewrite /eval order0 /= decomp0 ecreval0 mul0r.
  Qed.

  Lemma eval_lt0_order (f : {fraction ecpoly}) p:
    (order f p < 0) = (eval f p == [inf]).
  Proof. by rewrite /eval; case: (order _ _)=> [[|n]|n]. Qed.

  Lemma order_lt0_eval (f : {fraction ecpoly}) p:
    order f p < 0 -> eval f p = [inf].
  Proof. by rewrite eval_lt0_order => /eqP. Qed.

  Lemma order_gt0_eval (f : {fraction ecpoly}) p:
    order f p > 0 -> eval f p = 0%:PP.
  Proof. by rewrite /eval; case: (order _ _)=> [[|n]|n]. Qed.

  Lemma eval_gt0_order (f : {fraction ecpoly}) p:
    f != 0 -> oncurve p -> (order f p > 0) = (eval f p == 0%:PP).
  Proof.
    move=> nz_f oncve; apply/idP/idP.
      by move/order_gt0_eval=> ->.
    rewrite /eval; case: (order _ _)=> [[|n]|n] //=.
    move/eqP=> [] /eqP; rewrite mulf_eq0 invr_eq0.
    rewrite (negbTE (ecreval_num_decomp_neq0 _ _)) //.
    by rewrite (negbTE (ecreval_den_decomp_neq0 _ _)).
  Qed.

  Lemma evalfin_eq0_order (f : {fraction ecpoly}) x y:
    let p  := (|x, y|) in
    let nd := decomp f p in
       order f p == 0 -> eval f p = (nd.1.[x, y] / nd.2.[x, y])%:PP.
  Proof.
    move=> p nd /eqP z_ordfp; rewrite /eval z_ordfp /=.
    case oncve: (oncurve p); last first.
      rewrite /nd ecreval_outcve ?decomp_outcve ?oncve //=.
      by rewrite eceval0 !mul0r.
    by rewrite /ecreval oncve.
  Qed.

  Lemma evalinf_eq0_order (f : {fraction ecpoly}):
    let nd := decomp f ∞ in
      order f ∞ == 0 -> eval f ∞ = ((leadc nd.1) / (leadc nd.2))%:PP.
  Proof.
    by move=> nd z_ord_f; rewrite /eval (eqP z_ord_f) /=.
  Qed.

  Lemma eval_eq0_order (f : {fraction ecpoly}) p:
    let nd := decomp f p in
      order f p == 0 -> eval f p = (ecreval nd.1 p / ecreval nd.2 p)%:PP.
  Proof.
    move=> nd; case oncve: (oncurve p); last first.
      by rewrite !(eval_outcve, ecreval_outcve) ?oncve // mul0r.
    by rewrite /eval /ecreval oncve => /eqP -> /=.
  Qed.

  Lemma eval_eq0_orderP (f : {fraction ecpoly}) p:
    oncurve p -> f != 0 ->
      reflect
        (exists2 c, c != 0 & eval f p = c%:PP)
        (order f p == 0).
  Proof.
    move=> oncve nz_f; apply: (iffP eqP) => z_ordfp; last first.
      case: z_ordfp=> c nz_c; rewrite /eval.
      case: (order _ _)=> [[|o]|o] //; case=> /esym z_c.
     by rewrite z_c eqxx in nz_c.
    have f_uk := decomp_correct nz_f oncve.
    rewrite /eval z_ordfp /=;
      case: {z_ordfp} p oncve f_uk => [|x y] oncve f_uk;
      set c := (_ / _); exists c => //; rewrite /c => {c}.
    + rewrite mulf_eq0 invr_eq0 !leadc_eq0.
      rewrite (negbTE (uniok_nz_num f_uk)).
      by rewrite (negbTE (uniok_nz_den f_uk)).
    + rewrite mulf_eq0 invr_eq0 /ecreval oncve.
      rewrite (negbTE (uniok_fin_num_eval_neq0 f_uk)).
      by rewrite (negbTE (uniok_fin_den_eval_neq0 f_uk)).
  Qed.

  Lemma eval_ge0_orderP (f : {fraction ecpoly}) p:
    reflect
      (exists c, eval f p = c%:PP)
      (0 <= order f p).
  Proof.
    have [->|nz_f] := eqVneq f 0.
      by rewrite order0 eval0 lerr; constructor; exists 0.
    case oncve: (oncurve p); last first.
      rewrite order_outcve ?eval_outcve ?oncve // lerr.
      by constructor; exists 0.
    apply: (iffP idP); last first.
      by case=> c; rewrite /eval; case: (order _ _).
    rewrite ler_eqVlt; case/orP.
      rewrite eq_sym => /(eval_eq0_orderP oncve nz_f).
      by case=> c _ eq; exists c.
    rewrite /eval; case: (order _ _)=> [[|o]|o] // _.
    by exists 0.
  Qed.

  Lemma eval_fin_order_ge0 (f : {fraction ecpoly}) p c:
    eval f p = c%:PP -> 0 <= order f p.
  Proof. by move=> h; apply/eval_ge0_orderP; exists c. Qed.

  Lemma evalE_fin_ord_ge0 n d x y:
       oncurve (|x, y|) -> d.[x, y] != 0
    -> eval (n // d) (|x, y|) = (n.[x, y] / d.[x, y])%:PP.
  Proof.
    move=> xy_oncve nz_dxy; have [->|nz_n] := eqVneq n 0.
      by rewrite eceval0 !mul0r eval0.
    have nz_d: d != 0.
      by apply/negP=> /eqP z_d; move: nz_dxy; rewrite z_d eceval0 eqxx.
    have nz_nd: n // d != 0.
      by rewrite mulf_eq0 invr_eq0 !tofrac_eq0 (negbTE nz_n).
    have := poly_order_correct nz_n xy_oncve.
    have := poly_order_correct nz_d xy_oncve.
    set p := (|x, y|); rewrite /eval orderE //.
    case ponE: (poly_order n p) => [on [nn dn]].
    case podE: (poly_order d p) => [od [nd dd]].
    have := (decomp_correct nz_nd xy_oncve); rewrite -/p => nd_uk.
    have/uniok_decomp := nd_uk; rewrite orderE // ponE podE /= => eq.
    move=> d_uk n_uk /=; case cmp_o: (on - od) => [o|o]; last first.
      move: eq; rewrite cmp_o /exprz [_ ^- _ * _]mulrC -mulrA.
      move/eqP; rewrite -tofracX -invfM -tofracM frac_eq; last first.
        rewrite !mulf_neq0 // ?expf_eq0 /= ?(uniok_nz_den nd_uk) //.
        by move: (unifun_neq0 E (|x, y|)); rewrite /= tofrac_eq0.
      rewrite eq_sym => /eqP /(congr1 (fun p => eceval p x y)).
      rewrite mulrA [X in _ = X]eceval_mul // eceval_exp //.
      rewrite eceval_unifun_fin expr0n mulr0 => /eqP.
      rewrite eceval_mul // mulf_eq0; move: (uniok_fin_num_eval_neq0 nd_uk).
      by move/negbTE=> ->; rewrite (negbTE nz_dxy).
    case: o cmp_o eq => [|o] cmp_o; rewrite ?(cmp_o, expr0z, simpm) /= => eq.
      have/uniok_fin_den_eval_neq0 nz_decomp_nd_den_xy := nd_uk.
      have/uniok_nz_den nz_decomp_den_nd := nd_uk.
      congr (_%:PP); apply/eqP; rewrite divff_eq; last first.
        by rewrite /ecreval xy_oncve /= mulf_neq0.
      move/eqP: eq; rewrite frac_eq ?mulf_neq0 // eq_sym => /eqP.
      rewrite /ecreval xy_oncve /= => /(congr1 (fun p => eceval p x y)).
      by rewrite !eceval_mul // => /eqP.
    move/eqP: eq; rewrite /exprz -tofracX -tofracM frac_eq; last first.
      by rewrite mulf_neq0 // (uniok_nz_den nd_uk).
    move/eqP/(congr1 (fun p => eceval p x y)); rewrite !eceval_mul //.
    rewrite eceval_exp // eceval_unifun_fin expr0n !mul0r => /eqP.
    rewrite mulf_eq0 (negbTE (uniok_fin_den_eval_neq0 nd_uk)) orbF.
    by move/eqP=> ->; rewrite mul0r.
  Qed.

  Lemma eval_finF p x y: oncurve (|x, y|) -> eval p%:F (|x, y|) = p.[x, y]%:PP.
  Proof.
    move=> oncve; rewrite -[p%:F]divr1 -tofrac1.
    by rewrite evalE_fin_ord_ge0 ?(eceval1, oner_eq0) // divr1.
  Qed.

  Lemma evalC c (p : point K):
    oncurve p -> eval ((c%:P)%:E)%:F p = c%:PP.
  Proof.
    have [->|nz_c] := eqVneq c 0; first by rewrite eval0.
    case: p => [|x y] oncve.
    + rewrite /eval orderC /= /ecreval /=; congr (_%:PP).
      have {3}->: c = leadc (c%:P)%:E / leadc 1.
        by rewrite !leadcC divr1.
      apply: leadc_eqF; have nz_cF: ((c%:P)%:E)%:F != 0.
        by rewrite tofrac_eq0 ecX_eq0 polyC_eq0.
      move/uniok_decomp: (decomp_correct nz_cF oncve).
      by rewrite orderC expr0z mul1r => {3}->; rewrite divr1.
    + by rewrite eval_finF // ecX_eceval hornerE.
  Qed.

  Lemma evalM (f g : {fraction ecpoly}) p:
       (sgz (order f p)) * (sgz (order g p)) >= 0
    -> (eval (f * g) p) = (eval f p) \* (eval g p).
  Proof.
    case oncve: (oncurve p); last first.
      by rewrite !eval_outcve ?oncve //= mulr0.
    wlog: f g / (order f p) <= (order g p).
      move=> wlog sg; case: (lerP (order f p) (order g p)).
        by move/wlog; apply.
      move/ltrW=> cmp_ord; rewrite mulrC [X in _ = X]Monoid.mulmC /=.
      by apply: wlog=> //; rewrite mulrC.
    case: (f =P 0) => [->|/eqP nz_f].
      move=> _; by rewrite mul0r eval0 mul0p.
    case: (g =P 0) => [->|/eqP nz_g].
      by move=> _; rewrite mulr0 eval0 mulp0.
    move=> cmp_ord; case: (ltrP (order f p) 0) => [ord_fp_lt0|].
      rewrite nmulr_rge0 ?sgz_lt0 // sgz_le0 ler_eqVlt; case/orP.
        move=> z_ord_gp; rewrite order_lt0_eval; last first.
          by rewrite order_mul ?mulf_neq0 // (eqP z_ord_gp) addr0.
        case/(eval_eq0_orderP oncve nz_g): z_ord_gp => [c nz_c ->].
        by rewrite order_lt0_eval //= (negbTE nz_c).
      move=> ord_gp_lt0; rewrite !order_lt0_eval //=.
      by rewrite order_mul ?mulf_neq0 //= ltr_snsaddr.
    move=> ord_fp_ge0; have ord_gp_ge0: (0 <= order g p).
      by apply: (ler_trans ord_fp_ge0).
    move=> _; rewrite /eval order_mul ?mulf_neq0 //.
    move: ord_fp_ge0 ord_gp_ge0; case: (order f p)=> [[|n1]|n1] //; last first.
      by case: (order g p)=> [[|n2]|n2]; rewrite //= ?mul0r.
    move=> _; case: (order g p)=> [[|n2]|n2] //=; last by rewrite mulr0.
    move=> _; congr (_%:PP); rewrite mulfE -!ecrevalM.
    have nz_fg: f * g != 0 by rewrite mulf_neq0.
    have ufk  := (decomp_correct nz_f oncve).
    have ugk  := (decomp_correct nz_g oncve).
    have uk1 := uniok_mul (unifun_neq0 _ p) oncve ufk ugk.
    have uk2 := decomp_correct nz_fg oncve.
    apply/eqP; rewrite divff_eq; last first.
      by rewrite ecrevalM !mulf_neq0 // ecreval_den_decomp_neq0.
    rewrite -!ecrevalM; move: (uniok_uniq nz_fg oncve uk1 uk2)=> /andP [_].
    rewrite frac_eq; last first.
      by rewrite !mulf_neq0 // decomp_nz_den.
    by move/eqP=> ->.
  Qed.

  Lemma evalV (f : {fraction ecpoly}) p:
    eval f p != 0%:PP -> eval (f^-1) p = (eval f p) \^-1.
  Proof.
    move=> nz_eval_fp; rewrite /eval order_inv.
    case: (order _ _) => [[|o]|o] /=; rewrite ?eqxx //.
    rewrite mulf_eq0 invr_eq0; have nz_f: f != 0.
      by apply/negP=> /eqP z_f; rewrite z_f eval0 eqxx in nz_eval_fp.
    have oncve: oncurve p.
      case oncve: (oncurve _)=> //; move: nz_eval_fp.
      by rewrite eval_outcve ?oncve ?eqxx.
    rewrite (negbTE (ecreval_num_decomp_neq0 oncve nz_f)).
    rewrite (negbTE (ecreval_den_decomp_neq0 oncve nz_f)).
    rewrite /=; congr _%:PP; rewrite invfE.
    have nz_Vf: f^-1 != 0 by rewrite invr_eq0.
    move/uniok_decomp/eqP: (decomp_correct nz_Vf oncve).
    rewrite {1} (uniok_decomp (decomp_correct nz_f oncve)).
    rewrite order_inv invfM invfE invr_expz inj_eq; last first.
      by apply: mulfI; rewrite expfz_neq0 // unifun_neq0.
    rewrite frac_eq; last first; rewrite ?mulf_neq0 //.
      by rewrite (decomp_nz_num nz_f oncve).
      by rewrite (decomp_nz_den nz_Vf oncve).
    move/eqP/(congr1 (ecreval^~ p)) => eq; apply/eqP.
    rewrite divff_eq; last first; rewrite ?mulf_neq0 //.
      by rewrite (ecreval_den_decomp_neq0 oncve nz_Vf).
      by rewrite (ecreval_num_decomp_neq0 oncve nz_f).
    by rewrite -!ecrevalM eq eqxx.
  Qed.

  Lemma evalM_finL (f g : {fraction ecpoly}) (p : point K):
    order f p = 0 -> (eval (f * g) p) = (eval f p) \* (eval g p).
  Proof. by move=> h; apply: evalM; rewrite h sgz0 mul0r. Qed.

  Lemma evalN (f : {fraction ecpoly}) (p : point K):
    eval (-f) p = \- (eval f p).
  Proof.
    have [oncve|outcve] := boolP (oncurve p); last first.
      by rewrite !eval_outcve //= oppr0.
    rewrite -mulN1r; have ->: -1 = (((-1)%:P)%:E)%:F.
      by rewrite polyC_opp ecXN tofracN.
    rewrite evalM_finL ?orderC // evalC //; case: (eval f p) => [x|] /=.
    + by rewrite mulN1r.
    + by rewrite oppr_eq0 oner_eq0.
  Qed.
 
  Lemma eval_uniformizer u p: uniformizer u p -> eval u p = 0%:PP.
  Proof.
    move=> u_uz; apply: order_gt0_eval.
    by rewrite /uniformizer in u_uz; rewrite (eqP u_uz).
  Qed.

  Lemma eval_unifun p: oncurve p -> eval (unifun E p) p = 0%:PP.
  Proof.
    by move=> oncve; rewrite eval_uniformizer // uniformizer_unifun.
  Qed.

  (* FIXME: duplicate code from order_add / order_add_leq *)
  Lemma evalDl (f g : {fraction ecpoly}) (p : point K):
       isfinite (eval f p)
    -> (eval (f + g) p) = (eval f p) \+ (eval g p).
  Proof.
    have leq_predn n m: (n <= m -> n.-1 <= m.-1)%N.
      by case: n m => [|n] [|m].
    have [oncve|outcve] := boolP (oncurve p); last first.
      by move=> _; rewrite !eval_outcve //= addr0.
    have [->|nz_f] := eqVneq f 0.
      by rewrite add0r eval0 Monoid.mul1m.
    have [->|nz_g] := eqVneq g 0.
      by rewrite addr0 eval0 Monoid.mulm1.
    have [eq|nz_fDg] := eqVneq (f + g) 0.
      rewrite eq eval0; move/eqP: eq; rewrite addr_eq0.
      move/eqP=> eq h; rewrite eq evalN Monoid.mulmC /=.
      move: h; rewrite eq evalN; case: (eval g p) => //.
      by move=> x /=; rewrite subrr.
    case: (ltrP (order f p) 0); first by move/order_lt0_eval => ->.
    move=> hf _; case: (ltrP (order g p) 0) => hg.
      have/order_lt0_eval := hg => -> /=.
      have ->: eval f p \+ [inf] = [inf] by case (eval _ _).
      apply/eqP; rewrite -eval_lt0_order order_add.
      + by rewrite ltr_minl hg orbT.
      + by rewrite mulf_neq0.
      + move: (ltr_le_trans hg hf); rewrite ltr_neqAle.
        by case/andP=> h _; rewrite eq_sym.
    wlog: f g nz_f nz_g nz_fDg hf hg / order f p <= order g p; last move=> le.
      move=> wlog; case: (lerP (order f p) (order g p)).
        by move/wlog; apply.
      move/ltrW/wlog; rewrite [f + g]addrC [_ \+ _]Monoid.mulmC.
      by apply => //; rewrite addrC.
    have := decomp_correct nz_f oncve;
    have := decomp_correct nz_g oncve;
      set nf := (decomp f p).1; set df := (decomp f p).2;
      set ng := (decomp g p).1; set dg := (decomp g p).2;
      move=> uokg uokf.
    have nz_nf: nf != 0 by rewrite decomp_nz_num.
    have nz_ng: ng != 0 by rewrite decomp_nz_num.
    have nz_df: df != 0 by rewrite decomp_nz_den.
    have nz_dg: dg != 0 by rewrite decomp_nz_den.
    pose u := unifun E p; pose fd := order f p; pose gd := order g p.
    have orduD n: order (u ^+ n) p = n.
      move: (uniformizer_unifun oncve); rewrite /uniformizer.
      by rewrite order_exp; move/eqP => ->; rewrite natz.
    have evuD n: eval (u ^+ n) p = ((n == 0%N)%:R)%:PP; first case: n => [|n].
    + by rewrite expr0 evalC.
    + by rewrite order_gt0_eval // orduD.
    move: (erefl (f + g)); rewrite {1}(uniok_decomp uokf) {1}(uniok_decomp uokg).
    rewrite -/fd -/gd -/u; have ->: gd = fd - (fd - gd).
      by rewrite opprD addrA subrr add0r opprK.
    rewrite expfzDr ?unifun_neq0 // -mulrA -mulrDr opprB.
    have ->: gd - fd = `|gd - fd| :> int by rewrite ger0_norm // subr_ge0.
    rewrite -!exprnP; case: (p =P ∞) => [|/eqP] pE /=; last first.
    * have: forall p, p != ∞ -> exists xy, p = (|xy.1, xy.2|).
        by move=> T [|x y] // _; exists (x, y).
      move=> h; case/h: pE => [[x y]] /= pE {h}; rewrite pE.
      move: oncve uokf uokg; rewrite pE => oncve /= uokf uokg.
      have evuM k n d: d.[x, y] != 0 ->
          eval (u ^+ k * (n // d)) (|x, y|)
        = ((k == 0%N)%:R * (n.[x, y] / d.[x, y]))%:PP.
      + move=> nz_dxy; rewrite evalM; last first.
          rewrite -sgzM sgz_ge0 mulr_ge0 //.
          - by rewrite -pE orduD.
          - by apply/eval_ge0_orderP; eexists; rewrite pE evalE_fin_ord_ge0.
        by rewrite -pE evuD pE evalE_fin_ord_ge0 //=.
      have nz_dfxy := (uniok_fin_den_eval_neq0 uokf).
      have nz_dgxy := (uniok_fin_den_eval_neq0 uokg).
      rewrite {2}/u pE /= -tofracX mulrA -tofracM addf_div ?tofrac_eq0 //.
      rewrite -!(tofracM, tofracD); set n := (_ + _); set d := (df * _).
      have nz_dxy: d.[x, y] != 0 by rewrite /d eceval_mul // mulf_neq0.
      have ->: fd = `|fd| :> int by rewrite ger0_norm.
      move/esym=> eq; rewrite eq -exprnP evuM //.
      rewrite (uniok_fin_decomp uokf) (uniok_fin_decomp uokg).
      rewrite -!/(unifun _ (|x, y|)) -!pE -/fd -/gd -/u.
      have {2}->: fd = `|fd| :> int by rewrite ger0_norm.
      have    ->: gd = `|gd| :> int by rewrite ger0_norm.
      rewrite -!exprnP pE !evuM // /n !(eceval_add, eceval_mul) //.
      rewrite eceval_exp // eceval_unifun_fin expr0n.
      have [z_fd|nz_fd] := eqVneq fd 0.
      + by rewrite z_fd absz0 eqxx !simpm /= addf_div.
      + rewrite absz_eq0 (negbTE nz_fd) !simpm /=.
        move: hf; rewrite ler_eqVlt eq_sym (negbTE nz_fd) /=.
        move/(ltr_le_trans) => /(_ _ le); rewrite ltr_neqAle.
        case/andP; rewrite eq_sym => nz_gd _; rewrite absz_eq0.
        by rewrite (negbTE nz_gd) !mul0r.
    * have := hf; rewrite ler_eqVlt; case/orP; last first.
        move=> gt0_ordf; have gt0_ordg: 0 < order g p.
          by apply: (ltr_le_trans gt0_ordf).
        have: 0 < order (f + g) p.
          apply: (@ltr_le_trans _ (Num.min (order f p) (order g p))).
          + by rewrite ltr_minr gt0_ordf gt0_ordg.
          + by apply order_add_leq; rewrite ?mulf_neq0.
        by move=> gt0_ordfDg; rewrite !order_gt0_eval //= addr0.
      rewrite -/fd => /eqP /esym z_fd; rewrite z_fd -exprnP expr0 mul1r subr0.
      rewrite {1}/u {1}pE /= divf_exp -!tofracX mulf_div -!tofracM.
      rewrite addf_div ?(mulf_neq0, tofrac_eq0, expf_neq0, ecY_neq0) //.
      rewrite -!(tofracM, tofracD) [nf*_]mulrCA -!mulrA [df*_]mulrCA.
      set n := _ + _; set d := _ * (_ * _).
      set r := _ // _ => rE; have := nz_fDg; rewrite -{1}rE {1}/r.
      rewrite mulf_eq0 invr_eq0 !tofrac_eq0.
      case/norP; move=> nz_n nz_d; have/(congr1 (@fdegree _ _)) := rE.
      rewrite {1}/r /n /d fdegreeE 1?mulf_neq0 //.
      have [z_gd|nz_gd] := eqVneq gd 0; first rewrite z_gd.
      + rewrite absz0 !expr0 !(mul1r, mulr1) => /esym degfE.
        rewrite {-1}/eval -/fd -/gd z_fd z_gd /=.
        rewrite -/nf -/df -/ng -/dg pE /ecreval /=.
        rewrite addf_div ?leadc_eq0 // -!leadcM.
        move: (degree_add (nf * dg) (ng * df)).
        have eq_deg: degree (nf * dg) = degree (df * ng).
          rewrite !degree_mul_id ?mulf_neq0 //.
          move: uokg; rewrite pE /= => /uniok_inf_degeq => ->.
          by move: uokf; rewrite pE /= => /uniok_inf_degeq => ->.
        rewrite eq_deg [ng*_]mulrC maxnn -lez_nat -subr_le0.
        rewrite degree_mul_id ?mulf_neq0 //.
        have := uokg; rewrite pE /= => /uniok_inf_degeq => ->.
        rewrite -!degree_mul_id ?mulf_neq0 // {1}[df*ng]mulrC.
        rewrite -degfE ler_eqVlt; case/orP.
        * move/eqP=> z_degf; have h:
              leadc (nf * dg + ng * df)
            = leadc (nf * dg) + leadc (ng * df).
          + apply: leadcD; first by rewrite [ng*_]mulrC.
            move/eqP: degfE; rewrite z_degf eq_sym subr_eq0 eqz_nat.
            rewrite degree_mul_id ?mulf_neq0 //.
            have := uokf; rewrite pE /= => /uniok_inf_degeq => ->.
            by rewrite -degree_mul_id ?mulf_neq0 // => /eqP <-.
          move/eqP: z_degf; rewrite -[X in X==0]opprK -order_fdegree oppr_eq0.
          rewrite -pE => /eqP z_ordfDg.
          rewrite pE /eval /= -pE z_ordfDg /= pE /ecreval /= -pE.
          move/uniok_decomp: (decomp_correct nz_fDg oncve).
          rewrite z_ordfDg -exprnP expr0 !mul1r -rE /r.
          move/leadc_eqF=> <-; rewrite [_*ng]mulrC -h.
          by rewrite /n /d z_gd absz0 !expr0 !mul1r.
        * move=> lt0_fdeg; have := lt0_fdeg.
          rewrite -[X in X<0]opprK -order_fdegree oppr_lt0 => gt0_ordfDg.
          have h: leadc (nf * dg) + leadc (ng * df) = 0; first apply: leadcD_eq0.
          + by rewrite [ng*_]mulrC; apply: eq_deg.
          + rewrite degree_mul_id ?mulf_neq0 //.
            have := uokf; rewrite pE /= => /uniok_inf_degeq => ->.
            rewrite -degree_mul_id ?mulf_neq0 //.
            by move: lt0_fdeg; rewrite degfE subr_lt0 ltz_nat.
          by rewrite order_gt0_eval // [df*ng]mulrC h mul0r.
      + have lt_deg: (  degree ('X%:E ^+ `|gd| * (ng * df))%R
                      < degree ('Y ^+ `|gd| * (nf * dg))%R)%N.
          rewrite ![degree (_*(_*_))]degree_mul_id; first last.
          * by rewrite mulf_neq0 1?expf_neq0 ?ecX_neq0 // mulf_neq0.
          * by rewrite mulf_neq0 1?expf_neq0 ?ecY_neq0 // mulf_neq0.
          rewrite degree_expX degree_expY !degree_mul_id ?mulf_neq0 // !addSn /=.
          move: uokg; rewrite pE /= => /uniok_inf_degeq => ->.
          move: uokf; rewrite pE /= => /uniok_inf_degeq => ->.
          rewrite [X in X.-1%N]addnC ltn_add2r ltn_mul2r andbT.
          by rewrite lt0n absz_eq0.
        have eq_degnd: degree n = degree d.
          rewrite /n /d degree_addl //.
          rewrite !degree_mul_id ?(mulf_neq0, expf_neq0, ecY_neq0) //.
          by move: uokf; rewrite pE /= => /uniok_inf_degeq => ->.
        rewrite -/n -/d eq_degnd subrr => /esym z_degfDg.
        have: order (f + g) p = 0.
          by rewrite pE order_fdegree z_degfDg oppr0.
        have := hg; rewrite ler_eqVlt -/gd eq_sym (negbTE nz_gd) /=.
        move/order_gt0_eval => ->; rewrite Monoid.mulm1 => z_ordfDg.
        rewrite /eval z_ordfDg -/fd z_fd /= -/nf -/df.
        move/uniok_decomp: (decomp_correct nz_fDg oncve).
        rewrite z_ordfDg -exprnP expr0 mul1r -{1}rE /r => /leadc_eqF eq_lc.
        rewrite pE /ecreval /= -pE -eq_lc /n /d leadc_addl //.
        rewrite !leadcM !leadcX leadc_pY !lead_coef1 !expr1n !mul1r.
        by rewrite -mulf_div divff ?leadc_eq0 // mulr1.
  Qed.

  Lemma evalDr (f g : {fraction ecpoly}) (p : point K):
       isfinite (eval g p)
    -> (eval (f + g) p) = (eval f p) \+ (eval g p).
  Proof. by rewrite addrC addC => /evalDl. Qed.

  Lemma eval_fracecX_fin n d x y:
       oncurve (|x, y|)
    -> 0 <= order (n%:E // d%:E) (|x, y|)
    -> eval (n%:E // d%:E) (|x, y|) = (n // d).[!x].
  Proof.
    pose i := fun (n d : {poly K}) => rlift (ecX E) (n // d).
    have ->: n%:E // d%:E = i n d by rewrite /i rliftE.
    rewrite {}/i; elim/fracredW: (n // d) => {n d} n d.
    move=> cop_n_d mon_d oncve; have nz_d := (monic_neq0 mon_d).
    rewrite rliftE /= => ord; have [->|nz_n] := eqVneq n 0.
      by rewrite !mul0r eval0 finterp0.
    have mu_le_nd: (\mu_x d <= \mu_x n)%N.
      move: ord; rewrite orderE ?ecX_eq0 // !poly_order_mu //.
      by rewrite subr_ge0 lez_nat leq_pmul2r.
    have nz_dx: d.[x] != 0.
    + apply/negP; rewrite -rootE=> root_dx; move: cop_n_d.
      rewrite coprimep_sym => /coprimep_root -/(_ _ root_dx).
      rewrite -rootE -mu_gt0 // -leqNgt => /(leq_trans mu_le_nd).
      by move: root_dx; rewrite -mu_gt0 // => mudx_gt0 /(leq_trans mudx_gt0).
    by rewrite evalE_fin_ord_ge0 ?ecX_eceval // finterp_nzden.
  Qed.

  Lemma uniok_order_decomp u p ecp o (f g : ecpoly):
    uniok u p ecp o f g -> order (f // g) ecp = 0.
  Proof.
    have [->|nz_f] := eqVneq f 0; first by rewrite mul0r order0.
    have [->|nz_g] := eqVneq g 0; first by rewrite invr0 mulr0 order0.
    have [|outcve] := (boolP (oncurve ecp)); last by rewrite order_outcve.
    case: ecp => [|x y] oncve /=.
    + move/uniok_inf_degeq=> eq; rewrite orderE //=.
      rewrite /poly_order (negbTE nz_f) (negbTE nz_g) /= eq.
      by rewrite subrr.
    + case/uniok_finP=> [_ nz_fxy nz_gzy].
      apply/eqP/eval_eq0_orderP => //.
        by rewrite mulf_neq0 // ?invr_eq0 tofrac_eq0.
      exists (f.[x, y] / g.[x, y]); first by rewrite mulf_neq0 ?invr_eq0.
      by rewrite evalE_fin_ord_ge0.
  Qed.
End ECEval.

(* -------------------------------------------------------------------- *)
Section ECPolyConstant.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Hypothesis closedK : GRing.ClosedField.axiom K.
  Import PreClosedField.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Local Notation "[ 'ecp' a *Y + b ]" := (ECPoly E (a, b)).
  Local Notation "[ 'ecp' a *Y - b ]" := (ECPoly E (a, -b)).
  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ecX E p).

  Local Notation clK := (ClosedFieldType K closedK).

  Local Notation sizep := (size : {poly _} -> _).

  Lemma all_order_eq0P (f : ecpoly): f != 0 ->
    (    (forall x y : K, order f%:F (|x, y|) = 0)
     <-> exists2 c : K, c != 0 & f = (c%:P)%:E).
  Proof.
    have size1M (p1 p2 : {poly K}): size (p1 * p2) = 1%N -> size p1 = 1%N.
      have [->|nz_p1] := eqVneq p1 0; first by rewrite mul0r size_poly0.
      have [->|nz_p2] := eqVneq p2 0; first by rewrite mulr0 size_poly0.
      rewrite size_mul //; move: nz_p1; rewrite -size_poly_eq0.
      case szp1E: (size p1) => [//|n] _; rewrite addSn /=.
      case: {szp1E} n => [//|n]; rewrite addSn; case.
      by move/eqP; rewrite addn_eq0 size_poly_eq0 (negbTE nz_p2) andbF.
    move=> nz_f; split; last first.
      by case=> c _ -> x y; rewrite orderC.
    case: f nz_f => [[p q]] nz_f h; set f := [ecp p *Y + q].
    have normp_nz : forall x, (normp f).[x] != 0.
      move=> x; set y := sqrt (ec.Xpoly E).[x].
      have oncve: oncurve (|x, y|).
        rewrite oncurve_root; apply/rootP; rewrite !hornerE.
        by rewrite -expr2 {}/y (@sqr_sqrt clK) subrr.
      rewrite (ecroot_normp _ (y := y)) ?oncurveN_fin //.
      by rewrite negb_or !order_poly_cmp0 ?oncurveN_fin // !h.
    have: exists2 c : K, (c != 0) & (normp f = c%:P).
      apply/size_poly1P/(closed_rootP closedK (normp f)).
      by case=> x; rewrite rootE (negbTE (normp_nz _)).
    rewrite /f /normp /dotp /=; case=> [c nz_c].
    have [->|nz_p] := eqVneq p 0; rewrite ?simpm.
      move/(congr1 sizep); rewrite size_polyC nz_c /=.
      move/size1M/eqP/size_poly1P => [x nz_x qE].
      by exists x => //; rewrite qE.
    have [->|nz_q] := eqVneq q 0; rewrite ?simpm.
      move/(congr1 sizep); rewrite mulrC size_polyC nz_c /=.
      by move/size1M; rewrite size_Xpoly.
    move/eqP; rewrite !(mulrN, mulNr) subr_eq eq_sym addrC => /eqP.
    move/(congr1 sizep); rewrite size_addl; last first.
      rewrite size_polyC nz_c !size_mul ?(mulf_neq0, XpolyN0) //=.
      by rewrite size_Xpoly addn4.
    rewrite size_mul ?(mulf_neq0, XpolyN0) // size_Xpoly addn4 /=.
    by rewrite -!expr2 => /(congr1 odd) /=; rewrite !odd_size_id_exp.
  Qed.
End ECPolyConstant.
