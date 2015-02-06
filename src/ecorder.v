(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype choice xseq.
Require Import fintype ssralg ssrfun ssrint ssrnum bigop.
Require Import generic_quotient fraction fracfield polyall.
Require Import ssrring polyfrac polydec ec ecpoly.

Import GRing.Theory.
Import Num.Theory.
Import fraction.FracField.
Import fracfield.FracField.
Import FracInterp.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Local Notation simp := Monoid.simpm.
Local Notation sizep := (size : {poly _} -> _).

Local Hint Extern 0 (is_true (Xpoly _ != 0)) => exact: XpolyN0.

(* -------------------------------------------------------------------- *)
Section Order.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Local Notation "[ 'ecp' a *Y + b ]" := (ECPoly E (a, b)).
  Local Notation "[ 'ecp' a *Y - b ]" := (ECPoly E (a, -b)).
  Local Notation "p %:E" := (ecX E p).

  Local Notation ecpoly  := (ecpoly E).
  Local Notation Xpoly   := (Xpoly E).
  Local Notation oncurve := (oncurve E).

  Local Notation "'Y" := [ecp 1 *Y + 0] (at level 2).

  Local Notation "p .[ x , y ]" := (eceval p x y) (at level 2, format "p .[ x ,  y ]").

  Lemma Xpoly_divp_factor_neq0: forall x, Xpoly %/ ('X - x%:P) != 0.
  Proof.
    move=> x; apply/negP=> /eqP /(congr1 sizep).
    rewrite size_poly0 size_divp -?size_poly_eq0;
      by rewrite ?size_Xpoly ?size_XsubC.
  Qed.

  Lemma Xpoly_factor_oc_spec: forall (x : K), oncurve (| x, 0 |) ->
    Xpoly = (Xpoly %/ ('X - x%:P)) * ('X - x%:P).
  Proof.
    move=> x; rewrite /oncurve expr2 !simp -horner_Xpoly eq_sym.
    by rewrite -rootE root_factor_theorem dvdp_eq => /eqP.
  Qed.

  Lemma Xpoly_root_mu:
    forall x, root Xpoly x -> \mu_x Xpoly = 1%N.
  Proof.
    move=> x; rewrite -mu_gt0 //; case HXmu: (\mu_x Xpoly) => [//|Xmu].
    case: Xmu HXmu => // Xmu HXmu _; move: (smooth E x).
    by rewrite HXmu.
  Qed.

  Definition mudiv x (p : {poly K}) :=
    let d := \mu_x p in
      (d, p %/ ('X - x%:P)^+d).

  Definition mudiv_join x (p q : {poly K}) :=
    let: dp := \mu_x p in
    let: dq := \mu_x q in
      let d :=
        if   (p == 0) || (q == 0)
        then maxn dp dq
        else minn dp dq
      in
        (d, (p %/ ('X - x%:P)^+d, q %/ ('X - x%:P)^+d)).

  (* -------------------------------------------------------------------- *)
  Definition unifun_fin (x y : K) : ecpoly :=
    if   y == 0
    then [ecp 1 *Y + 0          ]
    else [ecp 0 *Y + ('X - x%:P)].

  Definition unifun (P : point K) :=
    match P with
    | (| x, y |) => (unifun_fin x y)%:F
    | ∞          => 'X%:E // [ecp 1 *Y + 0]
    end.

  Lemma unifun_finE:
    forall x y, unifun (|x, y|) = (unifun_fin x y)%:F.
  Proof. by []. Qed.

  Lemma unifun_fin_specE: forall x, unifun_fin x 0 = [ecp 1 *Y + 0].
  Proof. by move=> x; rewrite /unifun_fin eqxx. Qed.

  Lemma unifun_fin_regE:
    forall x y, y != 0 -> unifun_fin x y = ('X - x%:P)%:E.
  Proof. by move=> x y nz_y; rewrite /unifun_fin (negbTE nz_y). Qed.

  Lemma unifun_specE: forall x, unifun (|x, 0|) = [ecp 1 *Y + 0]%:F.
  Proof. by move=> x; rewrite unifun_finE unifun_fin_specE. Qed.

  Lemma unifun_regE:
    forall x y, y != 0 -> unifun (|x, y|) = (('X - x%:P)%:E)%:F.
  Proof.
    by move=> x y nz_y; rewrite unifun_finE unifun_fin_regE.
  Qed.

  Lemma eceval_unifun_fin:
    forall x y, (unifun_fin x y).[x, y] = 0.
  Proof.
    move=> x y; have [->|nz_y] := eqVneq y 0.
    + by rewrite unifun_fin_specE ecY_eceval !simp.
    + by rewrite unifun_fin_regE // ecX_eceval hornerXsubC subrr.
  Qed.

  Lemma unifun_neq0: forall p, unifun p != 0.
  Proof.
    case=> [|x y]; last have [->|nz_y] := eqVneq y 0.
    + by rewrite divf_neq0 !tofrac_eq0 ec_eq0 eqxx polyX_eq0 ecY_neq0.
    + by rewrite unifun_specE tofrac_eq0 ecY_neq0.
    + by rewrite unifun_regE // tofrac_eq0 ec_eq0 polyXsubC_eq0 eqxx.
  Qed.

  Definition unifun_repr p :=
    match p with
    | ∞ => ('X%:E, 'Y)
    | (|x, y|) => (unifun_fin x y, 1)
    end.

  Lemma unifun_reprE:
    forall p, unifun p = (unifun_repr p).1 // (unifun_repr p).2.
  Proof. by case=> [|x y] //=; rewrite divr1. Qed.

  Lemma unifun_repr_nz_num:
    forall p, (unifun_repr p).1 != 0.
  Proof.
    move=> p; move: (unifun_neq0 p); rewrite (unifun_reprE p).
    by rewrite mulf_eq0 invr_eq0 !tofrac_eq0 negb_or=> /andP [].
  Qed.

  Lemma unifun_repr_nz_den:
    forall p, (unifun_repr p).2 != 0.
  Proof.
    move=> p; move: (unifun_neq0 p); rewrite (unifun_reprE p).
    by rewrite mulf_eq0 invr_eq0 !tofrac_eq0 negb_or=> /andP [].
  Qed.

  Local Notation "\- x" := (ECGroup.neg x).

  Lemma unifun_opp ecp: unifun (\- ecp) = unifun ecp.
  Proof.
    by case: ecp=> [|x y] //=; rewrite /unifun_fin oppr_eq0.
  Qed.

  Section UniOk.
    Variable u : {fraction ecpoly}.
    Variable f : {fraction ecpoly}.

    Definition uniok_fin (x y : K) o (n d : ecpoly) :=
      [&& f == u ^ o * (n // d), n.[x, y] != 0 & d.[x, y] != 0].

    Definition uniok_inf o (n d : ecpoly) :=
      [&& f == u ^ o * (n // d), n // d != 0 & (degree n == degree d)].

    Definition uniok (ecp : point K) o (n d : ecpoly) :=
      match ecp with
      | ∞          => uniok_inf o n d
      | (| x, y |) => uniok_fin x y o n d
      end.
  End UniOk.

  Lemma uniok_infP u p o n d:
    reflect
       [/\ p = u ^ o * (n // d), n // d != 0 & degree n = degree d]
       (uniok_inf u p o n d).
  Proof.
    apply: (iffP and3P).
    + by case=> /eqP -> -> /eqP ->.
    + by case=> -> -> ->; rewrite !eqxx.
  Qed.

  Lemma uniok_finP u p x y o n d:
    reflect
      [/\ p = u ^ o * (n // d), n.[x, y] != 0 & d.[x, y] != 0]
      (uniok_fin u p x y o n d).
  Proof.
    apply: (iffP and3P).
    + by case=> /eqP -> -> ->.
    + by case; do 3!move=> ->; rewrite !eqxx.
  Qed.

  Lemma uniok_fin_decomp u f x y o n d:
    uniok_fin u f x y o n d -> f = (u ^ o) * (n // d).
  Proof. by case/uniok_finP. Qed.

  Lemma uniok_fin_num_eval_neq0 u p x y o n d:
    uniok_fin u p x y o n d -> n.[x, y] != 0.
  Proof. by case/uniok_finP. Qed.

  Lemma uniok_fin_den_eval_neq0 u p x y o n d:
    uniok_fin u p x y o n d -> d.[x, y] != 0.
  Proof. by case/uniok_finP. Qed.

  Lemma uniok_fin_nz_num u p x y o n d:
    uniok_fin u p x y o n d -> n != 0.
  Proof.
    move/uniok_fin_num_eval_neq0 => Heval; apply/negP=> /eqP.
    by move=> z_n; rewrite z_n eceval0 eqxx in Heval.
  Qed.

  Lemma uniok_fin_nz_den u p x y o n d:
    uniok_fin u p x y o n d -> d != 0.
  Proof.
    move/uniok_fin_den_eval_neq0 => Heval; apply/negP=> /eqP.
    by move=> z_n; rewrite z_n eceval0 eqxx in Heval.
  Qed.

  Lemma uniok_inf_decomp u f o n d:
    uniok_inf u f o n d -> f = (u ^ o) * (n // d).
  Proof. by case/uniok_infP. Qed.

  Lemma uniok_inf_nz u p o n d:
    uniok_inf u p o n d -> n // d != 0.
  Proof. by case/uniok_infP. Qed.

  Lemma uniok_inf_nz_num u p o n d:
    uniok_inf u p o n d -> n != 0.
  Proof.
    rewrite /uniok_inf; case/and3P=> _.
    by rewrite mulf_eq0 invr_eq0 !tofrac_eq0; case/norP.
  Qed.

  Lemma uniok_inf_nz_den u p o n d:
    uniok_inf u p o n d -> d != 0.
  Proof.
    rewrite /uniok_inf; case/and3P=> _.
    by rewrite mulf_eq0 invr_eq0 !tofrac_eq0; case/norP.
  Qed.

  Lemma uniok_inf_degeq u f o n d:
    uniok_inf u f o n d -> degree n = degree d.
  Proof. by case/uniok_infP. Qed.

  Lemma uniok_decomp u f p o n d:
    uniok u f p o n d -> f = (u ^ o) * (n // d).
  Proof.
    case: p=> [|x y]; rewrite /uniok.
    by move/uniok_inf_decomp. by move/uniok_fin_decomp.
  Qed.

  Lemma uniok_nz_num u p ecp o n d:
    uniok u p ecp o n d -> n != 0.
  Proof.
    case: ecp=> [|x y] /=;
      by [apply uniok_inf_nz_num | apply uniok_fin_nz_num].
  Qed.

  Lemma uniok_nz_den u p ecp o n d:
    uniok u p ecp o n d -> d != 0.
  Proof.
    case: ecp=> [|x y] /=;
      by [apply uniok_inf_nz_den | apply uniok_fin_nz_den].
  Qed.

   Lemma uniok_nz:
     forall u f p o n d, u != 0 -> uniok u f p o n d -> f != 0.
   Proof.
     move=> u f p o n d nz_u D; rewrite (uniok_decomp D).
     rewrite !mulf_eq0 expfz_eq0 !invr_eq0 !tofrac_eq0.
     rewrite (negbTE nz_u) !simp /= negb_or.
     by rewrite (uniok_nz_num D) (uniok_nz_den D).
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition poly_ordreg (x y : K) (p : ecpoly) : nat * (ecpoly * ecpoly) :=
    let: (d, (pp1, pp2)) := mudiv_join x p.1 p.2 in
    let: p'              := [ecp pp1 *Y + pp2] in

      if p'.[x, y] == 0
      then
        let d' := \mu_x (normp p') in
        let g  := (normp p') %/ ('X - x%:P)^+d' in
          ((d + d')%N, ([ecp 0 *Y + g], (conjp p')))
      else
        (d, (p', 1)).

  Definition poly_ordspec (x : K) (p : ecpoly) : nat * (ecpoly * ecpoly) :=
    let: C         := Xpoly %/ ('X - x%:P) in
    let: (d1, p'1) := mudiv x p.1 in
    let: (d2, p'2) := mudiv x p.2 in

      if (p.2 != 0) && ((p.1 == 0) || (2*d2 < (2*d1).+1)%N) then
        let n1 := p'1 * (C^+d1) * (('X - x%:P)^+(d1-d2)) in
        let n2 := p'2 * (C^+d1) in

          ((2*d2)%N, ([ecp n1*Y + n2], (C^+(d1+d2))%:E))

      else
        let n1 := p'2 * (C^+(d2-1)) * (('X - x%:P)^+(d2-d1-1)) in
        let n2 := p'1 * (C^+d2) in

          ((2*d1+1)%N, ([ecp n1*Y + n2], (C^+(d1+d2))%:E)).

  Definition poly_orderfin (x y : K) (f : ecpoly) :=
    if y == 0 then poly_ordspec x f else poly_ordreg x y f.

  Definition poly_orderinf (p:ecpoly) : int * (ecpoly * ecpoly) :=
    let d := (degree p).-1 in
      (-d%:Z, ('X%:E^+d * p, [ecp 1 *Y + 0] ^+ d)).

  Definition poly_order (p : ecpoly) (ecp : point K) : int * (ecpoly * ecpoly) :=
    if   (p == 0) || ~~(oncurve ecp)
    then (0, (0, 1))
    else if   ecp is (| x, y |)
         then let: (n, (g, h)) := poly_orderfin x y p in (n%:Z, (g, h))
         else poly_orderinf p.

  Lemma poly_orderfin_specE:
    forall x f, poly_orderfin x 0 f = poly_ordspec x f.
  Proof. by move=> x f; rewrite /poly_orderfin eqxx. Qed.

  Lemma poly_orderfin_regE:
    forall x y f, y != 0 -> poly_orderfin x y f = poly_ordreg x y f.
  Proof.
    by move=> x y f nz_y; rewrite /poly_orderfin (negbTE nz_y).
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma poly_orderfin_num_eval_neq0:
    forall (p : ecpoly) (x y : K),
      p != 0 -> oncurve (| x, y |) ->
      let: (d, (g1, g2)) := poly_orderfin x y p in
        g1.[x, y] != 0.
  Proof.
    case=> [[p q]] x y; rewrite ec_neq0 /= => nz_ec.
    have [->|nz_y] := eqVneq y 0 => oncve.
    + rewrite poly_orderfin_specE /poly_ordspec.
      case z_p: (p == 0); case z_q: (q == 0) => /=.
      * by move: nz_ec; rewrite (eqP z_p) (eqP z_q) eqxx.
      * by rewrite /eceval /= (eqP z_p) mu0 !simp -rootE rootN_div_mu // ?(negbT z_q).
      * by rewrite /eceval /= (eqP z_q) mu0 !simp -rootE rootN_div_mu // ?(negbT z_p).
      pose C := Xpoly %/ ('X - x%:P).
      have C_exp_evalx_neq0 : forall d, (C^+d).[x] != 0.
      * move=> d; rewrite /C horner_exp expf_neq0 // -rootE -['X - _]expr1.
        move: oncve; rewrite expr2 !simp -horner_Xpoly eq_sym.
        by rewrite -rootE => /Xpoly_root_mu <-; rewrite rootN_div_mu.
      case le: (_ < _)%N => /=.
      * rewrite /eceval !simp /= hornerM mulf_neq0 //.
        by rewrite -rootE rootN_div_mu // ?(negbT z_q).
      * rewrite /eceval !simp /= hornerM mulf_neq0 //.
        by rewrite -rootE rootN_div_mu // ?(negbT z_p).
    + rewrite poly_orderfin_regE // /poly_ordreg /mudiv_join /=.
      case mu0: (_ || _) => /=.
      * case z_ec: (_ == 0); last by rewrite z_ec.
        absurd false=> //; move: z_ec; rewrite /eceval /=.
        case/orP: mu0 => [/eqP z_p|/eqP z_q]; rewrite ?z_p ?z_q /= div0p.
        - rewrite horner0 !simp mu0 max0n -rootE (negbTE (rootN_div_mu _ _)) //.
          by rewrite z_p eqxx in nz_ec.
        - rewrite horner0 !simp mulf_eq0 (negbTE nz_y) orbF.
          rewrite mu0 maxn0 -rootE (negbTE (rootN_div_mu _ _)) //.
          by rewrite z_q eqxx orbF in nz_ec.
      case z_ec: (_ == 0); last by rewrite z_ec.
      rewrite ecX_eceval -rootE (negbTE (rootN_div_mu _ _)) //.
      rewrite norm_eq0 ec_neq0 /= divp_factor_mu_neq0 ?geq_minl //=.
      by case/norP: mu0.
  Qed.

  Lemma poly_orderfin_den_eval_neq0:
    forall (p:ecpoly) (x y : K),
      p != 0 -> oncurve (| x , y |) ->
      let: (d, (g1, g2)) := poly_orderfin x y p in
        g2.[x, y] != 0.
  Proof.
    move=> [[p q]] x y; rewrite ec_neq0 /= => nz_ec.
    have [->|nz_y] := eqVneq y 0 => oncve.
    + pose C := Xpoly %/ ('X - x%:P).
      have C_exp_evalx_neq0 : forall d, (C^+d).[x] != 0.
      * move=> d; rewrite /C horner_exp expf_neq0 // -rootE -['X - _]expr1.
        move: oncve; rewrite expr2 !simp -horner_Xpoly eq_sym.
        by rewrite -rootE => /Xpoly_root_mu <-; rewrite rootN_div_mu.
      rewrite poly_orderfin_specE /poly_ordspec /=.
      case z_p: (p == 0); case z_q: (q == 0) => /=.
      * by move: nz_ec; rewrite z_p z_q.
      * by rewrite ecX_eceval.
      * by rewrite ecX_eceval.
      by case: (_ < _)%N; rewrite ecX_eceval.
    + rewrite poly_orderfin_regE // /poly_ordreg.
      rewrite /mudiv_join /=; case mu0: (_ || _).
      * case z_ec: (_ == 0); last by rewrite eceval1 oner_neq0.
        absurd false=> //; move: z_ec; rewrite /eceval /=.
        case/orP: mu0 => [/eqP z_p|/eqP z_q]; rewrite ?z_p ?z_q /= div0p.
        - rewrite horner0 !simp mu0 max0n -rootE (negbTE (rootN_div_mu _ _)) //.
          by rewrite z_p eqxx in nz_ec.
        - rewrite horner0 !simp mulf_eq0 (negbTE nz_y) orbF.
          rewrite mu0 maxn0 -rootE (negbTE (rootN_div_mu _ _)) //.
          by rewrite z_q eqxx orbF in nz_ec.
      case/norP: mu0 => {nz_ec} nz_p nz_q.
      case z_ec: (_ == 0); last by rewrite eceval1 oner_neq0.
      move: (eqP z_ec); rewrite /conjp /eceval /= !hornerE => <-.
      case: (leqP (\mu_x p) (\mu_x q)) => mucmp.
      + rewrite (minn_idPl _) //; apply/negP=> /eqP /addIr /(mulIf nz_y) /esym.
        by move/ecu_eq_oppr=> /eqP; rewrite -rootE (negbTE (rootN_div_mu _ _)).
      + absurd false=> //; move: z_ec; rewrite (minn_idPr _); last by apply: ltnW.
        have mucmpW := (ltnW mucmp); set p' := (p %/ _).
        have z_p'x: p'.[x] == 0.
        * rewrite /p' -rootE -mu_gt0 ?divp_factor_mu_neq0 //.
          by rewrite mu_div // subn_gt0.
        rewrite /eceval /= (eqP z_p'x) !simp.
        by rewrite -rootE (negbTE (rootN_div_mu _ _)).
  Qed.

  Lemma poly_orderfin_decomp:
    forall (p : ecpoly) (x y : K),
      p != 0 -> oncurve (| x, y |) ->
      let: (d, (g1, g2)) := poly_orderfin x y p in
      let: u := unifun (| x, y |) in
        p%:F = (u^+d) * (g1 // g2).
  Proof.
    move=> [[p q]] x y nz_pq; have [->|nz_y] := eqVneq y 0 => on_cve.
    + rewrite poly_orderfin_specE /poly_ordspec /= unifun_fin_specE.
      case b: (_ && _).
      * rewrite mul2n -tofracX ecY_exp_double expr1n mul1r.
        rewrite exprD ecXM mulrAC.
        rewrite -ec_scaler frac_mull; last first.
        + by rewrite ecX_eq0 expf_neq0 // Xpoly_divp_factor_neq0.
        rewrite {1}(Xpoly_factor_oc_spec on_cve).
        rewrite [X in X ^+ _]mulrC exprMn ecXM tofracM -mulrA.
        rewrite [X in _ = (_ * X)]mulrCA divff ?mulr1; last first.
        + by rewrite tofrac_eq0 ecX_eq0 expf_neq0 // Xpoly_divp_factor_neq0.
        rewrite -tofracM ec_scaler mu_divp_mul.
        case/andP: b => nz_q /orP [/eqP z_p|mule].
        + by rewrite z_p div0p !simp.
        rewrite -mulrA -exprD subnK ?mu_divp_mul //.
        + by rewrite -leq_double -!mul2n -ltnS.
      * rewrite addn1 mul2n -tofracX exprS ecY_exp_double expr1n mul1r.
        rewrite {1}(Xpoly_factor_oc_spec on_cve).
        set C := ('X - x%:P); set XC := (Xpoly %/ C).
        rewrite [X in X ^+ _]mulrC exprMn !ecXM.
        rewrite !tofracM -!mulrA [X in _ = _ * (_ * X)]mulrA.
        rewrite exprD ecXM tofracM divf_mull; last first.
        + by rewrite tofrac_eq0 ecX_eq0 expf_neq0 // Xpoly_divp_factor_neq0.
        rewrite [X in _ = _ * X]mulrA -tofracM.
        rewrite ec_scaler -2!mulrA -exprD.
        rewrite [(p %/ _ * _) * _]mulrAC mu_divp_mul.
        case z_q: (q == 0) b => /=.
        + move=> _; rewrite (eqP z_q) mu0 div0p !sub0n !expr0.
          rewrite [_ 0 _]mul0r mulr1 divr1 -tofracM.
          by rewrite ecY_ecX_mul mul1r.
        case/norP; rewrite -leqNgt ltn_pmul2l // => nz_p.
        case z_muxq: (\mu_x q) => [//|muxq] le.
        rewrite !subn1 subSKn /= subnK //.
        rewrite mulrA -tofracM mulE /dotp /= !simp /=.
        set r := (X in _ = ([ecp _ *Y + X] // _)).
        have ->: r = q * XC ^+ muxq.+1.
        + rewrite /r {r} (Xpoly_factor_oc_spec on_cve) -/C -/XC.
          rewrite mulrCA -!mulrA [_^+_ * ('X - _)]mulrC -exprS.
          rewrite mulrCA [Xpoly %/ _ * _]mulrA -exprS mulrA.
          by rewrite mulrAC -z_muxq mu_divp_mul.
        rewrite -ec_scaler tofracM mulrAC divff ?mul1r //.
        by rewrite tofrac_eq0 ecX_eq0 expf_neq0 // Xpoly_divp_factor_neq0.
    + rewrite poly_orderfin_regE // /poly_ordreg /= /mudiv_join /=.
      have [z_p|nz_p] := eqVneq p 0.
      * rewrite z_p eqxx /= div0p ecX_eceval mu0 max0n.
        rewrite -rootE (negbTE (rootN_div_mu _ _)).
        - rewrite mulrC -tofracX divr1 -tofracM.
          by rewrite unifun_fin_regE // -ecXX -ecXM mu_divp_mul.
        - by move: nz_pq; rewrite ec_neq0 /= z_p eqxx.
      have [z_q|nz_q] := eqVneq q 0.
      * rewrite z_q eqxx orbT /= div0p ecY_eceval mu0 maxn0 mulf_eq0.
        rewrite (negbTE nz_y) /= -rootE (negbTE (rootN_div_mu _ _)).
        - rewrite mulrC -tofracX divr1 -tofracM.
          rewrite unifun_fin_regE // -ecXX mulE /dotp /=.
          by rewrite !simp mu_divp_mul.
        - by move: nz_pq; rewrite ec_neq0 /= z_q eqxx.
      rewrite (negbTE nz_p) (negbTE nz_q) /=; case z_eval : (_ == 0).
      * rewrite unifun_fin_regE // /= exprD -!tofracX -!ecXX.
        rewrite -mulrA [X in _ = _ * X]mulrA -tofracM.
        rewrite -ecXM [X in (X%:E // (conjp _))]mulrC mu_divp_mul.
        rewrite -[(normp _)%:E]conjp_normp [_ * conjp _]mulrC tofracM.
        rewrite mulrAC divff ?mul1r; last first.
        - rewrite tofrac_eq0 eqE /= eqE /= oppr_eq0; apply/nandP; left.
          by rewrite divp_factor_mu_neq0 // geq_minl.
        rewrite -tofracM ec_scaler;
          by rewrite !le_mu_divp_mul // (geq_minr, geq_minl).
      * rewrite unifun_fin_regE // -tofracX -ecXX mulrA.
        rewrite divr1 -tofracM ec_scaler.
        by rewrite !le_mu_divp_mul // (geq_minr, geq_minl).
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma poly_orderinf_eq_degree:
    forall (p : ecpoly), p != 0 ->
      let: (o, (g1, g2)) := poly_orderinf p in
        degree g1 = degree g2.
  Proof.
    move=> p nz_p /=; rewrite degree_mul_id ?mulf_neq0 //; last first.
    + by rewrite expf_neq0 // ecX_neq0.
    rewrite degree_expX degree_expY addSn /= [(3 * _)%N]mulSn.
    by rewrite -addSn prednK 1?addnC // lt0n degree_eq0.
  Qed.

  Lemma poly_orderinf_nz:
    forall (p : ecpoly), p != 0 ->
      let: (o, (g1, g2)) := poly_orderinf p in
        g1 // g2 != 0.
  Proof.
    move=> p nz_p /=; rewrite mulf_neq0 // ?invr_eq0 tofrac_eq0.
    + rewrite mulf_eq0 (negbTE nz_p) orbF /= expf_neq0 //.
      by rewrite ecX_eq0 polyX_eq0.
    + by rewrite expf_neq0 // ec_eq0 /= eqxx andbT oner_neq0.
  Qed.

  Lemma poly_orderinf_decomp:
    forall (p : ecpoly), p != 0 ->
      let: (o, (g1, g2)) := poly_orderinf p in
      let: u := unifun  ∞ in
        p%:F = (u ^ o) * (g1 // g2).
  Proof.
    move=> p nz_p /=; rewrite -invr_expz tofracM [_ * _ / _]mulrAC.
    rewrite !tofracX -divf_exp mulrCA mulrA divff ?mul1r //.
    by rewrite expf_neq0 // divf_neq0 !tofrac_eq0 ecY_neq0 ecX_neq0.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma poly_orderfin_correct:
    forall (p : ecpoly) x y, p != 0 -> oncurve (| x, y |) ->
      let: (o, (g1, g2)) := poly_orderfin x y p in
        uniok_fin (unifun (|x, y|)) p%:F x y o g1 g2.
  Proof.
    move=> p x y nz_p oncv; case Epo: (poly_orderfin _ _ _) => [o [g1 g2]].
    apply/and3P; split.
    + by move: (poly_orderfin_decomp nz_p oncv); rewrite Epo => ->.
    + by move: (poly_orderfin_num_eval_neq0 nz_p oncv); rewrite Epo; apply.
    + by move: (poly_orderfin_den_eval_neq0 nz_p oncv); rewrite Epo; apply.
  Qed.

  Lemma poly_orderinf_correct:
    forall (p : ecpoly), p != 0 ->
      let: (o, (g1, g2)) := poly_orderinf p in
        uniok_inf (unifun ∞) p%:F o g1 g2.
  Proof.
    move=> p nz_p; case Epo: (poly_orderinf _) => [o [g1 g2]]; apply/and3P; split.
    + by move: (poly_orderinf_decomp nz_p); rewrite Epo=> ->.
    + by move: (poly_orderinf_nz nz_p); rewrite Epo=> ->.
    + by move: (poly_orderinf_eq_degree nz_p); rewrite Epo=> ->.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma poly_order_correct:
    forall (p : ecpoly) (ecp : point K), p != 0 -> oncurve ecp ->
      let: (o, (g1, g2)) := poly_order p ecp in
        uniok (unifun ecp) p%:F ecp o g1 g2.
  Proof.
    move=> p [|x y] nz_p oncve /=;
      rewrite /poly_order (negbTE nz_p) oncve /=.
    + by move: (poly_orderinf_correct nz_p) => /=.
    + case Hpo: (poly_orderfin _ _ _) => [n [g h]].
      by move: (poly_orderfin_correct nz_p oncve); rewrite Hpo.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_mul u p1 p2 ecp o1 o2 f1 f2 g1 g2:
         u != 0 -> oncurve ecp
      -> uniok u p1 ecp o1 f1 g1
      -> uniok u p2 ecp o2 f2 g2
      -> uniok u (p1 * p2) ecp (o1 + o2) (f1 * f2) (g1 * g2).
  Proof.
    move=> nz_u oncve H1 H2;
      set r1 : ecpoly := (f1 * f2);
      set r2 : ecpoly := (g1 * g2).
    have Hdcp: (p1 * p2) = u ^ (o1 + o2) * (r1 // r2).
    + move/uniok_decomp: H1=> ->; move/uniok_decomp: H2 ->.
      have ->: (f1 * f2 // g1 * g2) = (f1 // g1) * (f2 // g2).
      * by rewrite !tofracM invfM mulf_cross.
      rewrite expfzDr; last by exact: nz_u.
      by rewrite mulf_cross.
    case: ecp oncve H1 H2=> [|x y] oncve /=.
    + move=> H1 H2; rewrite /uniok_inf; apply/and3P; split.
      * by rewrite Hdcp eqxx.
      * rewrite !tofracM invfM mulf_cross mulf_eq0.
        by rewrite (negbTE (uniok_inf_nz H1)) (negbTE (uniok_inf_nz H2)).
      * move: (uniok_inf_nz_num H1) => nz_f1.
        move: (uniok_inf_nz_den H1) => nz_g1.
        move: (uniok_inf_nz_num H2) => nz_f2.
        move: (uniok_inf_nz_den H2) => nz_g2.
        rewrite !degree_mul_id ?mulf_neq0 //.
        by rewrite (uniok_inf_degeq H1) (uniok_inf_degeq H2).
    + rewrite /uniok_fin=> /and3P [D1 Hf1 Hg1] /and3P [D2 Hf2 Hg2].
      by rewrite Hdcp eqxx !eceval_mul // !mulf_neq0.
  Qed.

  Lemma uniok_fin_mul u p1 p2 x y o1 o2 f1 f2 g1 g2:
         u != 0 -> oncurve (| x, y |)
      -> uniok_fin u p1 x y o1 f1 g1
      -> uniok_fin u p2 x y o2 f2 g2
      -> uniok_fin u (p1 * p2) x y (o1 + o2) (f1 * f2) (g1 * g2).
  Proof.
    move=> nz_u oncve H1 H2.
    move: (@uniok_mul u p1 p2 (|x, y|) o1 o2 f1 f2 g1 g2).
    by rewrite /uniok [uniok_fin]lock; apply; unlock.
  Qed.

  Lemma uniok_inf_mul u p1 p2 o1 o2 f1 f2 g1 g2:
         u != 0
      -> uniok_inf u p1 o1 f1 g1
      -> uniok_inf u p2 o2 f2 g2
      -> uniok_inf u (p1 * p2) (o1 + o2) (f1 * f2) (g1 * g2).
  Proof.
    move=> nz_u H1 H2.
    move: (@uniok_mul u p1 p2 ∞ o1 o2 f1 f2 g1 g2).
    by rewrite /uniok [uniok_inf]lock; apply; unlock.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_inv u f p o n d:
         u != 0 -> oncurve p
      -> uniok u f p o n d
      -> uniok u f^-1 p (-o) d n.
  Proof.
    move=> nz_u oncve H; have Hdcp: f^-1 = u ^ (-o) * (d // n).
    + by move/uniok_decomp: H=> ->; rewrite invfM invr_expz invfE.
    case: p H oncve=> [|x y] /= H oncve.
    + rewrite /uniok_inf; apply/and3P; split; first by rewrite Hdcp eqxx.
      * rewrite mulf_eq0 invr_eq0 !tofrac_eq0 negb_or.
        by rewrite (uniok_inf_nz_num H) (uniok_inf_nz_den H).
      * by rewrite (uniok_inf_degeq H) eqxx.
    + rewrite /uniok_fin; apply/and3P; split; first by rewrite Hdcp.
      * by rewrite (uniok_fin_den_eval_neq0 H).
      * by rewrite (uniok_fin_num_eval_neq0 H).
  Qed.

  Lemma uniok_fin_inv u p x y o f g:
         u != 0 -> oncurve (|x, y|)
      -> uniok_fin u p x y o f g
      -> uniok_fin u p^-1 x y (-o) g f.
  Proof.
    move=> nz_u oncve H; move: (@uniok_inv u p (|x, y|) o f g).
    by rewrite /uniok [uniok_fin]lock; apply; unlock.
  Qed.

  Lemma uniok_inf_inv u p o f g:
         u != 0
      -> uniok_inf u p o f g
      -> uniok_inf u p^-1 (-o) g f.
  Proof.
    move=> nz_u H; move: (@uniok_inv u p ∞ o f g).
    by rewrite /uniok [uniok_inf]lock; apply; unlock.
  Qed.

  (* -------------------------------------------------------------------- *)
  Notation "x %:FP" := (((x%:P)%:E)%:F) (at level 2, format "x %:FP").

  Lemma degree1 : degree (1 : ecpoly) = 1%N. (* XXX: MOVE *)
  Proof. by rewrite degree_pX size_poly1. Qed.

  Lemma uniokC:
    forall u c p,
      u != 0 -> c != 0 -> uniok u c%:FP p 0 (c%:P)%:E 1.
  Proof.
    move=> u c p nz_u nz_c.
    + have Hdcp: c%:FP = u ^ 0 * ((c%:P)%:E // 1).
      by rewrite expr0z mul1r divr1.
    case: p=> [|x y] /=.
    + apply/uniok_infP; split.
      * by rewrite {1}Hdcp.
      * by rewrite divr1 tofrac_eq0 ecX_eq0 polyC_eq0.
      * by rewrite degree1 degree_pX size_polyC nz_c.
    + apply/uniok_finP; split.
      * by rewrite {1}Hdcp.
      * by rewrite ecX_eceval hornerC.
      * by rewrite eceval1 oner_neq0.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_opp u f p o n d:
         u != 0 -> oncurve p
      -> uniok u f p o n d
      -> uniok u (-f) p o (-n) d.
  Proof.
    move=> nz_u oncve H1; have H2: uniok u (-1) p 0 (-1) 1.
    + move: (@uniokC _ (-1) p nz_u); rewrite oppr_eq0 oner_neq0.
      by rewrite !(polyC_opp, ecXN, tofracN); apply.
    by move: (uniok_mul nz_u oncve H1 H2); rewrite !mulrN !mulr1 addr0.
  Qed.

  Lemma uniok_fin_opp u p x y o f g:
         u != 0 -> oncurve (|x, y|)
      -> uniok_fin u p x y o f g
      -> uniok_fin u (-p) x y o (-f) g.
  Proof.
    move=> nz_u oncve H; move: (@uniok_opp u p (|x, y|) o f g).
    by rewrite /uniok [uniok_fin]lock; apply; unlock.
  Qed.

  Lemma uniok_inf_opp u p o f g:
         u != 0
      -> uniok_inf u p o f g
      -> uniok_inf u (-p) o (-f) g.
  Proof.
    move=> nz_u H; move: (@uniok_opp u p ∞ o f g).
    by rewrite /uniok [uniok_inf]lock; apply; unlock.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_exp u p ecp o (f g : {ecpoly E}) n:
       u != 0
    -> oncurve ecp
    -> uniok u p ecp o f g
    -> uniok u (p^+n) ecp (o *+ n) (f^+n) (g^+n).
  Proof.
    move=> nz_u oncve; elim: n => [|n IH].
    + by move=> _; rewrite !expr0 mulr0n uniokC ?oner_eq0.
    + by move=> uok; rewrite !exprS mulrS uniok_mul // IH.
  Qed.

  Lemma uniok_expz u p ecp o (f g : {ecpoly E}) z:
    let f' := if z < 0 then g else f in
    let g' := if z < 0 then f else g in

       u != 0
    -> oncurve ecp
    -> uniok u p ecp o f g
    -> uniok u (p^z) ecp (o *~ z) (f'^+(absz z)) (g'^+(absz z)).
  Proof.
    move=> /= nz_u oncve; case: z => [n|n] /=.
    + by apply: uniok_exp.
    + by move=> uok; rewrite uniok_inv // uniok_exp.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_uniq:
    forall p ecp, p != 0 -> oncurve ecp ->
      forall o1 o2 n1 n2 d1 d2,
           uniok (unifun ecp) p ecp o1 n1 d1
        -> uniok (unifun ecp) p ecp o2 n2 d2
        -> (o1 == o2) && (n1 // d1 == n2 // d2).
  Proof.
    move=> p ecp nz_p cve o1 o2; wlog cmp_o: o1 o2 / (o2 <= o1).
    + move=> Hsym; case: (lerP o2 o1); first by move=> *; apply Hsym.
      move=> /ltrW cmp n1 n2 d1 d2 Hu1 Hu2.
      by rewrite [o1 == _]eq_sym [n1 // _ == _]eq_sym; apply Hsym.
    move=> n1 n2 d1 d2 H1 H2.
    have nz_n1 := uniok_nz_num H1; have nz_n2 := uniok_nz_num H2.
    have nz_d1 := uniok_nz_den H1; have nz_d2 := uniok_nz_den H2.
    set nz := (ecY_neq0, ecX_neq0, nz_n1, nz_n2, nz_d1, nz_d2).
    move: (uniok_decomp H1); move: (uniok_decomp H2)=> ->.
    rewrite unifun_reprE; set nu := _.1; set du := _.2.
    have nz_du : du != 0 by apply (unifun_repr_nz_den ecp).
    have nz_nu : nu != 0 by apply (unifun_repr_nz_num ecp).
    have nz_u : nu // du != 0.
    + by rewrite /nu /du -unifun_reprE unifun_neq0.
    rewrite -[o1]add0r -[0](subrr o2) -addrA expfzDr // -mulrA.
    move/(mulfI (expfz_neq0 o2 nz_u)); rewrite addrC.
    move: cmp_o; rewrite -subr_ge0; case En: (o1 - o2)=> [n|//].
    rewrite ler_eqVlt; case/orP => [/eqP <-|].
    + by rewrite expr0z mul1r addr0 => ->; rewrite !eqxx.
    move=> ge0_n; rewrite -exprnP divf_exp -!tofracX=> /eqP.
    rewrite mulf_cross -invfM -!tofracM [_ // d2 == _]frac_eq; last first.
    + by rewrite !(mulf_neq0, expf_neq0) // ?(uniok_nz_den H2, uniok_nz_den H1).
    rewrite /nu /du => {nu du nz_du nz_nu nz_u}.
    case: ecp cve H1 H2 => [|x y] /= cve H1 H2.
    + move/eqP; move/(congr1 (@degree _ _)).
      rewrite !degree_mul_id ?(mulf_neq0, expf_neq0, nz) //.
      rewrite (uniok_inf_degeq H1) (uniok_inf_degeq H2) degree_expX degree_expY.
      rewrite !addSn /= [(degree _ + _)%N]addnC -![((_ + _) + (degree _))%N]addnA.
      case Hd: (degree d1 + degree d2)%N => [|dd] /=.
      * by move/eqP: Hd; rewrite addn_eq0 degree_eq0 (negbTE nz_d1).
      by rewrite !addnS /= => /addIn /eqP; rewrite eqn_pmul2r // -ltz_nat.
    + move/eqP=> /(congr1 (fun p => eceval p x y)).
      rewrite !eceval_mul // !eceval_exp // eceval_unifun_fin.
      have -> : 0 ^+ n = 0 :> K.
      * by apply/eqP; rewrite expf_eq0 eqxx -ltz_nat ge0_n.
      move/eqP; rewrite eceval1 expr1n mul1r !mul0r !mulf_eq0.
      rewrite (negbTE (uniok_fin_den_eval_neq0 H1)).
      by rewrite (negbTE (uniok_fin_num_eval_neq0 H2)).
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma poly_order_orderE:
    forall p ecp o n d,
         oncurve ecp
      -> uniok (unifun ecp) p%:F ecp o n d
      -> o = (poly_order p ecp).1.
  Proof.
    move=> p ecp o n d oncve D.
    move: (uniok_nz (unifun_neq0 ecp) D) => nz_fp.
    have nz_p: p != 0 by rewrite tofrac_eq0 in nz_fp.
    move: (poly_order_correct nz_p oncve).
    case: (poly_order p ecp) => [o' [n' d']] /= D'.
    by move: (uniok_uniq nz_fp oncve D D')=> /andP [/eqP ->].
  Qed.

  Lemma poly_order_outcve p ecp:
    ~~(oncurve ecp) -> poly_order p ecp = (0, (0, 1)).
  Proof.
    by move=> outcve; rewrite /poly_order outcve orbT.
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition orderf (f : {ratio ecpoly}) p : int :=
    if   \n_f == 0
    then 0
    else
      (poly_order \n_f p).1 - (poly_order \d_f p).1.

  Definition order f p :=
    (lift_fun1 {fraction ecpoly} (orderf^~ p)) f.

  Local Open Scope quotient_scope.

  Lemma pi_order p:
    {mono \pi_{fraction ecpoly} : f / orderf f p >-> order f p}.
  Proof.
    move=> f2; unlock order; set f1 := (repr _).
    have: (f1 = f2 %[mod {fraction _}]) by rewrite reprK.
    case: f2 f1 => [[n2 d2] /= nz_d2] [[n1 d1] /= nz_d1] /=.
    move/eqmodP => /=; rewrite FracField.equivfE /=.
    have [->|nz_n1] := eqVneq n1 0 => [|H].
      rewrite mul0r eq_sym mulf_eq0 (negbTE nz_d1) /= => /eqP ->.
      by rewrite /orderf /= /poly_order eqxx.
    have nz_n2: n2 != 0. move: (mulf_neq0 nz_n1 nz_d2).
      by rewrite (eqP H) mulf_eq0 negb_or => /andP [].
    rewrite /orderf /= (negbTE nz_n1) (negbTE nz_n2) /=.
    case ncve: (oncurve p); last by rewrite !poly_order_outcve ?ncve.
    case Hn1: (poly_order n1 p) => [on1 [fn1 gn1]].
    case Hd1: (poly_order d1 p) => [od1 [fd1 gd1]].
    case Hn2: (poly_order n2 p) => [on2 [fn2 gn2]].
    case Hd2: (poly_order d2 p) => [od2 [fd2 gd2]].
    move: (@poly_order_correct n1 p nz_n1 ncve); rewrite Hn1 => Dn1.
    move: (@poly_order_correct n2 p nz_n2 ncve); rewrite Hn2 => Dn2.
    move: (@poly_order_correct d1 p nz_d1 ncve); rewrite Hd1 => Dd1.
    move: (@poly_order_correct d2 p nz_d2 ncve); rewrite Hd2 => Dd2.
    rewrite -![(_ : ecpoly) == 0]tofrac_eq0 in nz_n1, nz_n2, nz_d1, nz_d2.
    move: (uniok_mul (unifun_neq0 p) ncve Dn1 Dd2); rewrite -tofracM => DL.
    move: (uniok_mul (unifun_neq0 p) ncve Dd1 Dn2); rewrite -tofracM => DR.
    rewrite (eqP H) in DL.
    have nz_d1n2: (d1 * n2)%:F != 0.
    + rewrite tofracM mulf_neq0; first 1 [done] || idtac.
      by rewrite nz_d1. by rewrite nz_n2.
    move: (uniok_uniq nz_d1n2 ncve DL DR) => /andP [/eqP Hpo _].
    by apply/eqP; rewrite addr_cross Hpo addrC.
  Qed.

  Canonical order_morph p := PiMono1 (pi_order p).

  Lemma order_correct (n d : ecpoly) ecp o1 o2 n1 n2 d1 d2:
         oncurve ecp
      -> uniok (unifun ecp) n%:F ecp o1 n1 d1
      -> uniok (unifun ecp) d%:F ecp o2 n2 d2
      -> [&& order (n // d) ecp == o1 - o2
           & uniok (unifun ecp) (n // d) ecp (o1 - o2) (n1 * d2) (n2 * d1)].
  Proof.
    move=> oncve D1 D2; have nz_u: (unifun ecp != 0) by exact: unifun_neq0.
    move: (uniok_mul nz_u oncve D1 (uniok_inv nz_u oncve D2)) => D.
    rewrite [n2 * d1]mulrC D !simp.
    move: (uniok_nz nz_u D1); rewrite tofrac_eq0 => nz_n.
    move: (uniok_nz nz_u D2); rewrite tofrac_eq0 => nz_d.
    rewrite !piE /orderf !numden_Ratio // (negbTE nz_n) /=.
    by rewrite -(poly_order_orderE oncve D1) -(poly_order_orderE oncve D2).
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition decomp (f : {fraction ecpoly}) (ecp : point K) : (ecpoly * ecpoly) :=
    let f := repr f in
      if   (\n_f == 0) || ~~(oncurve ecp)
      then (0, 1)
      else
        let: (n1, d1) := (poly_order \n_f ecp).2 in
        let: (n2, d2) := (poly_order \d_f ecp).2 in
          (n1 * d2, n2 * d1).

  Lemma decomp_correct (f : {fraction ecpoly}) ecp:
       f != 0 -> oncurve ecp
    -> uniok (unifun ecp) f ecp (order f ecp) (decomp f ecp).1 (decomp f ecp).2.
  Proof.
    elim/fracW: f => n d nz_d; rewrite divf_neq0 !tofrac_eq0.
    rewrite (negbTE nz_d) !simp => nz_n oncve; rewrite /decomp oncve !simp.
    move: (FracField.equivf_r (Ratio n d));
      rewrite -embed_Ratio !numden_Ratio // => Hr.
    set r := (repr (n // d)); have nz_n' : \n_r != 0.
    + apply/negP=> /eqP z_n'; move: Hr; rewrite /r z_n' => /eqP.
      rewrite mulr0 mulf_eq0 (negbTE nz_n) /=.
      by case: (repr (n // d))=> [[n' d'] /=] => /negbTE ->.
    rewrite (negbTE nz_n'); have nz_d' : \d_r != 0 by apply denom_ratioP.
    move/(congr1 (@FracField.tofrac _)): Hr => /eqP; rewrite !tofracM.
    rewrite [d%:F * _]mulrC -divff_eq ?(mulf_neq0, tofrac_eq0) // => /eqP Hr.
    move: (poly_order_correct nz_d' oncve).
    move: (poly_order_correct nz_n' oncve).
    case: (poly_order \n_r ecp) => [o1 [n1 d1]] => D1 /=.
    case: (poly_order \d_r ecp) => [o2 [n2 d2]] => D2 /=.
    by case/andP: (order_correct oncve D1 D2); rewrite -!Hr => /eqP ->.
  Qed.

  Lemma decomp_fin_correct f x y:
       f != 0 -> oncurve (|x, y|)
    -> uniok_fin
         (unifun (|x, y|)) f x y (order f (|x, y|))
         (decomp f (|x, y|)).1
         (decomp f (|x, y|)).2.
  Proof.
    move=> nz_f oncve /=; move: (decomp_correct nz_f oncve).
    by rewrite /uniok [uniok_fin]lock.
  Qed.

  Lemma decomp0 p: decomp 0 p = (0, 1).
  Proof.
    rewrite /decomp FracField.numer0 reprK piE /=.
    rewrite FracField.equivfE /= !numden_Ratio ?oner_eq0 //.
    by rewrite !(mulr0, mul0r) eqxx.
  Qed.

  Lemma decomp_outcve f p: ~~(oncurve p) -> decomp f p = (0, 1).
  Proof. by move=> outcve; rewrite /decomp outcve orbT. Qed.

  Lemma decomp_nz_num f p:
    f != 0 -> oncurve p -> (decomp f p).1 != 0.
  Proof.
    move=> nz_f oncve; move: (decomp_correct nz_f oncve).
    by move/uniok_nz_num.
  Qed.

  Lemma decomp_nz_den f p:
    f != 0 -> oncurve p -> (decomp f p).2 != 0.
  Proof.
    move=> nz_f oncve; move: (decomp_correct nz_f oncve).
    by move/uniok_nz_den.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma order0 ecp: order 0 ecp = 0.
  Proof.
    by rewrite piE /orderf numden_Ratio ?oner_neq0 // eqxx.
  Qed.

  Lemma order_outcve f ecp: ~~(oncurve ecp) -> order f ecp = 0.
  Proof.
    move=> Noncve; elim/quotW: f=> [[[n d] /= nz_d]].
    rewrite piE /orderf /=; case: (_ == 0)=> //.
    by rewrite !poly_order_outcve ?Noncve.
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition uniformizer u ecp := order u ecp == 1.

  Lemma uniformizer_neq0 u ecp: uniformizer u ecp -> u != 0.
  Proof.
    by have [->|nz_u] := eqVneq u 0 => //; rewrite /uniformizer order0.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniformizer_unifun ecp: oncurve ecp -> uniformizer (unifun ecp) ecp.
  Proof.
    have D1: uniok (unifun ecp) (unifun ecp) ecp 1 1 1.
    + case: ecp=> [|x y]; [apply/uniok_infP | apply/uniok_finP]; split.
      * by rewrite expr1z divr1 mulr1.
      * by rewrite divr1 oner_neq0.
      * by rewrite degree1.
      * by rewrite expr1z divr1 mulr1.
      * by rewrite eceval1 oner_neq0.
      * by rewrite eceval1 oner_neq0.
    move=> oncve; move: (decomp_correct (unifun_neq0 ecp) oncve) => D2.
    case/andP: (uniok_uniq (unifun_neq0 ecp) oncve D1 D2).
    by rewrite /uniformizer; move/eqP=> <-.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma orderC c ecp: order c%:FP ecp = 0.
  Proof.
    case oncve: (oncurve ecp); last by rewrite order_outcve ?oncve.
    have [->|nz_c] := eqVneq c 0; first by rewrite order0.
    move: (uniokC ecp (unifun_neq0 ecp) nz_c) => D.
    have nz_cfp: c%:FP != 0 by rewrite tofrac_eq0 ecX_eq0 polyC_eq0.
    move: (decomp_correct nz_cfp oncve) => D'.
    by case/andP: (uniok_uniq nz_cfp oncve D D')=> /eqP /esym.
  Qed.

  Lemma orderF p ecp: order p%:F ecp = (poly_order p ecp).1.
  Proof.
    case oncve: (oncurve ecp); last first.
    + by rewrite ?(poly_order_outcve, order_outcve) ?oncve.
    have[->|nz_p] := eqVneq p 0.
    + by rewrite order0 /poly_order eqxx.
    move: (poly_order_correct nz_p oncve).
    case: (poly_order p ecp) => [o [n d]] => D /=.
    have nz_fp: p%:F != 0 by rewrite tofrac_eq0.
    move: (decomp_correct nz_fp oncve) => D'.
    by case/andP: (uniok_uniq nz_fp oncve D D')=> /eqP /esym.
  Qed.

  Lemma orderF_inf (f : ecpoly): order f%:F ∞ = - ((degree f).-1)%:Z.
  Proof.
    case: (f =P 0) => [->|/eqP nz_f].
      by rewrite degree0 order0 oppr0.
    by rewrite orderF /poly_order (negbTE nz_f) /=.
  Qed.

  Lemma order_mul f1 f2 ecp: (f1 * f2) != 0 ->
    order (f1 * f2) ecp = order f1 ecp + order f2 ecp.
  Proof.
    case oncve: (oncurve ecp); last first.
    + by rewrite !order_outcve ?oncve.
    rewrite mulf_eq0=> /norP [nz_f1 nz_f2].
    have nz_f: f1 * f2 != 0 by rewrite mulf_neq0.
    move: (decomp_correct nz_f1 oncve) => D1.
    move: (decomp_correct nz_f2 oncve) => D2.
    move: (uniok_mul (unifun_neq0 ecp) oncve D1 D2) => D.
    move: (decomp_correct nz_f oncve) => D'.
    by case/andP: (uniok_uniq nz_f oncve D D')=> /eqP /esym.
  Qed.

  Lemma order_exp f n ecp: order (f^+n) ecp = (order f ecp) *+ n.
  Proof.
    have [->|nz_f] := (eqVneq f 0).
      by rewrite expr0n; case: n => [|n] /=; rewrite orderC ?mul0rn.
    elim: n => [|n IH]; first by rewrite expr0 orderC mulr0n.
    rewrite exprS; case: n IH => [|n] IH; first by rewrite expr0 mulr1.
    by rewrite order_mul ?(mulf_neq0, expf_eq0) // IH.
  Qed.

  Lemma order_inv f ecp:
    order (f^-1) ecp = - (order f ecp).
  Proof.
    case oncve: (oncurve ecp); last first.
    + by rewrite !order_outcve ?oncve.
    have [->|nz_f] := eqVneq f 0.
    + by rewrite invr0 order0 oppr0.
    move: (decomp_correct nz_f oncve).
    move/(uniok_inv (unifun_neq0 ecp) oncve) => D.
    have nz_fi: f ^-1 != 0 by rewrite invr_neq0.
    move: (decomp_correct nz_fi oncve) => D'.
    by case/andP: (uniok_uniq nz_fi oncve D D')=> /eqP /esym.
  Qed.

  Lemma order_expz f (z : int) ecp: order (f^z) ecp = order f ecp *~ z.
  Proof.
    case: z => [n|n] /=.
    + by rewrite -exprnP order_exp.
    + rewrite NegzE -exprz_inv order_exp order_inv.
      by rewrite -nmulrn mulNrn.
  Qed.

  Lemma order_opp f ecp:
    order (- f) ecp = order f ecp.
  Proof.
    case oncve: (oncurve ecp); last first.
    + by rewrite !order_outcve ?oncve.
    have [->|nz_f] := eqVneq f 0.
    + by rewrite oppr0 order0.
    rewrite -mulN1r order_mul.
    + by rewrite -tofracN -ecXN -polyC_opp orderC ?simp.
    + by rewrite ?(mulf_neq0, oppr_eq0, oner_neq0).
  Qed.

  Lemma orderE (n d : ecpoly) p: n != 0 -> d != 0 ->
    order (n // d) p = (poly_order n p).1 - (poly_order d p).1.
  Proof.
    move=> nz_n nz_d; rewrite order_mul; last first.
    + by rewrite ?(mulf_neq0, invr_eq0, tofrac_eq0).
    by rewrite order_inv !orderF.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma orderfinF_ge0:
    forall f x y, order f%:F (|x, y|) >= 0.
  Proof.
    move=> f x y; have [->|nz_f] := eqVneq f 0.
    + by rewrite order0.
    rewrite orderF // /poly_order (negbTE nz_f) /=.
    case: (_ == _) => //=; case: (poly_orderfin _ _ _).
    by move=> o [n d]; rewrite le0z_nat.
  Qed.

  Lemma orderfinF_nat f x y:
    exists n : nat, order f%:F (|x, y|) = n.
  Proof.
    move: (orderfinF_ge0 f x y).
    by case: (order _ _)=> // => n _; exists n.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma order_fdegree (f : {fraction {ecpoly E}}): order f ∞ = - (fdegree f).
  Proof.
    have [->|] := eqVneq f 0.
      by rewrite order0 fdegreeC oppr0.
    elim/fracW: f => n d nz_d; rewrite mulf_eq0; case/norP.
    rewrite tofrac_eq0 => nz_n _; rewrite orderE //.
    rewrite /poly_order !orbF (negbTE nz_d) (negbTE nz_n) /=.
    rewrite opprK addrC -opprB fdegreeE ?mulf_neq0 //.
    by rewrite !predn_int ?(lt0n, degree_eq0) //; ssring.
  Qed.

  Lemma fdegree_uniformizer (u : {fraction {ecpoly E}}):
    uniformizer u ∞ -> fdegree u = -1.
  Proof.
    by rewrite /uniformizer order_fdegree => /eqP <-; rewrite opprK.
  Qed.

  Lemma fdegree_unifun: fdegree (unifun ∞) = -1.
  Proof. by rewrite fdegree_uniformizer // uniformizer_unifun. Qed.

  Lemma fdegree_uniok_inf f u o n d: uniok_inf f u o n d -> fdegree (n // d) = 0.
  Proof.
    case/uniok_infP; rewrite mulf_eq0 !(invr_eq0, tofrac_eq0).
    move=> _ /norP [nz_n nz_d] eq_deg; rewrite fdegreeM; last first.
      by rewrite mulf_neq0 // ?invr_eq0 tofrac_eq0.
    by rewrite fdegreeV !fdegreeF eq_deg subrr.
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition conj: {fraction ecpoly} -> {fraction ecpoly}
    := rlift (conjp (E := E)).

  Lemma conj0     : conj 0 = 0                . Proof. exact: rmorph0. Qed.
  Lemma conjN     : {morph conj: x / - x}     . Proof. exact: rmorphN. Qed.
  Lemma conjD     : {morph conj: x y / x + y} . Proof. exact: rmorphD. Qed.
  Lemma conjB     : {morph conj: x y / x - y} . Proof. exact: rmorphB. Qed.
  Lemma conjMn  n : {morph conj: x / x *+ n}  . Proof. exact: rmorphMn. Qed.
  Lemma conjMNn n : {morph conj: x / x *- n}  . Proof. exact: rmorphMNn. Qed.
  Lemma conj1     : conj 1 = 1                . Proof. exact: rmorph1. Qed.
  Lemma conjM     : {morph conj: x y  / x * y}. Proof. exact: rmorphM. Qed.
  Lemma conjX   n : {morph conj: x / x ^+ n}  . Proof. exact: rmorphX. Qed.
  Lemma conjV     : {morph conj: x / x^-1}    . Proof. exact: fmorphV. Qed.

  Lemma conjF p : conj (p%:F) = (conjp p)%:F.
  Proof. exact: rliftF. Qed.

  Lemma conjE n d : conj (n // d) = (conjp n) // (conjp d).
  Proof. exact: rliftE. Qed.

  Lemma conjK f: conj (conj f) = f.
  Proof.
    by elim/fracW: f=> n d nz_d; rewrite !conjE !conjpK.
  Qed.

  Lemma conjXz z : {morph conj: x / x ^ z}.
  Proof.
    by case: z=> n x; rewrite /exprz ?conjV conjX.
  Qed.

  Lemma conj_eq0 f: (conj f == 0) = (f == 0).
  Proof.
    by elim/fracW: f=> n d nz_d; rewrite conjE !frac_eq0 !conjp_eq0.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_conj (u : {fraction ecpoly}) f ecp o n d:
       u != 0 -> oncurve ecp
    -> uniok u f ecp o n d
    -> uniok (conj u) (conj f) (\- ecp) o (conjp n) (conjp d).
  Proof.
    move=> nz_u oncve Du.
    have Hdecomp: (conj f) = (conj u) ^ o * ((conjp n) // (conjp d)).
    + by rewrite (uniok_decomp Du) conjM conjE conjXz.
    case: ecp oncve Du=> [|x y] /= oncve Du.
    + apply/uniok_infP; split; first by apply: Hdecomp.
      * rewrite mulf_eq0 invr_eq0 !tofrac_eq0 !conjp_eq0.
        by rewrite negb_or (uniok_inf_nz_num Du) (uniok_inf_nz_den Du).
      * by rewrite !degree_conjp (uniok_inf_degeq Du).
    + apply/uniok_finP; split; first by apply: Hdecomp.
      * by rewrite eceval_conjp (uniok_fin_num_eval_neq0 Du).
      * by rewrite eceval_conjp (uniok_fin_den_eval_neq0 Du).
  Qed.

  Lemma conj_unifun_R x y:
    y != 0 -> conj (unifun (|x, y|)) = unifun (|x, y|).
  Proof.
    move=> nz_y; rewrite /= /unifun_fin (negbTE nz_y).
    by rewrite conjF conjp_ecX.
  Qed.

  Lemma conj_unifun_S c:
    conj (unifun (|c, 0|)) = - (unifun (|c, 0|)).
  Proof.
    by rewrite /= /unifun_fin eqxx conjF conjp_ecY tofracN.
  Qed.

  Lemma conj_unifun_inf:
    conj (unifun ∞) = -(unifun ∞).
  Proof.
    rewrite /= conjE !(conjp_ecX, conjp_ecY).
    by rewrite tofracN invrN mulrN.
  Qed.

  Local Hint Extern 0 (is_true (unifun _ != 0)) => exact: unifun_neq0.

  Lemma unifun_conj ecp:
    oncurve ecp -> uniformizer (conj (unifun ecp)) ecp.
  Proof.
    move=> oncve; move: (uniformizer_unifun oncve).
    case: ecp oncve=> [|x y] oncve Hu; rewrite /uniformizer.
    + by rewrite conj_unifun_inf order_opp.
    + move: Hu oncve; have [->|nz_y] := eqVneq y 0 => Hu oncve.
      * by rewrite conj_unifun_S order_opp.
      * by rewrite conj_unifun_R.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniok_P_to_unifun u f ecp (o : nat) n d:
       uniformizer u ecp -> f != 0 -> oncurve ecp
    -> uniok u f ecp o n d
    -> uniok (unifun ecp) f ecp o (n * (decomp u ecp).1 ^+ o) (d * (decomp u ecp).2 ^+ o).
  Proof.
    move=> Hu nz_f oncve Df;
      move: (uniok_nz_den Df)=> nz_d;
      move: (uniok_nz_num Df)=> nz_n.
    move: (decomp_correct (uniformizer_neq0 Hu) oncve) => Du;
      move: (uniok_nz_den Du);
      move: (uniok_nz_num Du).
    move: (decomp u ecp).1 (decomp u ecp).2 Du=> nu du Du nz_nu nz_du.
    have Hdecomp : f = (unifun ecp) ^ o * ((n * nu ^+ o) // (d * du ^+ o)).
    + move/uniok_decomp: Df=> ->; move/uniok_decomp: Du=> ->.
      move: Hu; rewrite /uniformizer=> /eqP ->.
      rewrite expr1z !expfzMl -!exprnP -mulrA; congr (_ * _).
      rewrite mulf_cross exprVn -!tofracX -invfM -!tofracM.
      by rewrite [_ * n]mulrC [_ * d]mulrC.
    have nz_no: n * nu ^+ o != 0 by rewrite mulf_neq0 // expf_neq0.
    have nz_do: d * du ^+ o != 0 by rewrite mulf_neq0 // expf_neq0.
    case: {Hu} ecp oncve Du Df Hdecomp=> [|x y] oncve /= Du Df Hdecomp.
    + apply/uniok_infP; split.
      * exact: Hdecomp.
      * by rewrite mulf_neq0 ?(invr_eq0, tofrac_eq0).
      * rewrite !degree_mul_id // !degree_exp //.
        by rewrite (uniok_inf_degeq Du) (uniok_inf_degeq Df).
    + apply/uniok_finP; split.
      * exact: Hdecomp.
      * rewrite !(eceval_mul, eceval_exp) // mulf_neq0 //.
        - by apply (uniok_fin_num_eval_neq0 Df).
        - by rewrite expf_neq0 //; apply (uniok_fin_num_eval_neq0 Du).
      * rewrite !(eceval_mul, eceval_exp) // mulf_neq0 //.
        - by apply (uniok_fin_den_eval_neq0 Df).
        - by rewrite expf_neq0 //; apply (uniok_fin_den_eval_neq0 Du).
  Qed.

  Lemma uniok_to_unifun u f ecp o n d:
       uniformizer u ecp -> f != 0 -> oncurve ecp
    -> uniok u f ecp o n d
    -> exists nu, exists du,
         uniok (unifun ecp) f ecp o (n * nu) (d * du).
  Proof.
    move=> Hu nz_f oncve; case: o=> /= o Df.
    + move: (uniok_P_to_unifun Hu nz_f oncve Df) => D.
      exists ((decomp u ecp).1 ^+ o);
        exists ((decomp u ecp).2 ^+ o);
          exact: D.
    + have nz_u : u != 0 by apply (uniformizer_neq0 Hu).
      move: (uniok_inv nz_u oncve Df); rewrite NegzE opprK => Dfi.
      have nz_fi: f^-1 != 0 by rewrite invr_neq0 ?nz_f.
      move: (uniok_P_to_unifun Hu nz_fi oncve Dfi) => D.
      move: (uniok_inv (unifun_neq0 ecp) oncve D)=> {D}.
      rewrite invrK => D;
        exists ((decomp u ecp).2 ^+ o.+1);
          exists ((decomp u ecp).1 ^+ o.+1);
            exact: D.
  Qed.

  Lemma order_correct_unfz u f ecp o n d:
       uniformizer u ecp -> f != 0 -> oncurve ecp
    -> uniok u f ecp o n d
    -> o = order f ecp.
  Proof.
    move=> Hu nz_f oncve Df.
    move: (decomp_correct nz_f oncve) => Df1.
    move: (uniok_to_unifun Hu nz_f oncve Df) => [nu [du]] Df2.
    by move: (uniok_uniq nz_f oncve Df1 Df2)=> /andP [/eqP ->].
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma order_conj f ecp:
    order (conj f) (\- ecp) = order f ecp.
  Proof.
    case oncve: (oncurve ecp); last first.
    + by rewrite !order_outcve // -?oncurveN oncve.
    have [->|nz_f] := eqVneq f 0; first by rewrite conj0 !order0.
    have oncveN := ECGroup.negO oncve.
    have nz_cf: conj f != 0 by rewrite conj_eq0.
    move/(uniok_conj (unifun_neq0 _) oncveN): (decomp_correct nz_cf oncveN).
    rewrite unifun_opp conjK ECGroup.negK //.
    case/(uniok_to_unifun (unifun_conj oncve) nz_f oncve)=> [nu [du D]].
    move: (decomp_correct nz_f oncve) => D'.
    by move: (uniok_uniq nz_f oncve D D')=> /andP [/eqP].
  Qed.

  Lemma order_normp p ecp:
    order ((normp p)%:E)%:F ecp = (order p%:F ecp) + (order (conjp p)%:F ecp).
  Proof.
    have [->|nz_p] := eqVneq p 0.
    + by rewrite norm0 conjp0 !order0.
    rewrite -[(normp _)%:E]conjp_normp tofracM order_mul //.
    by rewrite mulf_eq0 !tofrac_eq0 conjp_eq0 (negbTE nz_p).
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma uniokS c:
       root Xpoly c
    -> uniok (unifun (|c, 0|)) (('X - c%:P)%:E)%:F (|c, 0|) 2 1 (Xpoly %/ ('X - c%:P))%:E.
  Proof.
    move=> Hr; set ecp := (|c, 0|); set d := (_ %/ _); set u := unifun ecp.
    have oncve : oncurve ecp by rewrite -Xpoly_oncurve.
    apply/uniok_finP; split.
    + rewrite /u /ecp /= /unifun_fin eqxx -exprnP -tofracX.
      rewrite ecY_sqr expr1n !mul1r (Xpoly_factor_oc_spec oncve).
      rewrite /d ecXM -[X in _ // X]mulr1 frac_mull; last first.
      * by rewrite ecX_eq0 Xpoly_divp_factor_neq0.
      * by rewrite divr1.
    + by rewrite eceval1 oner_neq0.
    + rewrite ecX_eceval /d -['X - _]expr1 -(Xpoly_root_mu Hr).
      by apply: rootN_div_mu.
  Qed.

  Lemma uniokR x y:
       y != 0 -> oncurve (|x, y|)
    -> uniok (unifun (|x, y|)) (('X - x%:P)%:E)%:F (|x, y|) 1 1 1.
  Proof.
    move=> nz_y oncve; apply/uniok_finP; split; try by rewrite eceval1 oner_neq0.
    by rewrite divr1 mulr1 expr1z /= /unifun_fin (negbTE nz_y).
  Qed.

  Lemma poly_orderS c:
       root Xpoly c
    -> (poly_order (('X - c%:P)%:E) (|c, 0|)).1 = 2.
  Proof.
    move=> Hr; move: (uniokS Hr)=> /poly_order_orderE <- //.
    by rewrite -Xpoly_oncurve.
  Qed.

  Lemma poly_orderR x y:
       y != 0 -> oncurve (|x, y|)
    -> (poly_order (('X - x%:P)%:E) (|x, y|)).1 = 1.
  Proof.
    by move=> nz_y oncve; move: (uniokR nz_y oncve) => /poly_order_orderE <-.
  Qed.

  Lemma orderS c:
    root Xpoly c -> order (('X - c%:P)%:E)%:F (|c, 0|) = 2.
  Proof.
    by move=> Hr; move: (poly_orderS Hr); rewrite -orderF //.
  Qed.

  Lemma orderR x y:
       y != 0 -> oncurve (|x, y|)
    -> order (('X - x%:P)%:E)%:F (|x, y|) = 1.
  Proof.
    move=> nz_y oncve; move: (poly_orderR nz_y oncve).
    by rewrite -orderF.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma order0_num_eval_neq0:
    forall n p x y,
         n // p != 0
      -> oncurve (|x, y|)
      -> order (n // p) (|x, y|) = 0
      -> p.[x, y] != 0 -> n.[x, y] != 0.
  Proof.
    move=> n p x y; rewrite frac_eq0 => /norP [nz_n nz_p] oncve ordf nz_p_xy.
    have nz_np: n // p != 0 by rewrite frac_eq0 negb_or nz_n nz_p.
    apply/negP=> /eqP n_xy_0; move: (decomp_fin_correct nz_np oncve) => D.
    have nz_num := (uniok_fin_nz_num D); have nz_den := (uniok_fin_nz_den D).
    move: (uniok_fin_decomp D); rewrite ordf expr0z mul1r => /eqP.
    rewrite frac_eq ?mulf_neq0 // => /eqP; move/(congr1 [fun p => p.[x, y]]) => /=.
    rewrite /= !eceval_mul // n_xy_0 mul0r => /esym /eqP.
    by rewrite mulf_eq0 (negbTE (uniok_fin_num_eval_neq0 D)) /= (negbTE nz_p_xy).
  Qed.

  Lemma order_ge0_num_eval_eq0:
    forall n p x y,
         n // p != 0
      -> oncurve (|x, y|)
      -> order (n // p) (|x, y|) > 0
      -> n.[x, y] = 0.
  Proof.
    move=> n p x y nz_np; have := nz_np; rewrite frac_eq0 => /norP.
    move=> [nz_n nz_p] oncve ordf; move: (decomp_fin_correct nz_np oncve) => D.
    move: (uniok_fin_decomp D); case ordf: (order _ _) ordf => [o|o] //.
    rewrite ltz_nat -exprnP unifun_finE -tofracX mulrA -tofracM => poso /eqP.
    rewrite frac_eq ?(mulf_neq0, uniok_fin_nz_den D) // => /eqP.
    move/(congr1 [fun p => p.[x, y]]) => /=; rewrite !(eceval_mul, eceval_exp) //.
    rewrite eceval_unifun_fin expr0n eqn0Ngt poso /= !mul0r => /eqP.
    by rewrite mulf_eq0 (negbTE (uniok_fin_den_eval_neq0 D)) orbF => /eqP.
  Qed.

  Lemma order_poly_cmp0:
    forall p x y, oncurve (|x, y|) -> p != 0 ->
      (p.[x, y] != 0) = (order p%:F (|x, y|) == 0).
  Proof.
    move=> p x y oncve nz_p; case: (orderfinF_nat p x y) => n.
    have pf1_nz: p // 1 != 0 by rewrite divr1 tofrac_eq0.
    have ->: p%:F = p // 1 by rewrite divr1.
    move => Ho; rewrite Ho; case: (posnP n).
    + move/(congr1 Posz); rewrite -Ho => {n Ho} Ho.
      rewrite Ho eqxx (order0_num_eval_neq0 (p := 1)) //.
      by rewrite eceval1 oner_neq0.
    + rewrite -ltz_nat -Ho => {Ho} Ho.
      rewrite (order_ge0_num_eval_eq0 (p := 1)) //.
      by move/gtr_eqF: Ho => ->; rewrite eqxx.
  Qed.

  Lemma order_ge0_den: forall f x y,
       f != 0
    -> oncurve (|x, y|)
    -> reflect
         (exists n, exists d, (f = n // d) /\ (d.[x, y] != 0))
         (0 <= order f (|x, y|)).
  Proof.
    move=> f x y nz_f oncve; apply: (iffP idP).
    + move=> Ho; move: (decomp_fin_correct nz_f oncve)=> D.
      move: (uniok_fin_decomp D); case: (order _ _) Ho=> // o _ ->.
      rewrite -exprnP unifun_finE -tofracX mulrA -tofracM.
      set n := (_ * _.1); set d := _.2; exists n; exists d; split=> //.
      by rewrite (uniok_fin_den_eval_neq0 D).
    + case=> [n [d]] [eq]; move: nz_f; rewrite eq.
      rewrite mulf_eq0 invr_eq0 !tofrac_eq0 => /norP [nz_n nz_d].
      rewrite order_poly_cmp0 // orderE // -!orderF => /eqP ->.
      rewrite subr0 orderF /poly_order; case: (_ || _) => //.
      by case: (poly_orderfin _ _ _) => o [p1 p2].
  Qed.

  Lemma order_lt0_den_eval_eq0 n d x y:
       n // d != 0
    -> oncurve (|x, y|)
    -> order (n // d) (|x, y|) < 0
    -> d.[x, y] = 0.
  Proof.
    rewrite frac_eq0 => /norP [nz_n nz_d] oncve Ho.
    have nz_nd: n // d != 0 by rewrite frac_eq0 negb_or nz_n nz_d.
    move: (decomp_fin_correct nz_nd oncve) => D.
    move: (uniok_fin_decomp D); case: (order _ _) Ho => //.
    move=> o; rewrite NegzE -exprnN unifun_finE => nego /eqP.
    rewrite [_ ^- _ * _]mulrC -mulrA -invfM -tofracX.
    rewrite -tofracM frac_eq; last first.
    + rewrite !mulf_neq0 ?expf_neq0 //.
      * by rewrite (uniok_fin_nz_den D).
      * by rewrite -tofrac_eq0 -unifun_finE unifun_neq0.
    move/eqP => /(congr1 [fun p => p.[x, y]]) /=.
    rewrite !(eceval_mul, eceval_exp) // eceval_unifun_fin.
    rewrite exprS !(mul0r, mulr0) => /esym /eqP.
    by rewrite mulf_eq0 (negbTE (uniok_fin_num_eval_neq0 D)) => /eqP.
  Qed.

  Lemma order_lt0_den_evalP f x y:
    f != 0 -> oncurve (|x, y|) ->
      reflect
        (forall n d, f = n // d -> d.[x, y] = 0)
        (order f (|x, y|) < 0).
  Proof.
    elim/fracW: f => n d _ nz_nd oncve; apply: (iffP idP).
    + move=> Ho n' d' Heq; move: Ho; rewrite Heq.
      by move/order_lt0_den_eval_eq0; rewrite -Heq=> ->.
    + move=> H; case Ho: (order _ _)=> [o|o] //.
      rewrite ltrNge; apply/negP; rewrite -Ho.
      move/order_ge0_den => /(_ nz_nd oncve) [n' [d']].
      by case=> Heq; rewrite (H _ _ Heq) eqxx.
  Qed.

  Lemma poly_order_mu (p : {poly K}) (x y : K):
    oncurve (|x, y|) -> (poly_order p%:E (|x, y|)).1 = ((\mu_x p) * (y == 0%R).+1)%N.
  Proof.
    move=> oncve; rewrite -orderF; have [->|nz_p] := (eqVneq p 0).
      by rewrite order0 mu0 mul0n.
    rewrite -{1}[p](mu_divp_mul x); set p' := (_ %/ _).
    have nz_p': p' != 0 by rewrite divp_factor_mu_neq0.
    rewrite !(ecXM, ecXX) !(tofracM, tofracX) order_mul; last first.
      by rewrite mulf_neq0 ?expf_neq0 // tofrac_eq0 ecX_eq0 ?polyXsubC_eq0.
    have /eqP->: order (p'%:E)%:F (|x, y|) == 0.
      rewrite -order_poly_cmp0 // ?ecX_eq0 // ecX_eceval.
      by rewrite -rootE rootN_div_mu.
    rewrite add0r order_exp; move: oncve; have [->|nz_y] := (eqVneq y 0).
    + rewrite /= expr0n eq_sym /= -horner_Xpoly -rootE => root_Xc.
      by rewrite orderS // eqxx /= PoszM pmulrn -mulrzl intz.
    + by move=> oncve; rewrite orderR // (negbTE nz_y) muln1 natz.
  Qed.

  Lemma order_Xpoly_le2 p: order (Xpoly%:E)%:F p <= 2.
  Proof.
    case oncve: (oncurve p); last by rewrite order_outcve ?oncve.
    case: p oncve => [|x y] oncve; first by rewrite orderF_inf ltez_natE.
    rewrite orderF poly_order_mu // -[2]mul1n !PoszM ler_pmul //.
      + by rewrite lez_nat smooth. + by case: (y =P 0).
  Qed.

  Lemma even_orderS n d c: root Xpoly c ->
    ~~ odd `|order (n%:E // d%:E) (|c, 0|)|.
  Proof.
    have [->|nz_n] := (eqVneq n 0); first by rewrite mul0r order0.
    have [->|nz_d] := (eqVneq d 0); first by rewrite invr0 mulr0 order0.
    move=> root_Xc; rewrite order_mul ?order_inv; last first.
      by rewrite mulf_neq0 // !(invr_eq0, tofrac_eq0, ecX_eq0).
    have oncve_c: oncurve (|c, 0|).
      by move/eqP: root_Xc; rewrite horner_Xpoly /= => ->; rewrite expr0n.
    rewrite -[n](mu_divp_mul c) -[d](mu_divp_mul c).
    set n' : {poly K} := (n %/ _); set d' : {poly K} := (d %/ _).
    have nz_n': n' != 0 by rewrite divp_factor_mu_neq0.
    have nz_d': d' != 0 by rewrite divp_factor_mu_neq0.
    rewrite !(ecXM, ecXX) !(tofracM, tofracX) !order_mul; first last.
    + by rewrite mulf_neq0 ?expf_neq0 // tofrac_eq0 ecX_eq0 ?polyXsubC_eq0.
    + by rewrite mulf_neq0 ?expf_neq0 // tofrac_eq0 ecX_eq0 ?polyXsubC_eq0.
    have /eqP->: order (n'%:E)%:F (|c, 0|) == 0.
      rewrite -order_poly_cmp0 // ?ecX_eq0 // ecX_eceval.
      by rewrite -rootE rootN_div_mu.
    have /eqP->: order (d'%:E)%:F (|c, 0|) == 0.
      rewrite -order_poly_cmp0 // ?ecX_eq0 // ecX_eceval.
      by rewrite -rootE rootN_div_mu.
    rewrite !add0r !order_exp orderS // !pmulrn -mulrzBr.
    move: (_ - _) => z; have ->: `|2%:Z *~ z|%N = `|z|.*2.
      have: injective Posz by move=> ?? [->].
      apply; rewrite abszE normrMz -abszE absz_nat -mul2n.
      by rewrite PoszM -pmulrn -mulr_natl mulrC abszE natz.
    by rewrite odd_double.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma order_add f g ecp:
       f * g != 0
    -> order f ecp != order g ecp
    -> order (f + g) ecp = Num.min (order f ecp) (order g ecp).
  Proof.
    wlog: f g / order f ecp < order g ecp.
      move=> wlog nz_fg ne; have := ne; rewrite neqr_lt; case/orP.
        by move/wlog; apply.
      rewrite addrC minrC => /wlog -> //; rewrite 1?mulrC //.
      by rewrite eq_sym (negbTE ne).
    move=> lt nz_fg ne; have [oncve|oucve] := boolP (oncurve ecp); last first.
      by rewrite !order_outcve.
    move: nz_fg; rewrite mulf_eq0; case/norP=> nz_f nz_g.
      have := decomp_correct nz_f oncve;
      have := decomp_correct nz_g oncve;
        set nf := (decomp f ecp).1; set df := (decomp f ecp).2;
        set ng := (decomp g ecp).1; set dg := (decomp g ecp).2;
      move=> uokg uokf.
    have nz_nf: nf != 0 by rewrite decomp_nz_num.
    have nz_ng: ng != 0 by rewrite decomp_nz_num.
    have nz_df: df != 0 by rewrite decomp_nz_den.
    have nz_dg: dg != 0 by rewrite decomp_nz_den.
    rewrite minr_l 1?ltrW //; pose u := unifun ecp.
    pose fd := order f ecp; pose gd := order g ecp.
    have [/eqP|nz_fDg] := eqVneq (f + g) 0; last move: (erefl (f + g)).
      rewrite addr_eq0 => /eqP /(congr1 (order^~ ecp)) /eqP.
      by rewrite order_opp (negbTE ne).
    rewrite {1}(uniok_decomp uokf) {1}(uniok_decomp uokg) -/fd -/gd -/u.
    have ->: gd = fd + (gd - fd) by rewrite addrCA subrr addr0.
    rewrite expfzDr ?unifun_neq0 // -mulrA -mulrDr.
    have ->: gd - fd = `|gd - fd| :> int.
      by rewrite gtr0_norm // subr_gt0.
    rewrite -exprnP; case: (ecp =P ∞) => [|/eqP].
    + move=> ecpE; move: uokf uokg; rewrite ecpE /= => uokf uokg.
      rewrite {2}/u ecpE /= divf_exp mulf_div.
      rewrite -!(tofracX, tofracM) addf_div; first last.
      - by rewrite tofrac_eq0 mulf_neq0 // expf_neq0 // ecY_neq0.
      - by rewrite tofrac_eq0.
      rewrite -!(tofracD, tofracX, tofracM).
      set n := (_ + _); set d := (df * _) => /esym eq.
      have: n // d != 0.
        by apply/eqP=> z_nMdV; move: nz_fDg; rewrite eq z_nMdV mulr0 eqxx.
      have eq_deg: degree (nf * dg) = degree (ng * df).
        rewrite !degree_mul_id ?mulf_neq0 // addnC.
        by rewrite (uniok_inf_degeq uokf) (uniok_inf_degeq uokg).
      rewrite mulf_eq0 invr_eq0 !tofrac_eq0; case/norP=> nz_n nz_d.
      have D: uniok_inf u (f + g) fd n d.
        apply/uniok_infP; split=> //.
        - by rewrite mulf_neq0 ?invr_eq0 // tofrac_eq0.
        - rewrite /n degree_addl; last first.
            rewrite mulrCA -!mulrA [X in (X<_)%N]degree_mul_id; last first.
              by rewrite !mulf_neq0 // expf_neq0 // ecX_neq0.
            rewrite [X in (_<X)%N]degree_mul_id; last first.
              by rewrite !mulf_neq0 // expf_neq0 // ecY_neq0.
            rewrite degree_expX degree_expY !addSn /=.
            rewrite eq_deg ltn_add2r ltn_mul2r /= andbT.
            by rewrite lt0n absz_eq0 subr_eq0 eq_sym.
          rewrite /d [X in X=_]degree_mul_id; last first.
            by rewrite !mulf_neq0 // expf_neq0 // ecY_neq0.
          rewrite [X in _=X]degree_mul_id; last first.
            by rewrite !mulf_neq0 // expf_neq0 // ecY_neq0.
          by congr (_ + _).-1; rewrite (uniok_inf_degeq uokf).
        move: D oncve; rewrite {1}/u !ecpE => D oncve.
        have D' := (decomp_correct nz_fDg oncve).
        by case/andP: (uniok_uniq nz_fDg oncve D D') => /eqP <-.
    + have: forall p, p != ∞ -> exists xy, p = (|xy.1, xy.2|).
        by move=> T [|x y] // _; exists (x, y).
      move=> h; case/h => [[x y]] /= ecpE {h}.
      move: uokf uokg; rewrite ecpE /= => uokf uokg.
      rewrite {2}/u {1}ecpE /= mulrA -tofracX -tofracM.
      rewrite addf_div ?tofrac_eq0 // -!(tofracM, tofracD).
      set n := (_ + _); set d := (df * _) => /esym eq.
      have D: uniok_fin u (f + g) x y fd n d.
        apply/uniok_finP; split=> //.
        - rewrite /n !(eceval_exp, eceval_mul, eceval_add) -?ecpE //.
          rewrite eceval_unifun_fin expr0n absz_eq0.
          rewrite subr_eq0 [gd==fd]eq_sym (negbTE ne) !mul0r addr0 mulf_neq0 //.
          * by rewrite (uniok_fin_num_eval_neq0 uokf).
          * by rewrite (uniok_fin_den_eval_neq0 uokg).
        - rewrite /d eceval_mul -?ecpE // mulf_neq0 //.
          * by rewrite (uniok_fin_den_eval_neq0 uokf).
          * by rewrite (uniok_fin_den_eval_neq0 uokg).
      move: D oncve; rewrite {1}/u !ecpE => D oncve.
      have D' := (decomp_fin_correct nz_fDg oncve).
      by case/andP: (uniok_uniq nz_fDg oncve D D') => /eqP <-.
  Qed.

  Lemma order_add_leq f g ecp:
       f * g != 0 -> f + g != 0
    -> order (f + g) ecp >= Num.min (order f ecp) (order g ecp).
  Proof.
    wlog: f g / order f ecp <= order g ecp.
      move=> wlog nz_fg nz_fDg; case: (lerP (order f ecp) (order g ecp)).
        by move/wlog; apply.
      move/ltrW; rewrite addrC minrC => /wlog -> //.
        * by rewrite mulrC. * by rewrite addrC.
    move=> le nz_fg nz_fDg; move: le; rewrite ler_eqVlt; case/orP; last first.
      by rewrite ltr_neqAle; case/andP => /(order_add nz_fg) -> _.
    move/eqP=> eq; rewrite -eq minrr.
    have [oncve|outcve] := boolP (oncurve ecp); last first.
      by rewrite !order_outcve.
    move: nz_fg; rewrite mulf_eq0; case/norP=> nz_f nz_g.
      have := decomp_correct nz_f oncve;
      have := decomp_correct nz_g oncve;
        set nf := (decomp f ecp).1; set df := (decomp f ecp).2;
        set ng := (decomp g ecp).1; set dg := (decomp g ecp).2;
      move=> uokg uokf.
    have nz_nf: nf != 0 by rewrite decomp_nz_num.
    have nz_ng: ng != 0 by rewrite decomp_nz_num.
    have nz_df: df != 0 by rewrite decomp_nz_den.
    have nz_dg: dg != 0 by rewrite decomp_nz_den.
    pose u := unifun ecp; pose fd := order f ecp; pose gd := order g ecp.
    move: (erefl (f + g));
      rewrite {1}(uniok_decomp uokf) {1}(uniok_decomp uokg) -/fd -/gd -/u.
    rewrite /gd -eq -/fd -mulrDr addf_div ?tofrac_eq0 //.
    rewrite -!(tofracM, tofracD) => /esym fDgE; rewrite fDgE.
    have nz_D: nf * dg + ng * df != 0.
      by apply/eqP=> z; move: nz_fDg; rewrite fDgE z !(mul0r, mulr0) eqxx.
    rewrite order_mul ?(mulf_neq0, invr_eq0, tofrac_eq0) //; last first.
      by rewrite expfz_eq0 /u (negbTE (unifun_neq0 _)) andbF.
    rewrite order_expz; move: (uniformizer_unifun oncve).
    rewrite /uniformizer => /eqP ->; rewrite intz -{1}[fd]addr0.
    rewrite ler_add2l; case: (ecp =P ∞) => [|/eqP].
    + move=> ecpE; rewrite orderE ?mulf_neq0 // ecpE.
      rewrite /poly_order !orbF (negbTE nz_D).
      rewrite (negbTE (mulf_neq0 _ _)) //= -opprD oppr_ge0 subr_le0.
      have leq_predn n m: (n <= m -> n.-1 <= m.-1)%N.
        by case: n m => [|n] [|m].
      apply/leq_predn; apply/(leq_trans (degree_add _ _)).
      rewrite !degree_mul_id ?mulf_neq0 // maxn_pred.
      apply/leq_predn; move: uokf uokg; rewrite ecpE /= => uokf uokg.
      rewrite (uniok_inf_degeq uokf) (uniok_inf_degeq uokg).
      by rewrite addnC maxnn leqnn.
    + have: forall p, p != ∞ -> exists xy, p = (|xy.1, xy.2|).
        by move=> T [|x y] // _; exists (x, y).
      move=> h; case/h => [[x y]] /= ecpE {h}.
      move: uokf uokg; rewrite ecpE /= => uokf uokg.
      apply/order_ge0_den; rewrite -?ecpE //.
        by rewrite ?(mulf_neq0, invr_eq0, tofrac_eq0).
      do 2! eexists; split; first by reflexivity.
      rewrite eceval_mul -?ecpE // mulf_neq0 //.
      * by rewrite (uniok_fin_den_eval_neq0 uokf).
      * by rewrite (uniok_fin_den_eval_neq0 uokg).
  Qed.
End Order.

(* -------------------------------------------------------------------- *)
Section ECPolyRoots.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ecX E p).

  Implicit Types f : ecpoly.

  (* ------------------------------------------------------------------ *)
  Definition ecroots f : seq (K * K) :=
    let forx := fun x =>
      let sqrts := roots ('X ^+ 2 - (Xpoly.[x])%:P) in
        [seq (x, y) | y <- sqrts & f.[x, y] == 0]
    in
      undup (flatten ([seq forx x | x <- roots (normp f)])).

  Lemma ecroots0: ecroots 0 = [::].
  Proof. by rewrite /ecroots norm0 roots0. Qed.

  Lemma ecrootsC c: ecroots (c%:P)%:E = [::].
  Proof. by rewrite /ecroots /= normp_ecX -polyC_exp rootsC. Qed.

  Lemma ecroots_uniq f: uniq (ecroots f).
  Proof. by apply: undup_uniq. Qed.

  Local Hint Extern 0 (is_true (uniq (ecroots _))) => exact: ecroots_uniq.

  Lemma ecrootsP f x y:
    reflect
      [/\ (x \in roots (normp f))
       ,  (y \in roots ('X ^+ 2 - (Xpoly.[x])%:P))
       &  f.[x, y] = 0]
      ((x, y) \in ecroots f).
  Proof.
    apply: (iffP idP).
    + rewrite /ecroots mem_undup; case/mem_flattenP => rs.
      case/mapP=> x' x'_root ->; case/mapP=> y'.
      by rewrite mem_filter => /andP [/eqP ? ?] [-> ->].
    + case=> x_root y_sqrt fxy_eq0; rewrite /ecroots mem_undup.
      set rs :=  [seq (x, z) | z <- roots ('X^2 - (Xpoly.[x])%:P) & f.[x, z] == 0].
      apply/mem_flattenP; exists rs; first by apply/mapP; exists x.
      rewrite /rs; apply/mapP; exists y => //; rewrite mem_filter.
      by rewrite fxy_eq0 y_sqrt eqxx.
  Qed.

  Lemma ecroots_oncve f x y: (x, y) \in ecroots f -> oncurve (|x, y|).
  Proof.
    case/ecrootsP => _ y_sqrt _; rewrite oncurve_root rootE.
    by rewrite  -mem_root -rootsP // XnsubC_eq0.
  Qed.

  Lemma ecroots_rootP f x y: ((x, y) \in ecroots f) -> f.[x, y] == 0.
  Proof. by case/ecrootsP => _ _ ->. Qed.

  Lemma ecroot_normp f x y: oncurve (|x, y|) ->
    ((normp f).[x] == 0) = ((f.[x, y] == 0) || (f.[x, -y] == 0)).
  Proof.
    move=> oncve; rewrite -mulf_eq0 -{3}[f]conjpK eceval_conjp.
    by rewrite -eceval_mul // conjp_normp ecX_eceval.
  Qed.

  Implicit Arguments ecroot_normp [f x].

  Lemma ecroots_order f x y:
    ((x, y) \in ecroots f) = (order f%:F (|x, y|) != 0).
  Proof.
    have [->|nz_f] := eqVneq f 0.
    + by rewrite order0 ecroots0.
    apply/idP/idP.
    + move=> xy_zero; have oncve := (ecroots_oncve xy_zero).
      by rewrite -order_poly_cmp0 // negbK ecroots_rootP.
    + case oncve: (oncurve (|x, y|)); last first.
      * by rewrite order_outcve // oncve.
      rewrite -order_poly_cmp0 // negbK => /eqP xy_zero.
      apply/ecrootsP; split => //.
      * rewrite rootsP ?norm_eq0 // rootE.
        by rewrite (ecroot_normp y) // xy_zero eqxx.
      * rewrite rootsP ?XnsubC_eq0 // mem_root -rootE.
        by rewrite -oncurve_root.
  Qed.

  Lemma ecroots_root f x y: f != 0 -> oncurve (|x, y|) ->
    ((x, y) \in ecroots f) = (f.[x, y] == 0).
  Proof.
    by move=> nz_f oncve; rewrite ecroots_order -order_poly_cmp0 // negbK.
  Qed.

  Lemma mem_ecroots_conjp f x y:
    (x, y) \in (ecroots (conjp f)) = ((x, -y) \in (ecroots f)).
  Proof.
    rewrite !ecroots_order; case oncve: (oncurve (|x, y|)).
    + by rewrite -conjF -order_conj //= conjK.
    + by rewrite !order_outcve ?(oncurveN_fin, oncve).
  Qed.

  Lemma mem_ecroots_ecX p x y:
    ((x, y) \in ecroots p%:E) = ((x, -y) \in ecroots p%:E).
  Proof.
    by rewrite -mem_ecroots_conjp conjp_ecX.
  Qed.

  Lemma mem_ecrootsM f g x y: (f * g != 0) ->
      ((x, y) \in ecroots (f * g))
    = ((x, y) \in ecroots f) || ((x, y) \in ecroots g).
  Proof.
    rewrite mulf_eq0; case/norP => nz_f nz_g.
    rewrite !ecroots_order tofracM order_mul; last first.
    + by rewrite ?(mulf_neq0, tofrac_eq0).
    case: (orderfinF_nat f x y) => n1 ->.
    case: (orderfinF_nat g x y) => n2 ->.
    by rewrite !eqz_nat addn_eq0 negb_and.
  Qed.

  Lemma mem_ecroots_normp f x y:
    (x, y) \in (ecroots (normp f)%:E) =
      ((x, y) \in (ecroots f)) || ((x, -y) \in (ecroots f)).
  Proof.
    have [->|nz_f] := eqVneq f 0.
    + by rewrite norm0 ecroots0.
    rewrite -[(normp _)%:E]conjp_normp.
    rewrite mem_ecrootsM ?mem_ecroots_conjp //.
    by rewrite ?(mulf_neq0, conjp_eq0).
  Qed.

  Lemma ecroots_conjp f:
    perm_eq (ecroots (conjp f)) [seq (ecp.1, -ecp.2) | ecp <- ecroots f].
  Proof.
    set ng := fun (p : K * K) => (p.1, -p.2); have Hing: injective ng.
    + case=> [x1 y1] [x2 y2] /= [<- /eqP].
      by rewrite eqr_opp; move/eqP=> ->.
    apply: uniq_perm_eq; rewrite ?map_inj_uniq //.
    case=> [x y];rewrite -{2}[y]opprK -/(ng (x, -y)).
    by rewrite mem_map // mem_ecroots_conjp.
  Qed.

  Lemma ecrootsM f g:
    f * g != 0 -> perm_eq (ecroots (f * g)) (undup ((ecroots f) ++ (ecroots g))).
  Proof.
    move=> nz_fg; apply: uniq_perm_eq=> //.
    + by rewrite undup_uniq.
    by case=> [x y]; rewrite mem_ecrootsM // mem_undup mem_cat.
  Qed.

  Lemma ecroots_sqr (p : ecpoly):
    perm_eq (ecroots (p * p)) (ecroots p).
  Proof.
    have [->|nz_p] := eqVneq p 0.
    + by rewrite mulr0 ecroots0.
    apply: (perm_eq_trans (ecrootsM _)); rewrite ?mulf_neq0 //.
    by rewrite undup_double undup_id.
  Qed.
End ECPolyRoots.
