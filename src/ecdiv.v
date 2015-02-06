(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype xseq.
Require Import fintype choice bigop ssralg ssrfun ssrint ssrnum.
Require Import generic_quotient fracfield polyall.
Require Import polyall polyfrac polydec.
Require Import ec ecpoly eceval ecorder freeg.
Require Import generic_quotient fraction.

Import GRing.Theory.
Import Num.Theory.
Import FracField.

Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma inj_pair1 (T U : Type) (x : T):
  injective (fun (y : U) => (x, y)).
Proof. by move=> y1 y2 /= []. Qed.

Lemma inj_pair2 (T U : Type) (y : T):
  injective (fun (x : U) => (x, y)).
Proof. by move=> x1 x2 /= []. Qed.

Lemma pairE (T U : Type) (p : T * U): (p.1, p.2) = p.
Proof. by case: p. Qed.

Local Hint Immediate inj_pair1 inj_pair2.

Reserved Notation "D1 :~: D2" (at level 70, no associativity).

(* -------------------------------------------------------------------- *)
Section ECDiv.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ecX E p).

  Local Notation "\- x"   := (@ECGroup.neg _ x).
  Local Notation "x \+ y" := (@ECGroup.add _ E x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Implicit Types f : ecpoly.

  (* ------------------------------------------------------------------ *)
  Definition ecdivp (f : ecpoly) : {freeg (point K)} :=
    locked (
      \sum_(p <- ecroots f) << (order f%:F (|p.1, p.2|)) *g (|p.1, p.2|) >>
    + << order f%:F ∞ *g ∞ >>).

  Lemma ecdivpE (f : ecpoly) (p : point K):
    coeff p (ecdivp f) = order f%:F p.
  Proof.
    rewrite /ecdivp; unlock; rewrite raddfD raddf_sum /= coeffU.
    pose F q := (order f%:F (|q.1, q.2|)) * ((|q.1, q.2|) == p).
    rewrite (eq_bigr F); last first.
      by move=> q _; rewrite coeffU {}/F natz.
    rewrite {}/F; case: p => [|x y].
      by rewrite big1 => [|i _] /=; rewrite !Monoid.simpm.
    rewrite !Monoid.simpm; case: (order f%:F (|x, y|) =P 0).
    + move=> z_ordfxy; rewrite z_ordfxy big_seq big1 //.
      move=> [q1 q2] /= q_ecrf; set q := (|q1, q2|).
      case: (q =P (|x, y|)); last by rewrite mulr0.
      by move=> Eq; move:z_ordfxy; rewrite Eq => ->.
    + move/eqP; rewrite -ecroots_order => xy_in_ecrf.
      rewrite (bigD1_seq _ xy_in_ecrf) ?ecroots_uniq //=.
      rewrite eqxx mulr1 big1 ?addr0 //.
      by case=> i1 i2 /=; rewrite !eqE /= => /negbTE ->; rewrite mulr0.
  Qed.

  Lemma ecdivpC c: ecdivp (c%:P)%:E = 0.
  Proof.
    apply/eqP; apply/freeg_eqP => p.
    by rewrite coeff0 ecdivpE orderC.
  Qed.

  Lemma ecdivp0: ecdivp 0 = 0.
  Proof. by rewrite ecdivpC. Qed.

  Lemma ecdivpM (f g : ecpoly): f * g != 0 ->
    ecdivp (f * g) = (ecdivp f) + (ecdivp g).
  Proof.
    move=> nz_fg; apply/eqP; apply/freeg_eqP => p.
    rewrite coeffD !ecdivpE tofracM order_mul //.
    by rewrite -tofracM tofrac_eq0.
  Qed.

  Lemma ecdivp_prod (I : Type) (r : seq I) (F : I -> ecpoly):
       \prod_(i <- r) F i != 0
    -> ecdivp (\prod_(i <- r) F i) = \sum_(i <- r) (ecdivp (F i)).
  Proof.
    elim: r => [|r rs IH].
      by move=> _; rewrite !big_nil ecdivpC.
    rewrite !big_cons => nz_prod; rewrite ecdivpM ?IH //=.
    by move: nz_prod; rewrite mulf_eq0; case/norP.
  Qed.

  Lemma orderF_line (c x y : K): c != x ->
    order (('X - c%:P)%:E)%:F (|x, y|) = 0.
  Proof.
    move=> ne_cx; case oncve: (oncurve (|x, y|)); last first.
      by rewrite order_outcve ?oncve.
    apply/eqP/eval_eq0_orderP => //.
      by rewrite tofrac_eq0 ecX_eq0 polyXsubC_eq0.
    exists (x - c); first by rewrite subr_eq0 eq_sym.
    by rewrite eval_finF // ecevalE /= !hornerE.
  Qed.

  Lemma ecdivp_line (x y : K): oncurve (|x, y|) ->
      ecdivp ('X - x%:P)%:E
    = << (|x, y|) >> + << (|x, -y|) >> - << 2%:Z *g ∞ >>.
  Proof.
    move=> oncve; apply/eqP; apply/freeg_eqP => p.
    rewrite ecdivpE !(coeffD, coeffN, coeffU) !mul1r.
    case: p => [|p1 p2] /=.
      by rewrite !add0r mulr1 orderF_inf degree_pX size_XsubC.
    rewrite mulr0 subr0; case: (x =P p1) oncve => [->|]; last first.
      move/eqP=> ne_x_p1 _; rewrite !eqE /= (negbTE ne_x_p1) /= addr0.
      by rewrite orderF_line.
    move=> oncve; rewrite !eqE /= eqxx /=.
    case oncve_p: (oncurve (|p1, p2|)); last first.
      rewrite order_outcve ?oncve_p // !natz; apply/eqP.
      rewrite eqz_nat eq_sym addn_eq0 eqr_oppLR !eqb0 -negb_or.
      rewrite -eqr_sqr (eqP oncve) eq_sym; move: oncve_p.
      by move=> /= ->.
    move: oncve_p; rewrite /= -(eqP oncve); case: (y =P 0) oncve.
      move=> -> oncve; rewrite expr0n expf_eq0 /= => /eqP ->.
      rewrite oppr0 eqxx /= -PoszD /= addn1 orderS //.
      by rewrite Xpoly_oncurve.
    move=> /eqP; case: (-y =P p2); case: (y =P p2) => /=.
    + by move=> -> /esym /ecu_eq_oppr ->; rewrite !eqxx.
    + move=> _ /eqP; rewrite eqr_oppLR => /eqP ->.
      rewrite oppr_eq0 sqrrN => nz_p2 oncve _.
      by rewrite orderR ?add0r.
    + by move=> -> _ nz_p2 oncve _; rewrite orderR ?addr0.
    + move=> /eqP ne_y_p2 /eqP ne_yN_p2 _ _; rewrite eqr_sqr.
      by rewrite ![p2 == _]eq_sym (negbTE ne_y_p2) (negbTE ne_yN_p2).
  Qed.

  Local Notation ecdeg f := (deg (ecdivp f)).

  Lemma ecdeg0: ecdeg 0 = 0.
  Proof. by rewrite ecdivp0 deg0. Qed.

  Lemma ecdegC c: ecdeg (c%:P)%:E = 0.
  Proof. by rewrite ecdivpC deg0. Qed.

  Lemma ecdegM f g: f * g != 0 -> ecdeg (f * g) = (ecdeg f) + (ecdeg g).
  Proof. by move=> nz_fg; rewrite ecdivpM // degD. Qed.

  Lemma ecdeg_conjp f: ecdeg (conjp f) = ecdeg f.
  Proof.
    rewrite /ecdivp; unlock; rewrite !degD !raddf_sum /=.
    rewrite -order_conj /= conjF conjpK; congr (_ + _).
    rewrite (eq_big_perm _ (ecroots_conjp f)) /= big_map /=.
    apply: eq_bigr=> p _; rewrite -order_conj /= !degU.
    by rewrite conjF conjpK opprK.
  Qed.

  Lemma ecdeg_norm f:
    ecdeg ((normp f)%:E) = 2%:Z * (deg (ecdivp f)).
  Proof.
    case: (f =P 0) => [->|/eqP nz_f].
      by rewrite norm0 ecdeg0 mulr0.
    rewrite -[_%:E]conjp_normp ecdegM; last first.
      by rewrite mulf_neq0 ?conjp_eq0.
    by rewrite ecdeg_conjp mul2z.
  Qed.

  Hypothesis closed : GRing.ClosedField.axiom K.

  Local Notation clK := (ClosedFieldType K closed).

  Lemma ecdeg_eq0 f: ecdeg f = 0.
  Proof.
    case: (f =P 0) => [->|/eqP nz_f].
      by rewrite ecdeg0.
    apply: (@mulfI _ 2%:Z) => //; rewrite mulr0.
    rewrite -ecdeg_norm [normp _](@roots_factor_theorem_f clK).
    rewrite -mul_polyC ecXM ecdegM; last first.
      rewrite mulf_neq0 //.
      + by rewrite ecX_eq0 polyC_eq0 lead_coef_eq0 norm_eq0.
      + rewrite ecX_eq0 prodf_seq_neq0; apply/allP => c _.
        by apply/implyP => _; rewrite polyXsubC_eq0.
    rewrite ecdegC add0r; move: (rmorph_prod (ecX_rmorphism E)) => /= ->.
    rewrite ecdivp_prod; last first.
      rewrite prodf_seq_neq0; apply/allP=> c _; apply/implyP=> _.
      by rewrite ecX_eq0 polyXsubC_eq0.
    rewrite raddf_sum /= big_seq big1 // => x x_root.
    pose y := sqrt (Xpoly.[x]); have oncve: (oncurve (|x, y|)).
      by rewrite /= {}/y (@sqr_sqrt clK) -horner_Xpoly.
    rewrite (ecdivp_line oncve) !(raddfB, raddfD) /= !degU.
    by rewrite -PoszD subrr.
  Qed.

  (* ------------------------------------------------------------------ *)
  Definition ecdiv_r (f : {ratio ecpoly}) :=
    if \n_f == 0 then 0 else (ecdivp \n_f) - (ecdivp \d_f).

  Definition ecdiv :=
    lift_fun1 {fraction ecpoly} ecdiv_r.

  Lemma pi_ecdiv: {mono \pi_{fraction ecpoly} : f / ecdiv_r f >-> ecdiv f}.
  Proof.
    move=> f2; unlock ecdiv; set f1 := (repr _).
    have: (f1 = f2 %[mod {fraction _}]) by rewrite reprK.
    case: f2 f1 => [[n2 d2] /= nz_d2] [[n1 d1] /= nz_d1] /=.
    move/eqmodP => /=; rewrite FracField.equivfE /= => /eqP eqr.
    apply/eqP; rewrite /ecdiv_r /=.
    move/eqP: eqr;
      have [->|nz_n1] := eqVneq n1 0;
      have [->|nz_n2] := eqVneq n2 0;
        rewrite ?eqxx //.
    * by rewrite eq_sym mul0r mulf_eq0; case/norP.
    * by rewrite mulr0 mulf_eq0; case/norP.
    move/eqP=> eqr; rewrite (negbTE nz_n1) (negbTE nz_n2).
    by rewrite addr_cross -!ecdivpM ?eqr ?[d1 * n2]mulrC // mulf_neq0.
  Qed.

  Canonical ecdiv_morph := PiMono1 (pi_ecdiv).

  Import fracfield.FracField.

  Lemma ecdiv0: ecdiv 0 = 0.
  Proof.
    rewrite !piE /Ratio /insubd insubT ?oner_eq0 //=.
    by rewrite /ecdiv_r /= eqxx.
  Qed.

  Lemma ecdivE (n d : ecpoly): n * d != 0 ->
    ecdiv (n // d) = (ecdivp n) - (ecdivp d).
  Proof.
    rewrite mulf_eq0 => /norP [nz_n nz_d]; rewrite embed_Ratio !piE.
    rewrite /Ratio /insubd insubT /= /ecdiv_r /=.
    by rewrite (negbTE nz_n).
  Qed.

  Lemma ecdivC c: ecdiv ((c%:P)%:E)%:F = 0.
  Proof.
    have [->|nz_c] := eqVneq c 0; first by rewrite ecdiv0.
    rewrite -[_%:F]divr1 -[1]tofrac1 ecdivE; last first.
      by rewrite mulf_neq0 ?oner_eq0 // ecX_eq0 polyC_eq0.
    by rewrite !ecdivpC subrr.
  Qed.

  Lemma ecdiv_coeffE (f : {fraction ecpoly}) p:
    coeff p (ecdiv f) = order f p.
  Proof.
    elim/FracField.fracW: f => n d nz_d.
    case: (n =P 0) => [->|/eqP nz_n].
      by rewrite mul0r ecdiv0 coeff0 order0.
    rewrite ecdivE ?mulf_neq0 // coeffB !ecdivpE.
    by rewrite orderE // -!orderF.
  Qed.

  Lemma ecdivF f: ecdiv f%:F = ecdivp f.
  Proof.
    have [->|nz_f] := eqVneq f 0; first by rewrite ecdiv0 ecdivp0.
    rewrite -[f%:F]divr1 -[1]tofrac1 ecdivE; last first.
      by rewrite mulf_neq0 // oner_eq0.
    by rewrite ecdivpC subr0.
  Qed.

  Lemma ecdivM (f g : {fraction ecpoly}): f * g != 0 ->
    ecdiv (f * g) = (ecdiv f) + (ecdiv g).
  Proof.
    move=> nz_fg; apply/eqP; apply/freeg_eqP => p.
    by rewrite coeffD !ecdiv_coeffE order_mul.
  Qed.

  Lemma ecdiv_prod (I : Type) (r : seq I) (F : I -> {fraction ecpoly}) (P : pred I):
       \prod_(i <- r | P i) F i != 0
    -> ecdiv (\prod_(i <- r | P i) F i) = \sum_(i <- r | P i) (ecdiv (F i)).
  Proof.
    elim: r => [|i r IH]; first by rewrite !big_nil ecdivC.
    rewrite !big_cons; case: (P i) => nz; last by rewrite IH.
    move: nz; rewrite mulf_eq0 => /norP [nz_Fi nz].
    by rewrite ecdivM ?mulf_neq0 // IH.
  Qed.

  Lemma ecdivX (f : {fraction ecpoly}) n:
    ecdiv (f ^+ n) = (ecdiv f) *+ n.
  Proof.
    have [->|nz_f] := eqVneq f 0.
      rewrite expr0n ecdiv0 mul0rn.
      by case: (n == 0)%N; rewrite ecdivC.
    elim: n => [|n IH].
      by rewrite expr0 mulr0n ecdivC.
    rewrite exprS ecdivM; last first.
      by rewrite mulf_neq0 ?expf_neq0.
    by rewrite IH mulrS.
  Qed.

  Lemma ecdivV (f : {fraction ecpoly}):
    ecdiv (f^-1) = - (ecdiv f).
  Proof.
    apply/eqP; apply/freeg_eqP=> p.
    by rewrite coeffN !ecdiv_coeffE order_inv.
  Qed.

  Lemma ecdivXz (f : {fraction ecpoly}) z:
    ecdiv (f ^ z) = (ecdiv f) *~ z.
  Proof.
    case: z => n.
    + by rewrite ecdivX.
    + by rewrite NegzE /= -exprnN ecdivV ecdivX.
  Qed.

  Lemma ecdiv_eq0 (f : {fraction ecpoly}): deg (ecdiv f) = 0.
  Proof.
    elim/fracW: f => n d nz_d; have [->|nz_n] := eqVneq n 0.
      by rewrite mul0r ecdiv0 deg0.
    by rewrite ecdivE ?mulf_neq0 // degB !ecdeg_eq0 subrr.
  Qed.

  Lemma mem_negdiv R (f :{fraction ecpoly}):
    (R \in dom (fgneg (ecdiv f))) = (order f R < 0).
  Proof.
    rewrite mem_dom inE coeff_fgnegE oppr_eq0 eqr_minl.
    by rewrite -ltrNge ecdiv_coeffE.
  Qed.

  Lemma mem_posdiv R (f : {fraction ecpoly}):
    (R \in dom (fgpos (ecdiv f))) = (order f R > 0).
  Proof.
    rewrite mem_dom inE coeff_fgposE eqr_maxl.
    by rewrite -ltrNge ecdiv_coeffE.
  Qed.


  (* -------------------------------------------------------------------- *)
  Lemma deg_ecdiv_eq0 (f : {fraction ecpoly}): deg (ecdiv f) = 0.
  Proof.
    have [->|] := eqVneq f 0; first by rewrite ecdiv0 deg0.
    elim/fracW: f => n d _; rewrite mulf_eq0 invr_eq0 !tofrac_eq0.
    case/norP=> nz_n nz_d; rewrite ecdivE ?mulf_neq0 //.
    by rewrite degB !ecdeg_eq0.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma div_sumE (D : {freeg point K}):
    D = << coeff ∞ D *g ∞ >> + \sum_(z <- dom D | z != ∞) << coeff z D *g z >>.
  Proof.
    rewrite -{1}[D]freeg_sumE; case i_in_D: (∞ \in dom D).
      by rewrite (bigD1_seq ∞) ?uniq_dom.
    rewrite coeff_outdom ?i_in_D // freegU0 add0r.
    rewrite -[X in _ = X]big_filter; set d := [seq _ <- _ | _].
    have ->//: d = dom D; rewrite {}/d.
    rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
    move=> z zD /=; apply/negP=> /eqP zi; move: zD.
    by rewrite zi i_in_D.
  Qed.

  Lemma ecdiv_sumE (f : {fraction ecpoly}):
    ecdiv f = \sum_(z <- dom (ecdiv f)) << order f z *g z >>.
  Proof.
    rewrite -{1}[ecdiv _]freeg_sumE; apply: eq_bigr.
    by move=> p _; rewrite ecdiv_coeffE.
  Qed.

  Lemma ecdiv_degE (f : {fraction ecpoly}):
    deg (ecdiv f) = \sum_(R <- dom (ecdiv f)) order f R.
  Proof.
    rewrite -{1}[ecdiv _]freeg_sumE raddf_sum /=.
    by apply: eq_bigr => p _; rewrite degU ecdiv_coeffE.
  Qed.

  Section DivIndDom.
    Variable P : {freeg (point K)} -> Prop.

    Hypothesis H0: forall k, P << k *g ∞ >>.
    Hypothesis HS:
      forall k p D, p \notin dom D -> k != 0 -> p != ∞ ->
        P D -> P (<< k *g p >> + D).

    Lemma div_ind_dom D: P D.
    Proof.
      apply: (@freeg_ind_dom _ _ (pred1 (∞ : point K))) => {D}; last first.
        by move=> k p D /= p_notin_D nz_k nz_p PD; apply: HS.
      move=> D domD; rewrite {1}[D]div_sumE -big_filter.
      set s := [seq _ <- _ | _]; have ->: s = [::]; last first.
        by rewrite big_nil addr0; apply: H0.
      rewrite {}/s; case sE: [seq _ <- _ | _] => [//|x xs].
      have: x \in x :: xs by rewrite in_cons eqxx.
      rewrite -sE mem_filter andbC; move/(_ x): domD.
      by rewrite !inE => ->.
    Qed.
  End DivIndDom.

  (* -------------------------------------------------------------------- *)
  Local Notation PEF       := (@tofrac _ \o ((ecX E) \o polyC)).
  Local Notation "x %:PEF" := (PEF x) (at level 2).
  Local Notation "'Y"      := [ecp 1 *Y + 0].

  Lemma Necdiv_transE (f : {fraction ecpoly}) (c : K):
    fgneg (ecdiv (f + c%:PEF)) = fgneg (ecdiv f).
  Proof.
    have h:
      forall (f : {fraction ecpoly}) (c : K) p,
        order f p < 0 -> order f p = order (f + c%:PEF) p.
    + move=> {f c} f c p; case oncve: (oncurve p); last first.
        by rewrite order_outcve // oncve.
      have [->|nz_c] := eqVneq c 0; first by rewrite /= addr0.
      have [->|nz_f] := eqVneq f 0; first by rewrite order0.
      pose n := (decomp f p).1; have nz_n: n != 0 by apply: decomp_nz_num.
      pose d := (decomp f p).2; have nz_d: d != 0 by apply: decomp_nz_den.
      pose o := order f p; pose u := unifun E p.
      have:= (decomp_correct nz_f oncve); rewrite -/u -{1}/o -/n -/d => uok.
      have: f + c%:PEF = (u ^ o * ((n%:F + u^(-o) * (c%:PEF * d%:F)) / d%:F)).
        rewrite mulrA mulrDr mulrA -expfzDr ?unifun_neq0 //.
        rewrite subrr expr0z mul1r mulrDl -!mulrA divff ?tofrac_eq0 //.
        by rewrite mulr1 (uniok_decomp uok).
      set g := (_ / _); have [->|nz_g] := eqVneq g 0.
        move/eqP; rewrite mulr0 addr_eq0 => /eqP {1}->.
        by rewrite order_opp orderC.
      move=> eq; rewrite eq order_mul; last first.
        by rewrite mulf_neq0 // expfz_neq0 // unifun_neq0.
      rewrite order_expz; move: (uniformizer_unifun oncve).
      rewrite /uniformizer -{2}/o => /eqP ->; rewrite intz.
      move=> ordf_lt0; apply/eqP; rewrite addrC -subr_eq.
      rewrite subrr eq_sym; move: {eq} nz_g; rewrite {}/g -[-o]ltz0_abs //.
      move: n d nz_n nz_d uok => n d nz_n nz_d; rewrite {}/u.
      move: (erefl o); rewrite {2}/o => oE.
      case: p oncve o oE ordf_lt0 => [|x y] oncve o oE ordf_lt0 /= uok.
      + set r := (_ + _); have ->: r =
            (n * 'Y^+`|o| + 'X%:E^+`|o| * (c%:P%:E) * d) // 'Y^+`|o|.
          rewrite {}/r -!exprnP divf_exp mulrAC mulrA -!(tofracX, tofracM).
          rewrite -{1}[n%:F]divr1 -[1]tofrac1 addf_div; first last.
          * by rewrite tofrac_eq0 expf_neq0 // ecY_neq0.
          * by rewrite oner_eq0.
          by rewrite !(mul1r, mulr1) -!(tofracX, tofracM, tofracD).
        rewrite -![_ / d%:F]mulrA -invfM -tofracM.
        rewrite mulf_eq0 {1}invr_eq0 2!tofrac_eq0; case/norP => [nz1 nz2].
        rewrite orderE //= /poly_order /= (negbTE nz1) (negbTE nz2) /=.
        rewrite subr_eq0; apply/eqP; congr (- _); congr (_.-1).
        rewrite degree_addl; last first.
          pose neq0 := (mulf_neq0, expf_neq0, ecX_neq0, ecY_neq0, ecX_eq0, polyC_eq0).
          rewrite [n*_]mulrC !degree_mul_id ?neq0 // => {neq0}.
          rewrite degreeC // (uniok_inf_degeq uok).
          rewrite !(degree_expX, degree_expY) addn1 /= ltn_add2r.
          by rewrite ltn_mul2r oE absz_gt0 neqr_lt ordf_lt0.
        rewrite mulrC !degree_mul_id ?(mulf_neq0, expf_neq0, ecY_neq0) //.
        by rewrite (uniok_inf_degeq uok).
      + rewrite -!exprnP -!(tofracX, tofracM, tofracD) => nz.
        apply/eval_eq0_orderP => //; rewrite evalE_fin_ord_ge0 //; last first.
          by apply (uniok_fin_den_eval_neq0 uok).
        set v1 := (_ + _); exists (v1.[x, y] / d.[x, y]) => //.
        rewrite mulf_eq0 invr_eq0 negb_or (uniok_fin_den_eval_neq0 uok) andbT.
        rewrite /v1 !(eceval_add, eceval_mul, eceval_exp) //.
        rewrite eceval_unifun_fin expr0n oE absz_eq0 eqr_le.
        rewrite [0 <= _]lerNgt ordf_lt0 andbF mul0r addr0.
        by rewrite (uniok_fin_num_eval_neq0 uok).
    apply/eqP/freeg_eqP=> R; rewrite !coeff_fgnegE !ecdiv_coeffE.
    have [oncve_R|outcve_R] := (boolP (oncurve R)); last first.
      by rewrite !order_outcve.
    case: (ltrP (order f R) 0); first by move/(h _ c) => <-.
    move=> ge0_ordfR; have/eval_ge0_orderP [x evalhR] := ge0_ordfR.
    have: (0 <= order (f + c%:PEF) R).
      apply/eval_ge0_orderP; exists ((evalK R f) + c).
      by rewrite evalDr evalC // /evalK evalhR.
    by move=> ge0_ordfDcR; rewrite !minr_l.
  Qed.

  (* ------------------------------------------------------------------ *)
  Definition ecdeqv D1 D2 :=
    (exists f : {fraction ecpoly}, ecdiv f = D1 - D2).

  Local Notation "D1 :~: D2" := (ecdeqv D1 D2).

  Lemma ecdeqv_refl D: D :~: D.
  Proof. by rewrite /ecdeqv; exists 0; rewrite ecdiv0 subrr. Qed.

  Lemma ecdeqv_sym D1 D2: D1 :~: D2 -> D2 :~: D1.
  Proof.
    by case=> f divf; exists (f^-1); rewrite ecdivV divf opprB.
  Qed.

  Lemma ecdeqv_trans D1 D2 D3: D1 :~: D2 -> D2 :~: D3 -> D1 :~: D3.
  Proof.
    move=> [f1 divf1] [f2 divf2].
    case: (f1 =P 0) divf1 => [-> /eqP|/eqP nz_f1 divf1].
      by rewrite ecdiv0 eq_sym subr_eq0 => /eqP->; exists f2.
    case: (f2 =P 0) divf2 => [-> /eqP|/eqP nz_f2 divf2].
      by rewrite ecdiv0 eq_sym subr_eq0 => /eqP<-; exists f1.
    exists (f1 * f2); rewrite ecdivM ?mulf_neq0 //.
    rewrite divf1 divf2 addrC addrCA [X in _ + X]addrAC.
    by rewrite subrr add0r.
  Qed.

  Lemma ecdeqv_opp D1 D2: D1 :~: D2 -> -D1 :~: -D2.
  Proof.
    by case=> [f divf]; exists (f^-1); rewrite ecdivV -opprD divf.
  Qed.

  Lemma ecdeqv_oppI D1 D2: -D1 :~: -D2 -> D1 :~: D2.
  Proof.
    case=> [f divf]; exists (f^-1).
    by rewrite ecdivV divf opprD !opprK.
  Qed.

  Lemma ecdeqv_addl D1 D1' D2:
    D1 :~: D1' -> (D1 + D2) :~: (D1' + D2).
  Proof.
    case=> [f1 divf1]; exists f1.
    by rewrite -addrA opprD [D2 + _]addrCA subrr addr0.
  Qed.

  Lemma ecdeqv_addIl D1 D1' D2:
    (D1 + D2) :~: (D1' + D2) -> D1 :~: D1'.
  Proof.
    case=> [f1 divf1]; exists f1; rewrite divf1.
    by rewrite -addrA opprD [D2 + _]addrCA subrr addr0.
  Qed.

  Lemma ecdeqv_addr D1 D2 D2':
    D2 :~: D2' -> (D1 + D2) :~: (D1 + D2').
  Proof.
    by move=> eqv_D2; rewrite ![D1 + _]addrC; apply: ecdeqv_addl.
  Qed.

  Lemma ecdeqv_addIr D1 D2 D2':
    (D1 + D2) :~: (D1 + D2') -> D2 :~: D2'.
  Proof. by rewrite ![D1 + _]addrC => /ecdeqv_addIl. Qed.

  Lemma ecdeqv_add D1 D1' D2 D2':
    D1 :~: D1' -> D2 :~: D2' -> (D1 + D2) :~: (D1' + D2').
  Proof.
    move=> eqvD1 eqvD2; apply: (@ecdeqv_trans _ (D1 + D2')).
    + by apply: ecdeqv_addr. + by apply: ecdeqv_addl.
  Qed.

  Lemma ecdeqv_sub D1 D1' D2 D2':
    D1 :~: D1' -> D2 :~: D2' -> (D1 - D2) :~: (D1' - D2').
  Proof.
    by move=> eqvD1 eqvD2; apply: ecdeqv_add => //; apply: ecdeqv_opp.
  Qed.

  Lemma ecdeqv_deg D1 D2: D1 :~: D2 -> deg D1 = deg D2.
  Proof.
    case=> f /esym/eqP; rewrite subr_eq => /eqP->.
    by rewrite degD ecdiv_eq0 ?add0r.
  Qed.

  Lemma ecdeqv_lineS (p : point K):
    oncurve p -> (<<p>> + <<\- p>> - << 2%:Z *g ∞ >>) :~: 0.
  Proof.
    case: p=> [|x y] oncve /=.
    + by rewrite freegUD freegUB freegU0; apply ecdeqv_refl.
    + move/ecdivp_line: oncve; set f := (ecX _ _) => divf.
      by exists f%:F; rewrite subr0 ecdivF divf.
  Qed.

  (* ------------------------------------------------------------------ *)
  Definition ecnorm (D : {freeg point K}) := deg (fgnorm D) - `|coeff ∞ D|.

  Lemma ecnormE D: ecnorm D = \sum_(z <- dom D | z != ∞) `|coeff z D|.
  Proof.
    rewrite /ecnorm fgnormE raddf_sum /=; case iD: (∞ \in dom D).
    + rewrite (bigD1_seq ∞) ?uniq_dom //= degU addrAC.
      by rewrite subrr add0r; apply: eq_bigr=> i _; rewrite degU.
    + rewrite -[X in _ = X]big_filter; set d := [seq _ <- _ | _].
      rewrite coeff_outdom ?iD // normr0 subr0.
      have ->: d = dom D; last by apply: eq_bigr=> i _; rewrite degU.
      rewrite {}/d (eq_in_filter (a2 := predT)) ?filter_predT //.
      move=> z zD /=; apply/negP=> /eqP zi; move: zD.
      by rewrite zi iD.
  Qed.

  Lemma ecnorm0: ecnorm 0 = 0.
  Proof. by rewrite ecnormE dom0 big_nil. Qed.

  Lemma ecnormU k p: ecnorm << k *g p >> = `|k| * (p != ∞).
  Proof.
    case: (k =P 0) => [->|/eqP k_neq0].
      by rewrite freegU0 ecnorm0 normr0 mul0r.
    rewrite ecnormE domU // big_cons big_nil.
    case: (p != ∞); rewrite (mulr0, mulr1) // addr0.
    by rewrite coeffU eqxx mulr1.
  Qed.

  Lemma ecnormD (D1 D2 : {freeg (point K)}):
       [predI (dom D1) & (dom D2)] =1 pred0
    -> ecnorm (D1 + D2) = ecnorm D1 + ecnorm D2.
  Proof.
    move=> D12_nI; have/domD_perm_eq dom_permeq := D12_nI.
    have inD1E p: p \in dom D1 -> p \notin dom D2.
      move=> p_in_D1; move/(_ p): D12_nI; rewrite !inE p_in_D1.
      by rewrite andTb => /= ->.
    have inD2E p: p \in dom D2 -> p \notin dom D1.
      move=> p_in_D2; move/(_ p): D12_nI; rewrite !inE p_in_D2.
      by rewrite andbT => /= ->.
    rewrite ecnormE (eq_big_perm _ dom_permeq) /=.
    rewrite big_cat /= big_seq_cond [X in _ + X]big_seq_cond.
    rewrite (eq_bigr (fun p => `|coeff p D1| )); last first.
      move=> p /andP [/inD1E p_notin_D2 _]; rewrite coeffD.
      by rewrite [X in _ + X]coeff_outdom // addr0.
    rewrite [X in _ + X](eq_bigr (fun p => `|coeff p D2| )); last first.
      move=> p /andP [/inD2E p_notin_D1 _]; rewrite coeffD.
      by rewrite [X in X + _]coeff_outdom // add0r.
    by rewrite -!big_seq_cond -!ecnormE.
  Qed.

  Lemma ecnorm_ge0 D: 0 <= ecnorm D.
  Proof. by rewrite ecnormE; apply: sumr_ge0=> i _; rewrite normrE. Qed.


  Lemma norm_eq0P(D : {freeg (point K)}):
    ecnorm D = 0 -> D = << deg D *g ∞ >>.
  Proof.
    move=> nmD_eq0; have: D = << coeff ∞ D *g ∞ >>.
      rewrite {1}[D]div_sumE -[X in _ = X]addr0; congr (_ + _).
      rewrite big_seq_cond big1 // => p /andP [p_in_D nz_p].
      move/eqP: nmD_eq0; rewrite ecnormE psumr_eq0; last first.
        by move=> i _; rewrite normrE.
      move/allP/(_ p p_in_D)/implyP/(_ nz_p); rewrite normr_eq0.
      by move/eqP=> ->; rewrite freegU0.
    by move=> ED; rewrite ED degU.
  Qed.

  Lemma norm_eq1P (D : {freeg (point K)}):
    ecnorm D = 1 ->
      exists2 p, (p != ∞) &
        exists b : bool, exists n,
          D = << p >> *~ ((-1) ^+ b) + << n *g ∞ >>.
  Proof.
    move=> nD_eq1; have: forall p, p != ∞ -> `|coeff p D| <= 1.
      move=> p nz_p; rewrite lerNgt; apply/negP => NDp_gt1.
      move: nD_eq1; rewrite ecnormE (big_rem p) /=; last first.
        by rewrite mem_dom inE -normr_eq0 neqr_lt (ltr_trans ltr01).
      move/eqP; rewrite nz_p eqr_le => /andP [h _]; move: h.
      set s := \sum_(_ <- _ | _) _; have: 0 <= s.
        by apply/sumr_ge0=> i _; rewrite normr_ge0.
      by move/(ltr_le_add NDp_gt1); rewrite addr0 ltrNge=> /negbTE->.
    move=> NDp_le1; move: nD_eq1; rewrite ecnormE -big_filter.
    rewrite {3}[D]div_sumE -[X in _ + X]big_filter; set s := [seq _ <- _ | _].
    case sE: s => [|p ps]; first by rewrite big_nil.
    have: p \in s by rewrite sE inE eqxx.
    rewrite /s mem_filter=> /andP [nz_p p_in_D].
    rewrite !big_cons; have cpD: `|coeff p D| = 1.
      apply/eqP; rewrite eqr_le NDp_le1 ?andTb //.
      by have := p_in_D; rewrite -gtz0_ge1 normrE mem_dom inE.
    rewrite cpD -{2}[1]addr0 => /addrI=> sum_ps_eq0; exists p=> //.
    exists (coeff p D < 0); exists (coeff ∞ D); rewrite addrC.
    congr (_ + _); rewrite freegU_mulz -[X in _ = X]addr0.
    congr (_ + _); last first.
      rewrite big_seq big1 // => i i_in_ps; apply/eqP.
      rewrite freegU_eq0; move/eqP: sum_ps_eq0.
      rewrite psumr_eq0; last by move=> ? _; rewrite normrE.
      by move/allP/(_ i i_in_ps)/implyP; rewrite normr_eq0; apply.
    by rewrite -{1}[coeff p D]mulr_sign_norm cpD mulr1 intz.
  Qed.

  Lemma norm_eq1P_deg (D : {freeg (point K)}):
    ecnorm D = 1 ->
      exists2 p, (p != ∞) &
        exists b : bool,
          D = << p >> *~ ((-1) ^+ b) + << (deg D) - (-1) ^+ b *g ∞ >>.
  Proof.
    move/norm_eq1P; case=> p nz_p [b [n DE]]; exists p=> //; exists b.
    have/(congr1 (@deg _)) := DE; rewrite degD raddfMz /= !degU.
    by move=> ->; rewrite addrAC intr_sign subrr add0r.
  Qed.
End ECDiv.
