(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq.
From mathcomp Require Import fintype choice tuple perm zmodp ssrfun.
From mathcomp Require Import bigop ssralg ssrint order ssrnum generic_quotient.

Require Import xseq xmatrix polyall polydec polyfrac.
Require Import fraction fracfield SsrMultinomials.freeg.
Require Import ec ecpoly eceval ecorder ecdiv eceval.

(* -------------------------------------------------------------------- *)
Import GRing.Theory.
Import Num.Theory.
Import Order.POrderTheory.
Import Order.TotalTheory.
Import fraction.FracField.
Import fracfield.FracField.
Import FracInterp.
Import PreClosedField.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Reserved Notation "p \PFo f" (at level 50).
Reserved Notation "f \Fo g"  (at level 50).

Section FracECPoly.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ecX E p).

  Hypothesis closedK : GRing.ClosedField.axiom K.

  Local Notation clK := (ClosedFieldType K closedK).

  Local Notation PEF := (@tofrac _ \o ((ecX _) \o polyC)).
  Local Notation "x %:PEF" := (PEF x) (at level 2).

  Declare Scope G.
  Delimit Scope G with G.

  Local Notation "\- x"   := (@ECGroup.neg _ x)     : G.
  Local Notation "x \+ y" := (@ECGroup.add _ E x y) : G.
  Local Notation "x \- y" := (x \+ (\- y))%G        : G.

  Local Notation neq0 := (mulf_neq0, invr_eq0, ecX_eq0, tofrac_eq0, conjp_eq0).

  Local Hint Extern 0 (is_true (ec.Xpoly _ != 0)) => exact: XpolyN0 : core.

  Definition proportional (p q : ecpoly) :=
    [&& (p.1 %= q.1), (p.2 %= q.2) &
      (lead_coef p.1 * lead_coef q.2 == lead_coef p.2 * lead_coef q.1)].

  Lemma pptnle0 p: (proportional p 0) = (p == 0).
  Proof.
    rewrite /proportional /= lead_coef0 !mulr0 eqxx andbT.
    by case: p => [[p1 p2]] /=; apply/esym; rewrite !eqp0 eqE /=.
  Qed.

  Lemma pptnlC: commutative proportional.
  Proof.
    move=> p q; rewrite /proportional; congr ([&& _, _ & _]);
      last 1 [idtac] || by rewrite /eqp andbC.
    by rewrite eq_sym mulrC [X in _ = (_ == X)]mulrC.
  Qed.

  Lemma pptnl0e p: (proportional 0 p) = (p == 0).
  Proof. by rewrite pptnlC pptnle0. Qed.

  Lemma eqpfP (p q : {poly K}):
    p %= q -> (lead_coef q) *: p = (lead_coef p) *: q.
  Proof.
    have [->|nz_q] := eqVneq q 0.
      by rewrite eqp0 => /eqP ->.
    move/eqpfP=> ->; rewrite lead_coefZ scalerA.
    by rewrite mulrCA -mulrA [_ ^-1 * _]mulrC.
  Qed.

  Lemma pptnlrP (p q : ecpoly):
    reflect (exists2 c, (c.1 != 0) && (c.2 != 0)
                      & ((c.1%:P)%:E) * p = ((c.2%:P)%:E) * q)
            (proportional p q).
  Proof.
    case: p q => [[p1 p2]] [[q1 q2]] /=; apply: (iffP idP).
    + case/and3P=> /=; have [->|nz_q1] := (eqVneq q1 0).
        rewrite eqp0 => /eqP->; have [->|nz_q2] := eqVneq q2 0.
          by rewrite eqp0 => /eqP-> _; exists (1, 1) => //=; rewrite oner_eq0.
        case/eqpP=> c nz_c pp_p2_q2 _; exists c => //.
        by rewrite -!ecXM !mul_polyC pp_p2_q2.
      have [->|nz_p1] := (eqVneq p1 0); first by rewrite eqp_sym eqp0 (negbTE nz_q1).
      case/eqpP=> c /andP [nz_c1 nz_c2] pp_p1_q1; have [->|nz_q2] := eqVneq q2 0.
        rewrite eqp0 => /eqP-> _; exists c; first by rewrite nz_c1 nz_c2.
        rewrite ![_%:E * _]mulrC !ecY_ecX_mul ![_*_%:P]mulrC.
        by rewrite !mul_polyC pp_p1_q1.
      have [->|nz_p2] := (eqVneq p2 0); first by rewrite eqp_sym eqp0 (negbTE nz_q2).
      case/eqpP=> c' /andP [nz_c'1 nz_c'2] pp_p2_q2 /eqP eq_lc.
      exists (c.1, c.2) => //=; first by apply/andP; split.
      rewrite !mulE /dotp /= !simpm; apply/eqP; do 2! rewrite eqE /=.
      have/(congr1 (( *%R ) (c'.1 *: p2))) := pp_p1_q1; rewrite {1}pp_p2_q2.
      move/(congr1 lead_coef); rewrite !lead_coefM !lead_coefZ.
      rewrite [X in X = _]mulf_cross [X in _ = X]mulf_cross.
      rewrite -eq_lc [lead_coef p1 * _]mulrC => /mulIf.
      rewrite mulf_neq0 ?lead_coef_eq0 // => /(_ (erefl true)) => eq_c.
      rewrite !mul_polyC pp_p1_q1 eqxx /=; apply/eqP.
      apply/(scalerI (a := c'.1)) => //; rewrite scalerA [_*c.1]mulrC.
      by rewrite -scalerA pp_p2_q2 !scalerA [c.1*_]mulrC eq_c.
    + case=> [[c1 c2]] /= /andP [nz_c1 nz_c2]; rewrite !mulE /dotp /= !simpm.
      case=> eq1 eq2; apply/and3P; split=> /=.
      * apply/eqpP; exists (c1, c2); first by rewrite nz_c1 nz_c2.
        by rewrite -!mul_polyC /= eq1.
      * apply/eqpP; exists (c1, c2); first by rewrite nz_c1 nz_c2.
        by rewrite -!mul_polyC /= eq2.
      apply/eqP; apply/(mulfI (x := c1 * c2)); first by rewrite mulf_neq0.
      rewrite [X in X = _]mulf_cross [X in _ = X]mulf_cross.
      rewrite -2!lead_coefZ -!mul_polyC eq1 -eq2.
      by rewrite !mul_polyC !lead_coefZ [X in X = _]mulrC.
   Qed.

   Lemma pptnlP (p q : ecpoly):
     reflect (exists2 c, c != 0 & p = ((c%:P)%:E) * q)
             (proportional p q).
   Proof.
     apply: (iffP idP).
     + move/pptnlrP=> [[c1 c2] /= /andP [nz_c1 nz_c2]] eq; exists (c2 / c1).
       * by rewrite mulf_neq0 // invr_eq0.
       * apply/(@mulfI _ (c1%:P)%:E); first by rewrite ecX_eq0 polyC_eq0.
         rewrite mulrCA mulrA -ecXM -polyCM [_ * c1]mulrAC -mulrA.
         by rewrite divff // mulr1 eq.
     + case=> c nz_c ->; apply/and3P; rewrite mulE /dotp /= !simpm; split.
       * apply/eqpP; exists (1, c) => /=; first by rewrite oner_eq0.
         by rewrite scale1r mul_polyC.
       * apply/eqpP; exists (1, c) => /=; first by rewrite oner_eq0.
         by rewrite scale1r mul_polyC.
       * by rewrite !lead_coefM mulrAC.
    Qed.

   Definition constant_ratio (h : {ratio ecpoly}) :=
     (\n_h == 0) || (proportional \n_h \d_h).

   Definition constant_fraction (h : {fraction ecpoly}) :=
     (lift_fun1 {fraction ecpoly} constant_ratio h).

   Lemma pi_constant_fraction :
     {mono \pi_({fraction ecpoly})%qT : f /
       constant_ratio f >-> constant_fraction f}.
   Proof.
     move=> f; unlock constant_fraction; set g := (repr _).
     have: (g = f %[mod {fraction ecpoly}])%qT.
     + by rewrite reprK.
     case: f g => [[nf df] /= nz_df] [[ng dg] /= nz_dg] /=.
     move/eqmodP => /=; rewrite FracField.equivfE /= => eqE.
     rewrite /constant_ratio /= .

     move: eqE; case: (ng =P 0) => [|/eqP nz_ng] /=.
     + move=> -> /=; rewrite mul0r eq_sym mulf_eq0.
       by rewrite (negbTE nz_dg) /= => ->.
     case: (nf =P 0) => [->|/eqP nz_nf].
     + by rewrite mulr0 mulf_eq0 (negbTE nz_ng) (negbTE nz_df).

     move=> eqE; apply/pptnlP/pptnlP.

     case=> c1 nz_c1 eq.
     exists c1; move=> //.
     move: eqE ; rewrite eq.
     rewrite mulrAC mulrC -subr_eq0 -mulrBr.
     move/eqP => H.
     have hypothesis : (c1%:P)%:E * df - nf == 0.
     by move/idomainAxiom : H; rewrite (negbTE nz_dg) //.
     symmetry; apply /eqP; by rewrite -subr_eq0.

     case=> c1 nz_c1 eq.
     exists c1; move=> //.
     move: eqE; rewrite eq mulrA -subr_eq0 -mulrBl.
     move/eqP => H.
     have hypothesis : ng - dg * (c1%:P)%:E == 0.
     by move/idomainAxiom : H; rewrite (negbTE nz_df) Bool.orb_false_r.
     by apply /eqP; rewrite -subr_eq0 mulrC.
   Qed.

   Local Open Scope quotient_scope.

   Canonical pi_constant_fraction_morph := PiMono1 pi_constant_fraction.

   Lemma constant_fractionP (f: {fraction ecpoly}):
     reflect
       (exists c, f = ((c%:P)%:E)%:F)
       (constant_fraction f).
   Proof.
     apply: (iffP idP); elim/quotW: f => f;
       rewrite !piE; case: f => [[n d] /= nz_d];
       rewrite /constant_ratio /=.
     + case/orP => [/eqP->|].
       * exists 0; rewrite !piE; apply/eqmodP; rewrite /= equivfE /=.
         by rewrite !numden_Ratio ?oner_eq0 // !simpm.
       move/pptnlP => [c nz_c En]; exists c.
       rewrite !piE; apply/eqmodP=> /=; rewrite equivfE /=.
       by rewrite !numden_Ratio ?oner_eq0 // mulr1 mulrC En.
     + case=> c; rewrite !piE => /eqmodP /=; rewrite equivfE /=.
       rewrite !numden_Ratio ?oner_eq0 // mulr1 => /eqP ->.
       rewrite mulf_eq0 (negbTE nz_d) /=; case: (c =P 0).
       * by move=> ->; rewrite eqxx.
       move/eqP=> nz_c; apply/orP; right; apply/pptnlP.
       by exists c=> //; rewrite mulrC.
   Qed.

  (* ================================================================== *)
  Lemma constant_fraction_order0 :
  forall (f : {fraction ecpoly}) (P : point K),
  order f P != 0 -> ~~ (constant_fraction f).
  Proof.
  move=> f P ordP_nz.
  apply/constant_fractionP; case=> c H.
  move: (orderC E c P); rewrite -H; move=> h.
  move:ordP_nz; by rewrite h.
  Qed.

  Lemma constant_fraction0: constant_fraction 0.
  Proof. by apply/constant_fractionP; exists 0. Qed.

  Lemma constant_fractionC c: constant_fraction c%:PEF.
  Proof. by apply/constant_fractionP; exists c. Qed.

  Lemma fctt_shift (f : {fraction ecpoly}) (c : K):
    (constant_fraction (f - c%:PEF)) = (constant_fraction f).
  Proof.
    apply/constant_fractionP/constant_fractionP.
    + case=> fc /eqP; rewrite subr_eq => /eqP ->.
      by exists (fc + c); rewrite !(rmorphD, ecXD).
    + case=> fc ->; exists (fc - c).
      by rewrite !(rmorphB, ecXB).
  Qed.

  Lemma Nfctt_neq0 (f : {fraction ecpoly}):
    ~~ (constant_fraction f) -> f != 0.
  Proof.
    move=> Nctt; apply/eqP=> z_f; move: Nctt.
    by rewrite z_f constant_fraction0.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma reduced_polyratio (p : {polyratio K}):
    reducep p = p.
  Proof.
    apply: polyratio_axiom_uniq.
    + exact: reducep_axiom.
    + by case: p.
    + exact: reducep_eqmod.
  Qed.

  (* -------------------------------------------------------------------- *)
  Reserved Notation "e .[! x , y ]" (at level 2, format "e .[! x ,  y ]").

  Implicit Types p q : {poly K}.
  Implicit Types f : {fraction {poly K}}.
  Implicit Types e : {fraction ecpoly}.

  Definition comp_poly_fec e p := (map_poly PEF p).[e].

  Lemma comp_poly_fec_is_additive e: additive (comp_poly_fec e).
  Proof.
    by move=> p q /=; rewrite /comp_poly_fec rmorphB /= !hornerE.
  Qed.

  Canonical comp_poly_fec_additive e :=
    Additive (comp_poly_fec_is_additive e).

  Lemma comp_poly_fec_is_multiplicative e: multiplicative (comp_poly_fec e).
  Proof.
    split; last first.
      by rewrite /comp_poly_fec rmorph1 hornerC.
    by move=> p q /=; rewrite /comp_poly_fec rmorphM /= !hornerE.
  Qed.

  Canonical comp_poly_fec_multiplicative e :=
    AddRMorphism (comp_poly_fec_is_multiplicative e).

  Notation "p \PFo e" := (comp_poly_fec e p).

  Lemma comp_polyX_fec e: ('X \PFo e) = e.
  Proof. by rewrite /comp_poly_fec map_polyX hornerX. Qed.

  Lemma comp_polyC_fec c e: (c%:P \PFo e) = c%:PEF.
  Proof. by rewrite /comp_poly_fec map_polyC /= hornerC. Qed.

  Lemma comp_polyD_fec p q e:
  (p + q) \PFo e = (p \PFo e) + (q \PFo e).
  Proof. by rewrite /comp_poly_fec rmorphD /= hornerD. Qed.

  Lemma comp_polyM_fec p q e:
    (p * q) \PFo e = (p \PFo e) * (q \PFo e).
  Proof. by rewrite /comp_poly_fec rmorphM /= hornerM. Qed.

  Notation "e .[! x , y ]" := (eval e (|x, y|)).

  Local Notation "x \+ y" := (FracInterp.add x y).
  Local Notation "x \* y" := (FracInterp.mul x y) (at level 30).

  Lemma eval_ge0_order (f : {fraction ecpoly}) (p : point K):
    (isfinite (eval f p)) = (0 <= order f p).
  Proof.
    apply/idP/eval_ge0_orderP.
    + by case: (eval f p) => [g|//] _; exists g.
    + by case=> g ->.
  Qed.

  Lemma eval_comp_fec p e g:
    oncurve g -> (size p > 1)%N ->
      (eval (p \PFo e) g) =
        match eval e g with
        | z%:PP => (p.[z])%:PP
        | [inf] => [inf]
        end.
  Proof.
    move=> oncve nc_p; elim/poly_ind: p nc_p => [|p c IH].
      by rewrite size_poly0.
    rewrite size_MXaddC; case: (p =P 0) => [->|/eqP nz_p].
      by rewrite /=; case: (_ == 0); rewrite ?size_poly0.
    move=> _; rewrite !(rmorphD, rmorphM) /= comp_polyX_fec comp_polyC_fec.
    rewrite evalDr evalC //; case: (ltnP 1 (size p)); last first.
      move=> lt_szp_1; rewrite [p]size1_polyC //; set k := p`_0.
      rewrite comp_polyC_fec evalM_finL ?orderC // evalC //.
      case: (eval e _) => [z|]; first by rewrite !hornerE.
      rewrite /= -(inj_eq (@polyC_inj _)) -size1_polyC //.
      by rewrite (negbTE nz_p).
    move/IH=> {}IH; rewrite evalM; last first.
      rewrite -sgzM sgz_ge0; case: (ltrP (order e g) 0).
      + move=> lt_oe_0; rewrite nmulr_lge0 // ltW //.
        rewrite eval_lt0_order IH; move: lt_oe_0.
        by rewrite eval_lt0_order => /eqP ->.
      + move=> ge_oe_0; rewrite mulr_ge0 //.
        rewrite -eval_ge0_order IH.
        by move/eval_ge0_orderP: ge_oe_0 => [z ->].
    rewrite IH; case: (eval e _) => [z|] //.
    by rewrite !hornerE.
  Qed.

  Definition fzeros (e : {fraction ecpoly}): seq (point K) :=
    dom (fgpos (ecdiv e)).

  Lemma fzerosP e: e != 0 ->
    forall (g : point K), oncurve g -> (g \in fzeros e) = (eval e g == 0%:PP).
  Proof.
    move=> nz_e g oncve; rewrite /fzeros mem_dom inE /= coeff_fgposE.
    by rewrite eq_maxl -ltNge ecdiv_coeffE eval_gt0_order.
  Qed.

  Lemma comp_poly_fec_eq0 p e:
    p != 0 -> p \PFo e == 0 -> constant_fraction e.
  Proof.
    move=> nz_p z_pe; case: (leqP (size p) 1).
      move=> le_szp_1; move: z_pe; rewrite [p]size1_polyC //.
      rewrite comp_polyC_fec tofrac_eq0 ecX_eq0.
      by rewrite -size1_polyC // (negbTE nz_p).
    move=> lt_1_szp; pose eg g := gproject (eval e g).
    have: forall g, eval e g = (eg g)%:PP.
      move=> g; case oncve_g: (oncurve g); last first.
        by rewrite /eg !eval_outcve ?oncve_g //.
      have/eval_comp_fec := lt_1_szp => /(_ e g oncve_g).
      by rewrite /eg (eqP z_pe) eval0; case: (eval e g).
    move=> fin_eg; have: forall g, oncurve g -> p.[eg g] == 0.
      move=> g oncve_g; have/eval_comp_fec := lt_1_szp => /(_ e g oncve_g).
      by rewrite fin_eg /= (eqP z_pe) eval0 => [[<-]].
    move=> eg_root_p; case ctt_e: (constant_fraction e) => //.
    pose pj g := match g with (|x, y|) => Some (x, y) | _ => None end.
    pose R g := pmap (pj K) (fzeros (e - g%:PEF)).
    pose G := flatten [seq R g | g <- roots p].
    pose q := (\prod_(g <- G) ('X - g.1%:P)).
    pose a := (root1 Xpoly, 0 : K).

    have nz_eBC c: e - c%:PEF != 0.
      by apply: Nfctt_neq0; rewrite fctt_shift ctt_e.

    have: forall x y, oncurve (|x, y|) -> (x, y) \in G.
      move=> x y oncve_xy; rewrite /G; apply/flattenP.
      exists (R (eg (|x, y|))).
      + apply/mapP; exists (eg (|x, y|)) => //.
        by rewrite rootsP // mem_root; apply: eg_root_p.
      + rewrite /R mem_pmap; apply/mapP; exists (|x, y|) => //.
        rewrite fzerosP ?nz_eBC //.
        by rewrite evalDl ?fin_eg // -rmorphN evalC //= subrr.

    have oncve_a: oncurve (|a.1, a.2|).
      rewrite /a /= -horner_Xpoly eq_sym expr0n /=.
      rewrite  -rootE root1_root //.
      by rewrite (@hasroot_size_neq1 clK) size_Xpoly.
    move/(_ a.1 a.2 oncve_a) => a_in_G.

    set z := root1 (q + 1); have z_root_qS: root (q + 1) z.
      have: (size q > 1)%N.
        rewrite /q size_prod_XsubC ltnS lt0n size_eq0.
        by apply/eqP => G_eq0; rewrite G_eq0 in_nil in a_in_G.
      move=> lt_1_szq; apply: root1_root.
      rewrite (@hasroot_size_neq1 clK) size_addl.
      + by rewrite eq_sym neq_ltn lt_1_szq.
      + by rewrite size_poly1.

    pose b := (z, sqrt Xpoly.[z]).

    have oncve_b: oncurve (|b.1, b.2|).
    + by rewrite {}/b /= -horner_Xpoly (@sqr_sqrt clK).

    have/(_ (|b.1, b.2|) oncve_b) := eg_root_p; set g := eg _.
    move=> root_p_g; have: b \in R g.
      rewrite /R mem_pmap; apply/mapP.
      exists (|b.1, b.2|) => //; rewrite /g.
      rewrite fzerosP ?nz_eBC // evalDl ?fin_eg //.
      by rewrite -!rmorphN evalC //= subrr.

    move=> b_in_Rg; have: b \in G.
      rewrite /G; apply/mem_flattenP; exists (R g) => //.
      + by apply/mapP; exists g => //; rewrite rootsP.

    move=> b_in_G; have: root q z.
      rewrite rootE /q horner_prod.
      rewrite (perm_big _ (perm_to_rem b_in_G)) /=.
      by rewrite big_cons /b /= !hornerE subrr mul0r.

    move=> z_root_q; move: z_root_qS; rewrite rootE.
    by rewrite !hornerE (rootP z_root_q) add0r oner_eq0.
  Qed.

  Definition comp_frac_fec f e: {fraction ecpoly} :=
    gproject (map_polyfrac PEF f).[!e].

  Notation "f \Fo e"  := (comp_frac_fec f e).

  Lemma comp_fracC_fec e c: (c%:P)%:F \Fo e = c%:PEF.
  Proof.
    rewrite /comp_frac_fec /gproject map_polyfracF map_polyC /=.
    by rewrite finterp_poly hornerC.
  Qed.

  Lemma comp_frac_fecE n d e: ~~ (constant_fraction e)
    -> (n // d) \Fo e = (n \PFo e) / (d \PFo e).
  Proof.
    move=> Nccte; have [->|nz_n] := eqVneq n 0.
      by rewrite comp_polyC_fec !mul0r comp_fracC_fec.
    have [->|nz_d] := eqVneq d 0.
      by rewrite comp_polyC_fec !invr0 !mulr0 comp_fracC_fec.
    rewrite /comp_frac_fec map_polyfracE /= finterp_nzden //=.
    by apply/negP => /comp_poly_fec_eq0 -/(_ nz_d); rewrite (negbTE Nccte).
  Qed.

  Lemma comp_fracD_fec f1 f2 e:
  ~~ (constant_fraction e) ->
  (f1 + f2) \Fo e = (f1 \Fo e) + (f2 \Fo e).
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1;
    elim/fracW: f2 => n2 d2 nz_d2.
    move=> NCFe.
    rewrite !comp_frac_fecE // addf_div ?tofrac_eq0 //.
    rewrite -!tofracM -tofracD comp_frac_fecE // !addf_div.
    + rewrite comp_polyM_fec; congr (_ / _).
    by rewrite comp_polyD_fec !comp_polyM_fec.
    + case Hd1: (d1 \PFo e == 0).
    move: (@comp_poly_fec_eq0 d1 e nz_d1).
    by rewrite (negbTE NCFe); apply; rewrite (eqP Hd1).
    rewrite //.
    + case Hd2: (d2 \PFo e == 0).
    move: (@comp_poly_fec_eq0 d2 e nz_d2).
    by rewrite (negbTE NCFe); apply; rewrite (eqP Hd2).
    rewrite //.
  Qed.

  Lemma comp_fracM_fec f1 f2 e: ~~(constant_fraction e) ->
    (f1 * f2) \Fo e = (f1 \Fo e) * (f2 \Fo e).
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1;
    elim/fracW: f2 => n2 d2 nz_d2;
      rewrite mulf_div -!tofracM => Nctt_e.
    by rewrite !comp_frac_fecE // !comp_polyM_fec mulfE.
  Qed.

  Lemma comp_frac_prod_fec (I : Type) (r : seq I) (P : pred I) F (e : {fraction ecpoly}):
       ~~ constant_fraction e
    -> (\prod_(i <- r | P i) (F i)) \Fo e = \prod_(i <- r | P i) ((F i) \Fo e).
  Proof.
    move=> Ncct_e; elim: r => [|i r IH].
      by rewrite !big_nil comp_fracC_fec.
    by rewrite !big_cons; case: (P i); rewrite ?comp_fracM_fec // IH.
  Qed.

  Lemma comp_fracF_fec (p : {poly K}) (e : {fraction ecpoly}):
    ~~ constant_fraction e -> p%:F \Fo e = p \PFo e.
  Proof.
    move=> Ncct_e; rewrite -[_%:F]divr1 -[1]tofrac1 comp_frac_fecE //.
    by rewrite comp_polyC_fec divr1.
  Qed.

  Lemma comp_fracV_fec f e: ~~(constant_fraction e) ->
    (f^-1) \Fo e = (f \Fo e)^-1.
  Proof.
    move=> Nctt_e; elim/fracW: f => n d nz_d.
    by rewrite invfE !comp_frac_fecE // invfE.
  Qed.

  (*bad name*)
  Lemma comp_fracXn_fec e f n: ~~ (constant_fraction e) ->
    (f \Fo e) ^+ n = (f ^+ n) \Fo e.
  Proof.
    move=> Nctt_e; elim: n => [|n IH].
      by rewrite !expr0 comp_fracC_fec.
    by rewrite !exprS comp_fracM_fec // IH.
  Qed.

  (*bad name*)
  Lemma comp_fracX_exp f e (z : int): ~~ (constant_fraction e) ->
    (f \Fo e) ^ z = (f ^ z) \Fo e.
  Proof.
    move=> Nctt_e; case: z => n.
    + by rewrite -!exprnP comp_fracXn_fec.
    + by rewrite !NegzE -!exprnN comp_fracV_fec // comp_fracXn_fec.
  Qed.

  (*bad name*)
  Lemma comp_fracX_fec f e (n : nat):
     ~~ constant_fraction e ->
     comp_frac_fec (f ^+ n) e = (comp_frac_fec f e) ^+ n.
  Proof.
    move=> Nctt_e; elim: n.
    + rewrite !expr0 comp_fracC_fec //=.
    + move=> n IH.
    by rewrite !exprS comp_fracM_fec // IH.
  Qed.

  (*XXX*)
  Lemma ecdiv_eq0_cct (f : {fraction ecpoly}):
    ecdiv f = 0 -> constant_fraction f.
  Proof.
    have [->|nz_f] := (eqVneq f 0).
      by rewrite constant_fraction0.
    elim/fracW: f nz_f => n d nz_d.
    rewrite mulf_eq0 tofrac_eq0 => /norP [nz_n _].
    have ->: n // d = (n * conjp d) // (normp d)%:E.
      rewrite -[_%:E]conjp_normp !tofracM -mulfE divff ?mulr1 //.
      by rewrite tofrac_eq0 conjp_eq0.
    set n1 := n * _; set d1 := (normp _).
    have nz_n1: n1 != 0 by rewrite mulf_neq0 ?conjp_eq0.
    have nz_d1: d1 != 0 by rewrite norm_eq0.
    move: {n d nz_n nz_d} n1 d1 nz_n1 nz_d1 => n d nz_n nz_d.
    move=> eq0_div; have eq0_divcj: ecdiv ((conjp n) // d%:E) = 0.
      apply/eqP/freeg_eqP=> p; rewrite !ecdiv_coeffE coeff0.
      move/eqP/freeg_eqP: eq0_div => /(_ (\- p)%G).
      rewrite !ecdiv_coeffE coeff0 -[_ // _]conjK.
      by rewrite order_conj conjE conjp_ecX.
     have ord_f: forall (p : point _), 0 <= order (n // d%:E) p.
     by move=> p; rewrite -ecdiv_coeffE eq0_div coeff0.
    have ord_cf: forall (p : point _), 0 <= order (conjp n // d%:E) p.
      by move=> p; rewrite -ecdiv_coeffE eq0_divcj coeff0.
    have order_n2: forall (p : point _), order (n.2 %:E // d%:E) p >= 0.
      pose f := n // d%:E; move=> p; case oncve: (oncurve p); last first.
        by rewrite order_outcve // oncve.
      move/(congr1 (fun e => eval e p)): (erefl (f + conj f)).
      rewrite {1 2}/f; rewrite {1}conjE conjp_ecX /ecX -mulrDl.
      rewrite -tofracD -[n]ecpolyE /conjp addE /= subrr -mulr2n.
      rewrite -mulr_natl -!/(ecX _ _) ecXM tofracM -mulrA.
      rewrite /GRing.one /= -polyCMn evalM_finL ?orderC //.
      rewrite evalC // evalDl; last first.
        by case/(eval_ge0_orderP): (ord_f p)=> c ->.
      rewrite /f conjE conjp_ecX;
        case/(eval_ge0_orderP): (ord_f  p)=> c1 ->;
        case/(eval_ge0_orderP): (ord_cf p)=> c2 ->.
      rewrite -eval_ge0_order; case: (eval (_ // _)) => //=.
      by rewrite (negbTE (ecu_chi2 _)).
    have order_n1: forall (p : point _), 0 <= order ([ecp n.1 *Y + 0] // d%:E) p.
      pose f := n // d%:E; move=> p; case oncve: (oncurve p); last first.
        by rewrite order_outcve // oncve.
      move: (erefl f); move/(congr1 (+%R^~ (- (n.2%:E // d%:E)))).
      rewrite {1}/f -{1}mulNr -mulrDl -{1}[n]ecpolyE -tofracB.
      rewrite -ecXN addE /= subrr addr0 => /esym.
      move/(congr1 (fun e => eval e p)); rewrite evalDl; last first.
        by case/(eval_ge0_orderP): (ord_f p)=> c1 ->.
      rewrite evalN; case/(eval_ge0_orderP): (order_n2 p)=> c ->.
      case/(eval_ge0_orderP): (ord_f p)=> cf -> /=.
      move: (cf - c) => {cf}c /esym eval_n1d.
      by rewrite -eval_ge0_order eval_n1d.
    have: forall p : point K, 0 <= order ((n.1)%:E // d%:E) p.
      move=> p; have [->|nz_n1] := (eqVneq n.1 0).
        by rewrite mul0r order0.
      case oncve: (oncurve p); last by rewrite order_outcve ?oncve.
      move/eval_ge0_orderP: (order_n1 p) => [c].
      move/(congr1 (fun x => x \* x)); rewrite -evalM; last first.
        by rewrite -sgzM -expr2 sgzX sqr_ge0.
      rewrite mulf_cross -!expr2 exprVn -tofracX ecY_sqr /=.
      move: (c * c) => {}c /eval_fin_order_ge0.
      rewrite ecXM tofracM mulrAC ecXX tofracX -divf_exp.
      rewrite [X in 0 <= X -> _]order_mul ?(neq0, XpolyN0) // order_exp.
      case: p oncve => [|x y] oncve /=.
        by rewrite orderF_inf subr_ge0; case: (order _ _).
      move: oncve; have [->|nz_y] := (eqVneq y 0); last first.
        move=> oncve; have /eqP->: order (Xpoly%:E)%:F (|x, y|) == 0.
          rewrite -order_poly_cmp0 ?ecX_eq0 // ecX_eceval.
          apply/negP=> root_Xc; have := oncve; rewrite oncurve_root.
          rewrite rootE !hornerE (eqP root_Xc) subr0 -expr2.
          by rewrite sqrf_eq0 (negbTE nz_y).
        by rewrite addr0 pmulrn_lge0.
      rewrite -Xpoly_oncurve => oncve; move: (order_Xpoly_le2 E (|x, 0|)) => h.
      rewrite addrC -[X in _ + X]opprK subr_ge0 => h'.
      move: {h h'} (le_trans h' h).
      rewrite -mulNrn -natz ler_muln2r /= le_eqVlt; case/orP.
      + rewrite eqr_oppLR => /eqP orderE; move: (even_orderS n.1 d oncve).
        by rewrite orderE abszN absz1.
      + by case: (order _ _).
    move=> {}order_n1.

    (*to use and not ord_f*)
    have ord_F: forall (p : point _), 0 = order (n // d%:E) p.
     by move=> p; rewrite -ecdiv_coeffE eq0_div coeff0.
    have ord_cF: forall (p : point _), 0 = order (conjp n // d%:E) p.
      by move=> p; rewrite -ecdiv_coeffE eq0_divcj coeff0.
     (**)

    pose Y := ([ecp 1 *Y + 0]%:F : {fraction {ecpoly E}}).
    have fE: n // d%:E = ((n.1%:E) // d%:E) * Y + ((n.2%:E) // d%:E).
    + rewrite /Y mulrAC -tofracM mulE /dotp /= !simpm.
      by rewrite -mulrDl -tofracD addE /= !simpm ecpolyE.

    have f_ecpoly: exists f : ecpoly, f%:F = n // d%:E.
    + rewrite fE;  have h q:
           (forall p : point K, 0 <= order (q%:E // d%:E) p)
        -> exists q', q%:E // d%:E= q'%:E%:F.
      * move=> order_q; have [->|q_eq0] := (eqVneq q 0).
          by exists 0; rewrite mul0r.
        case: (@finterp_all_finite clK q d); last move=> r1 ->.
          by rewrite mulf_neq0 // ?invr_eq0 tofrac_eq0.
        move=> x; set y := sqrt (Xpoly.[x]).
        rewrite -(eval_fracecX_fin (E := E) (y := y)); first last.
        * by apply: order_q.
        * by rewrite /= /y horner_Xpoly (@sqr_sqrt clK).
        * by rewrite eval_ge0_order.
        exists r1; rewrite ecXM tofracM -mulrA divff ?mulr1 //.
        by rewrite tofrac_eq0 ecX_eq0.
      case: (h n.1) => // q1 ->; case: (h n.2) => // q2 ->.
      exists [ecp q1 *Y + q2].
      rewrite -tofracM -tofracD mulE /dotp /= !simpm.
      by rewrite addE /= !simpm.

      case: f_ecpoly => f f_ecpoly.

      have order_eq0 : forall (p : point _), order f%:F p = 0.
      move=> p; by rewrite -ecdiv_coeffE f_ecpoly eq0_div coeff0.
      have [c f_constant]: exists c : K, f = (c%:P)%:E.
      + have [->|nz_f] := eqVneq f 0; first by exists 0.
        case: (all_order_eq0P closedK nz_f); case.
          by move=> x y; rewrite order_eq0.
        by move=> x nz_x -> _; exists x.
      apply/constant_fractionP; exists c.
      by rewrite -f_ecpoly -f_constant.
  Qed.

  Lemma eq_ecdiv_proportional_func (f g : {fraction ecpoly}):
       f != 0
    -> g != 0
    -> ecdiv f = ecdiv g
    -> exists2 a : K, a != 0 & f = g * (a%:PEF).
  Proof.
    move=> nz_f nz_g eq; set r := f / g; have: ecdiv r = 0.
      by rewrite ecdivM ?(mulf_neq0, invr_eq0) // ecdivV eq subrr.
    move/ecdiv_eq0_cct/constant_fractionP; case=> c hc; exists c.
    + apply/negP=> /eqP c_eq0; move/eqP: hc.
      by rewrite /r c_eq0 mulf_eq0 invr_eq0 (negbTE nz_f) (negbTE nz_g).
    + by rewrite /= -hc /r mulrCA divff // mulr1.
  Qed.

  Lemma ecdiv_eq0_constant_fraction (f : {fraction ecpoly}) :
    (ecdiv f == 0) = (constant_fraction f).
  Proof.
    apply/eqP/idP.
    + elim/fracW: f => n d nz_d; have [->|nz_n] := eqVneq n 0.
        by rewrite mul0r constant_fraction0.
      by move=> h; rewrite ecdiv_eq0_cct.
    + by case/constant_fractionP => c ->; rewrite ecdivC.
  Qed.

  Lemma Nctt_surjective (f : {fraction ecpoly}) x:
    ~~ constant_fraction f -> exists2 P, oncurve P & eval f P = x.
  Proof.
    move=> Nctt_f; have := Nctt_f; rewrite -ecdiv_eq0_constant_fraction.
    rewrite [ecdiv _]fg_decomp subr_eq0 => neq.
    have hdeg: deg (fgpos (ecdiv f)) = deg (fgneg (ecdiv f)).
      by apply/eqP; rewrite -subr_eq0 -degB -fg_decomp deg_ecdiv_eq0.
    case: x => [x|]; last first.
      set P := nth ∞ (dom (fgneg (ecdiv f))) 0.
      have P_in: P \in dom (fgneg (ecdiv f)).
        rewrite mem_nth // lt0n size_eq0 dom_eq0.
        apply/eqP=> eq; move: hdeg neq; rewrite eq deg0.
        by move/(fgpos_eq0P (fgpos_le0 _)) => ->; rewrite eqxx.
      exists P.
      + have [//|outcve] := (boolP (oncurve P)); move: P_in.
        by rewrite mem_negdiv order_outcve.
      + by apply order_lt0_eval; rewrite -mem_negdiv.
    have h (g : {fraction ecpoly}):
         fgpos (ecdiv g) != fgneg (ecdiv g)
      -> exists2 P, oncurve P & eval g P = 0%:PP.
      move=> {hdeg}neq; set P := nth ∞ (dom (fgpos (ecdiv g))) 0.
      have hdeg: deg (fgpos (ecdiv g)) = deg (fgneg (ecdiv g)).
        by apply/eqP; rewrite -subr_eq0 -degB -fg_decomp deg_ecdiv_eq0.
      have P_in: P \in dom (fgpos (ecdiv g)).
        rewrite mem_nth // lt0n size_eq0 dom_eq0.
        apply/eqP=> eq; move: hdeg neq; rewrite eq deg0 => /esym.
        by move/(fgpos_eq0P (fgneg_le0 _)) => ->; rewrite eqxx.
      exists P.
      + have [//|outcve] := (boolP (oncurve P)); move: P_in.
        by rewrite mem_posdiv order_outcve.
      + by rewrite order_gt0_eval // -mem_posdiv.
    case: (h (f - x%:PEF)).
      by rewrite -subr_eq0 -fg_decomp ecdiv_eq0_constant_fraction fctt_shift.
    move=> P oncve_P eq; exists P => //; move: eq.
    rewrite evalDr evalN evalC //= => /(congr1 (fun y => y \+ x%:PP)).
    by rewrite -Monoid.mulmA /= [-x+_]addrC subrr add0r Monoid.mulm1.
  Qed.

  Lemma injective_comp_poly_fec (h : {fraction ecpoly}) (p1 p2 : {poly K}):
       ~~ constant_fraction h
    -> comp_poly_fec h p1 = comp_poly_fec h p2 -> p1 = p2.
  Proof.
    move=> Nctt_h; move/eqP; rewrite -subr_eq0 -raddfB /=.
    move/eqP; case: (ltnP 1 (size (p1 - p2))); last first.
      rewrite leq_eqVlt; case/orP=> [/size_poly1P [c nz_c ->]|]; last first.
        by rewrite ltnS leqn0 size_poly_eq0 subr_eq0 => /eqP.
      move/eqP; rewrite comp_polyC_fec tofrac_eq0 ecX_eq0.
      by rewrite polyC_eq0 (negbTE nz_c).
    move=> lt1_szp1Bp2; case: (Nctt_surjective [inf] Nctt_h).
    move=> R oncveR eval_hR /(congr1 ((@eval _ _)^~ R)).
    by rewrite eval0 eval_comp_fec // eval_hR.
  Qed.

  Lemma injective_comp_frac_fec (h : {fraction ecpoly}) (f1 f2 : {fraction {poly K}}):
       ~~ constant_fraction h
    -> comp_frac_fec f1 h = comp_frac_fec f2 h -> f1 = f2.
  Proof.
    move=> Nctt_h;
      elim/fracW: f1 => n1 d1 nz_d1;
      elim/fracW: f2 => n2 d2 nz_d2;
    move/eqP=> eq; apply/eqP; move: eq.
    rewrite !comp_frac_fecE // !divff_eq; first last.
    + by rewrite mulf_neq0 //; apply/negP;
           [ move/comp_poly_fec_eq0 => /(_ nz_d1)
           | move/comp_poly_fec_eq0 => /(_ nz_d2) ];
           rewrite (negbTE Nctt_h).
    + by rewrite mulf_neq0 // tofrac_eq0.
    rewrite -!comp_polyM_fec -!tofracM => /eqP.
    by move/injective_comp_poly_fec => /(_ Nctt_h) ->.
  Qed.
End FracECPoly.
