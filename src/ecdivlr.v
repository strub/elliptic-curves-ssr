(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp
Require Import ssreflect ssrnat ssrbool eqtype fintype choice.
From mathcomp
Require Import tuple perm zmodp ssrfun bigop ssralg ssrint.
From mathcomp
Require Import ssrnum poly polydiv generic_quotient.
Require Import polyall polydec polyfrac SsrMultinomials.freeg.

Require Import Setoid.

Require Import ec ecpoly eceval ecorder ecdiv ecrr.
Require Import fraction ecpolyfrac xmatrix xseq.

(* -------------------------------------------------------------------- *)
Import GRing.Theory.
Import Num.Theory.
Import fraction.FracField.
Import fracfield.FracField.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Section LinearReduction.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).
  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ECPoly E (0, p)).

  Implicit Types f : {fraction ecpoly}.

  Hypothesis closedK : GRing.ClosedField.axiom K.

  Import PreClosedField.

  Hint Resolve closedK.

  Local Notation clK := (ClosedFieldType K closedK).
  Local Notation PEF := (@tofrac _ \o ((ecX E) \o polyC)).
  Local Notation "x %:PEF" := (PEF x) (at level 2).
  Local Notation "x %:F"  := (tofrac x).
  Local Notation "x // y" := (x%:F / y%:F) (at level 50, no associativity).

  Local Notation "\+%G" := (@ECGroup.add _ E).

  Local Notation "\- x" := (@ECGroup.neg _ x).
  Local Notation "x \+ y" := (@ECGroup.add _ E x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Local Notation "D1 :~: D2" := (@ecdeqv _ E D1 D2).

  Definition lr_r (D : {freeg (point K)}) :=
    let iter p n := nosimpl iterop _ n \+%G p ∞ in
      \big[\+%G/∞]_(p <- dom D | p != ∞) (iter p `|coeff p D|%N).

  Definition lr (D : {freeg (point K)}) : point K :=
    let: (Dp, Dn) := (fgpos D, fgneg D) in
      lr_r Dp \- lr_r Dn.

  Local Notation "D1 <=g D2" := (fgle D1 D2).

  (* FIXME: move this *)
  Lemma oncurve_natmul n p: oncurve p -> oncurve (iterop n \+%G p ∞).
  Proof.
    move=> p_oncve; rewrite /iterop; elim: n => [//|n IH].
    by rewrite iteriS; case: n IH => [//|n] IH; apply ECGroup.addO.
  Qed.

  (* FIXME: move this *)
  Lemma oncurve_sum (I : Type) (F : I -> point K) (ps : seq I):
    all (oncurve \o F) ps -> oncurve (\big[\+%G/∞]_(p <- ps) (F p)).
  Proof.
    elim: ps => [|p ps IH]; first by rewrite big_nil.
    move=> /= /andP [oncve_p oncve_ps]; rewrite big_cons.
    by apply: ECGroup.addO => //; apply: IH.
  Qed.

  Add Parametric Relation (E : ecuType K):
    {freeg (point K)} (ecdeqv E)
      reflexivity  proved by (@ecdeqv_refl  _ E)
      symmetry     proved by (@ecdeqv_sym   _ E)
      transitivity proved by (@ecdeqv_trans _ E)
    as ecdeqv_rel.

  Add Parametric Morphism (E : ecuType K):
    (@GRing.opp _) with signature
          (ecdeqv E)
      ==> (ecdeqv E)
    as ecdeqv_morph_opp.
  Proof. by move=> D1 D2 eqv; apply: ecdeqv_opp. Qed.

  Add Parametric Morphism (E : ecuType K):
    (@GRing.add _) with signature
          (ecdeqv E)
      ==> (ecdeqv E)
      ==> (ecdeqv E)
    as ecdeqv_morph_add.
  Proof. by move=> D1 D2 eqv D'1 D'2 eqv'; apply: ecdeqv_add. Qed.

  Require Import ssrring.

  Lemma Nsym_ecdivpE (p : ecpoly) cs:
       (forall x y, y != 0 -> (p.[x, y] != 0) || (p.[x, -y] != 0))
    -> (forall x y, (x, y) \in cs -> oncurve (|x, y|))
    -> (forall x y, (x, y) \in cs -> p.[x, y] = 0)
    -> perm_eq (map (@fst _ _) cs) (roots (normp p))
    -> ecdivp p = \sum_(i <- cs) << (|i.1, i.2|) >> + << order p%:F ∞ *g ∞ >>.
  Proof.
    move=> Nsym csoncve csok; have [->|nz_p] := eqVneq p 0.
      rewrite ecdivp0 norm0 roots0 => /perm_eq_small.
      move/(_ (erefl true)); case: {csok csoncve} cs => [|//] _.
      by rewrite big_nil order0 freegU0 addr0.
    move=> csroots; apply/eqP/freeg_eqP => ecp.
    rewrite ecdivpE coeffD raddf_sum /=; case: ecp => [|x y].
      rewrite big1; last first.
        by move=> i _; rewrite coeffU mulr0.
      by rewrite add0r coeffU eqxx mulr1.
    have [oncve|Noncve] := boolP (oncurve (|x, y|)); last first.
      rewrite order_outcve // big_seq big1; last first.
        case=> [x' y'] /= /csoncve oncve.
        move/memPn: Noncve => /(_ _ oncve) => ne.
        by rewrite coeffU (negbTE ne) mulr0.
      by rewrite add0r coeffU mulr0.
    rewrite coeffU /= mulr0 addr0.
    move: (erefl (order (normp p)%:E%:F (|x, y|))).
    rewrite {1}orderF poly_order_mu // -conjp_normp.
    rewrite tofracM order_mul ?(mulf_neq0, tofrac_eq0, conjp_eq0) //.
    have [z_y|nz_y] := eqVneq y 0; first rewrite z_y.
      rewrite -conjF -{4}[0]oppr0 (order_conj _ (|x, 0|)).
      rewrite eqxx /= -mulr2n PoszM pmulrn mulrzz => /mulIf <- //.
      rewrite (bigID (fun i => i.1 == x)) /= addrC big1; last first.
        by move=> i ne_i1_x; rewrite coeffU eqE /= (negbTE ne_i1_x) mulr0.
      rewrite add0r big_seq_cond (eq_bigr (fun i => 1)); last first.
        case=> [x' y'] /= /andP [x'y'_in_cs /eqP eq_x'x]; rewrite coeffU eqE /=.
        rewrite eq_x'x eqxx /= mul1r; move/csoncve: x'y'_in_cs => /=.
        by rewrite eq_x'x -(eqP oncve) z_y expr0n /= sqrf_eq0 => ->.
      rewrite -big_seq_cond -big_filter big_const_seq count_predT.
      rewrite -Monoid.iteropE /= -/(GRing.natmul _ _) size_filter.
      by rewrite roots_mu ?norm_eq0 // -(perm_eqP csroots) count_map natz.
    have [z_ord|] := eqVneq (order p%:F (|x, y|)) 0.
      move=> _; rewrite z_ord big_seq big1 ?addr0 //.
      move=> [x' y'] x'y'_in_cs; rewrite coeffU mul1r.
      case: (_ =P _) => [|//] /= eq; move/csok/eqP: x'y'_in_cs.
      move/eqP: z_ord; rewrite -order_poly_cmp0 //.
      by case: eq => -> -> /negbTE ->.
    rewrite -order_poly_cmp0 // negbK => /eqP z_pxy.
    have := (Nsym x y nz_y); rewrite z_pxy eqxx /= => nz_pxNy.
    rewrite -conjF -{3}[y]opprK (order_conj _ (|x, -y|)).
    have ->: order p%:F (|x, -y|) = 0.
      move: nz_pxNy; rewrite order_poly_cmp0 -?(oncurveN E (|x, y|)) //.
      by move/eqP => ->.
    rewrite addr0 => <-; rewrite (negbTE nz_y) muln1.
    rewrite (bigID (fun i => i.1 == x)) /= addrC big1; last first.
      by move=> i ne_i1_x; rewrite coeffU eqE /= (negbTE ne_i1_x) mulr0.
    rewrite add0r big_seq_cond (eq_bigr (fun i => 1)); last first.
      case=> [x' y'] /andP [x'y'_in_cs /= /eqP eq_x'x].
      rewrite coeffU mul1r eqE /= eq_x'x eqxx /=.
      have/csoncve := x'y'_in_cs; rewrite eq_x'x /= -(eqP oncve).
      rewrite eqf_sqr; case/orP => [->//|/eqP y'E].
      move: (csok _ _ x'y'_in_cs); rewrite eq_x'x y'E => /eqP.
      by rewrite (negbTE nz_pxNy).
    rewrite -big_seq_cond -big_filter big_const_seq count_predT.
    rewrite -Monoid.iteropE /= -/(GRing.natmul _ _) size_filter.
    by rewrite roots_mu ?norm_eq0 // -(perm_eqP csroots) count_map natz.
  Qed.

  Lemma lrline p1 p2:
       oncurve p1
    -> oncurve p2
    -> (<< p1 >> + << p2 >>) :~: (<< p1 \+ p2 >> + << ∞ >>).
  Proof.
    case: p1 p2 => [|x1 y1] [|x2 y2].
    + by move=> _ _; rewrite ECGroup.add0o; reflexivity.
    + by move=> _ oncve; rewrite ECGroup.add0o // addrC; reflexivity.
    + by move=> oncve _; rewrite ECGroup.addoC ECGroup.add0o // addrC; reflexivity.
    move=> oncve_1 oncve_2; case h: (ECGroup.line E (x1, y1) (x2, y2)) => [[u v] c].
    set a := (_ \+ _); pose r : ecpoly := [ecp u%:P *Y + v *: 'X - c%:P].
    have oncve_a: oncurve a by rewrite /a ECGroup.addO.
    case: (u =P 0) => [z_u|/eqP nz_u].
      move: h z_u; rewrite /ECGroup.line oncve_1 oncve_2 /=.
      case: (x1 =P x2) => [eq_x1x2|_]; last first.
        by case=> <- _ _ /eqP; rewrite oner_eq0.
      case b: (_ && _); first by move=> [<- _ _] /eqP; rewrite oner_eq0.
      rewrite /a; move=> _ _; rewrite /ECGroup.add oncve_1 oncve_2.
      rewrite -eq_x1x2 eqxx b; have ->: y2 = -y1.
        move: oncve_1 oncve_2 => /=; rewrite -eq_x1x2 => /eqP <-.
        rewrite eqr_sqr ![y2 == _]eq_sym; case/orP; last by move/eqP=>->.
        move/eqP=> eq_y1y2; move: b; rewrite eq_y1y2 eqxx /=.
        by move/negbT; rewrite negbK => /eqP ->; rewrite oppr0.
      case: (ecdeqv_lineS oncve_1) => f Ef; exists f.
      by rewrite Ef /= subr0 freegUD.
    have: ecdivp r = <<(|x1, y1|)>> + <<(|x2, y2|)>> + <<\- a>> - << 3%:Z *g ∞ >>.
      pose z := u ^- 2 * v ^+ 2 - (x1 + x2).
      have: perm_eq (roots (normp r)) [:: x1; x2; z].
        move: (@ECGroup.thdimp K E (x1, y1) (x2, y2)).
        rewrite h => /(_ nz_u) /=; rewrite -/z; move: (erefl (normp r)).
        rewrite {1}/r {1}normpE /= => /(congr1 ( *%R (u ^- 2)%:P)).
        rewrite mulrBr [X in _-X=_]mulrA -polyC_exp -polyC_mul.
        rewrite mulVf ?expf_neq0 // polyC1 mul1r -{1}exprVn.
        rewrite polyC_exp -exprMn !mul_polyC => /(congr1 -%R).
        rewrite opprB => -> /eqP; rewrite eqr_oppLR => /eqP.
        move/(congr1 ( *%R (u^+2)%:P)); rewrite -mul_polyC mulrA.
        rewrite -exprVn 2!polyC_exp -exprMn -polyC_mul divff //.
        rewrite polyC1 expr1n mul1r => ->; apply/perm_eqlP => x.
        rewrite mulrN -mulNr -polyC_exp -[X in roots (X * _)]polyC_opp.
        rewrite -!mulrA mul_polyC roots_mulC ?(oppr_eq0, expf_neq0) //.
        move: x; apply/perm_eqlP; move: (perm_eq_roots_factors [:: x1; x2; z]).
        by rewrite unlock /= mulr1.
      move=> rsr; pose yz := u^-1 * (c - v * z); have NaE: \- a = (|z, yz|).
        rewrite -ECGroup.ladd_addE /ECGroup.ladd !(oncve_1, oncve_2).
        by rewrite h (negbTE nz_u) /yz /z.
      pose cs := [:: (x1, y1); (x2, y2); (z, yz)].
      rewrite (@Nsym_ecdivpE _ cs); last first.
      + by rewrite /cs /= perm_eq_sym.
      + move=> x y; rewrite /cs mem_seq3; case/or3P => /eqP;
          case=> -> ->; rewrite /r /eceval !hornerE /=.
        * by move: (ECGroup.line_okl E (x1, y1) (x2, y2)); rewrite h.
        * by move: (ECGroup.line_okr E (x1, y1) (x2, y2)); rewrite h.
        * by rewrite divff // mul1r; move: {rsr yz NaE cs} z => z; ssring.
      + move=> x y; rewrite /cs mem_seq3; case/or3P => /eqP [->->] //.
        by rewrite -NaE; move: oncve_a; rewrite oncurveN.
      + move=> x y nz_y; rewrite -negb_and; apply/negP => /andP [].
        move/eqP => <- /eqP; rewrite /eceval => /addIr/eqP.
        rewrite mulrN eq_sym ECGroup.eqrN_eq0 mulf_eq0.
        by rewrite (negbTE nz_y) orbF /r /= !hornerE (negbTE nz_u).
      rewrite /cs unlock /= addr0 NaE !addrA; congr (_ + _).
      rewrite orderF /poly_order /= /r eqE /= eqE /=.
      rewrite polyC_eq0 (negbTE nz_u) /= degreeE /=.
      rewrite polyC_eq0 size_polyC !(negbTE nz_u) muln1 /=.
      rewrite /maxn; case: ltnP => /=; first by rewrite -freegUN.
      have [->|nz_v] := eqVneq v 0.
        by rewrite scale0r sub0r size_opp size_polyC; case: (c != 0).
      have {1}->: c = v * (c / v) by rewrite mulrCA divff // mulr1.
      rewrite !polyC_mul -{1}mul_polyC -mulrBr mul_polyC -polyC_mul.
      by rewrite size_scale // size_XsubC.
    case: (ecdeqv_lineS oncve_a) => f /eqP; rewrite subr0 eq_sym.
    rewrite subr_eq eq_sym -subr_eq => /eqP/esym {1}-> /eqP.
    rewrite eq_sym subr_eq eq_sym -subr_eq => /eqP <-.
    have eq: << 2%:Z *g ∞ >> - <<\- a>> + <<∞>> = << 3%:Z *g ∞ >> - <<\- a>>.
      by rewrite addrAC freegUD.
    have [->|nz_f] := eqVneq f 0.
      rewrite ecdiv0 add0r eq; symmetry; exists (r%:F)^-1.
      rewrite -[ecdivp _ + _ + _]addrA; set z := << _ *g _ >> - _.
      by rewrite opprD addrCA subrr addr0 ecdivV ecdivF.
    exists (r%:F / f). rewrite -[X in _ = X-_]addrA.
    set z := << _ *g _ >> - _; move: {-2}z (erefl z).
    rewrite {}/z => z Ez; rewrite -!addrA opprD.
    rewrite [<< 2%:Z *g _ >> + _] addrA eq -Ez !addrA.
    rewrite addrAC -[_ + z - z]addrA subrr addr0.
    rewrite ecdivM ?(mulf_neq0, invr_eq0, tofrac_eq0) //; last first.
      by rewrite /r eqE /= eqE /= polyC_eq0 (negbTE nz_u).
    by rewrite ecdivV ecdivF.
  Qed.

  Lemma oncurve_lr_r D: all oncurve (dom D) -> oncurve (lr_r D).
  Proof.
    move=> oncve; rewrite /lr_r -big_filter; set ps := [seq _ <- _ | _].
    have oncve_ps: all oncurve ps.
      rewrite {}/ps; apply/allP=> p; rewrite mem_filter.
      by case/andP=> _; move/allP: oncve; apply.
    elim: ps oncve_ps => [|p ps IH]; first by rewrite big_nil.
    move=> /= /andP [oncve_p oncve_ps]; rewrite big_cons.
    by apply: ECGroup.addO; apply: IH.
  Qed.

  Lemma oncurve_lr D: all oncurve (dom D) -> oncurve (lr D).
  Proof. by move=> oncve; rewrite /lr; apply: ECGroup.addO. Qed.

  Lemma ecdeqv_lr_r D: 0 <=g D -> all oncurve (dom D) ->
    D :~: << lr_r D >> + << deg D - 1 *g ∞ >>.
  Proof.
    move=> D_ge0 oncve; rewrite /lr_r - big_filter addrC; symmetry.
    rewrite {1}[D]div_sumE degD degU raddf_sum /= -big_filter.
    rewrite addrAC [X in << X *g _ >>]addrC; symmetry.
    rewrite (eq_bigr (fun p => coeff p D)); last by move=> p _; rewrite degU.
    rewrite {1}[D]div_sumE addrC [X in _ :~: X]addrC -big_filter.
    set ps := [seq p <- dom D | p != ∞].
    have oncve_ps: all oncurve ps.
      apply/allP=> p; rewrite mem_filter => /andP [_ p_in_D].
      by move/allP/(_ p p_in_D): oncve.
    elim: ps oncve_ps => [|p ps IH] /=.
      by rewrite !big_nil !add0r freegUD addrCA subrr addr0; reflexivity.
    case/andP=> oncve_p oncve_ps; rewrite !big_cons;
      set px  := (iterop _ _ _ _);
      set psx := \big[\+%G/∞]_(_ <- _ | _) _.
    rewrite -[<<_ \+ _>>]addr0 -{2}(subrr <<∞>>) !addrA -lrline; first 1 last.
    + by apply: oncurve_natmul.
    + apply/oncurve_sum/allP => q q_in_ps /=; apply/oncurve_natmul.
      by move/allP/(_ q q_in_ps): oncve_ps.
    rewrite -addrA IH // -/psx; set s := \sum_(_ <- _) _.
    rewrite -!freegUD !addrA; do 3! apply/ecdeqv_addl.
    rewrite addrC [<<px>>+_]addrC -!addrA; apply/ecdeqv_addr.
    rewrite [-_+_]addrC freegUB {}/px {}/psx.
    set k := coeff _ _; have k_ge0: k >= 0 by move/fgposP/(_ p): D_ge0.
    rewrite {1 3}[k]intEsign ltrNge k_ge0 expr0 mul1r.
    move: {k_ge0} k => k; move: (absz _) => {k} n; rewrite /iterop.
    set f := fun n q => _; have oncve_it k: oncurve (iteri k f ∞).
      by apply: oncurve_natmul.
    elim: n => [|n IHn] //=.
      by rewrite freegU0 sub0r -freegUN subrr; reflexivity.
    case: n IHn => [|n].
      by move=> _; rewrite subrr freegU0 addr0; reflexivity.
    set r := (iteri _ _ _); have: oncurve r by apply: oncve_it.
    move: r => {oncve_it} r oncve_r IHn; rewrite {}/f.
    rewrite -{1}addn1 PoszD -freegUD IHn /= !subzn // !subn1 /=.
    rewrite addrAC [<<r>> + _]addrC lrline // -addrA.
    rewrite freegUD -PoszD add1n; reflexivity.
  Qed.

  Lemma ecdeqv_lr D: all oncurve (dom D) ->
    D :~: << lr D >> + << deg D - 1 *g ∞ >>.
  Proof.
    move=> oncve; rewrite {1}[D]fg_decomp /lr.
    set rP := lr_r (fgpos D); set rN := lr_r (fgneg D).
    have oncveP: all oncurve (dom (fgpos D)).
      by apply/allP=> p /fgpos_dom; move/allP/(_ p): oncve.
    have oncveN: all oncurve (dom (fgneg D)).
      by apply/allP=> p /fgneg_dom; move/allP/(_ p): oncve.
    have oncve_rP: oncurve rP by apply: oncurve_lr_r.
    have oncve_rN: oncurve rN by apply: oncurve_lr_r.
    rewrite {1}[fgpos D]ecdeqv_lr_r ?fgpos_le0 //.
    rewrite {1}[fgneg D]ecdeqv_lr_r ?fgneg_le0 //.
    rewrite -/rP -/rN opprD addrCA -addrA freegUB.
    rewrite opprD opprK [deg _ - _ + _]addrAC !addrA.
    rewrite -degB -fg_decomp [_ - 1]addrAC [_+1]addrC.
    rewrite -freegUD !addrA; apply: ecdeqv_addl.
    rewrite [-_+_]addrC -[<<rN>>]subr0 -(ecdeqv_lineS oncve_rN).
    rewrite !opprD !opprK !addrA [_ + <<rN>>]addrAC.
    rewrite -[_ - <<rN>>]addrA subrr addr0 lrline -?oncurveN //.
    rewrite -!addrA -[X in _ :~:X]addr0; apply: ecdeqv_addr.
    rewrite addrCA freegUD -PoszD addrC freegUB subrr.
    by rewrite freegU0; reflexivity.
  Qed.

  Lemma ecnorm_lr_le1 D: ecnorm (<< lr D >> + << deg D - 1 *g ∞ >>) <= 1.
  Proof.
    rewrite /lr; move: (_ \- _)=> x; case: (x =P ∞) => [->|].
    + by rewrite freegUD ecnormU eqxx mulr0 ler01.
    + move/eqP=> x_neq0; case: (deg D - 1 =P 0) => [->|].
        by rewrite freegU0 addr0 ecnormU x_neq0 mulr1.
      move/eqP=> pdegD_neq0; rewrite ecnormD; last first.
        move=> p; rewrite !inE domU1 domU // !mem_seq1.
        by apply/negP=> /andP [/eqP->]; rewrite (negbTE x_neq0).
      by rewrite !ecnormU x_neq0 eqxx !(mulr0, mulr1) addr0.
  Qed.

  Lemma ecnorm_lr_deg0_le1 D: deg D = 0 ->
    ecnorm (<< lr D >> - << ∞ >>) <= 1.
  Proof.
    move=> degD_eq0; move: (ecnorm_lr_le1 D).
    by rewrite degD_eq0 sub0r -freegUN.
  Qed.

  Lemma ecdeqv_lr_deg0 (D : {freeg (point K)}):
    deg D = 0 -> all oncurve (dom D) ->
      D :~: (<< lr D >> - << ∞ >>).
  Proof.
    move=> degD_eq0 oncveD; rewrite {1}(ecdeqv_lr oncveD).
    by rewrite degD_eq0 sub0r -freegUN; reflexivity.
  Qed.

  Lemma ecdeqv_lr_deg0_uniq (D : {freeg point K}) (p : point K):
       deg D = 0 -> all oncurve (dom D)
    -> D :~: (<< p >> - << ∞ >>)
    -> p = lr D.
  Proof.
    move=> degD_eq0 oncve; rewrite {1}[D]ecdeqv_lr_deg0 //.
    by move/ecdeqv_addIl/(L_2_40 closedK)/esym.
  Qed.

  Lemma lr0: lr 0 = ∞.
  Proof.
    rewrite /lr fgposE fgnegE dom0 !big_nil.
    by rewrite /lr_r dom0 !big_nil.
  Qed.

  Lemma lrD D1 D2:
    deg D1 = 0 -> all oncurve (dom D1) ->
    deg D2 = 0 -> all oncurve (dom D2) ->
    lr (D1 + D2) = lr D1 \+ lr D2.
  Proof.
    move=> degD1_eq0 oncveD1 degD2_eq0 oncveD2.
    have lrD1 := (ecdeqv_lr_deg0 degD1_eq0 oncveD1).
    have lrD2 := (ecdeqv_lr_deg0 degD2_eq0 oncveD2).
    have := ecdeqv_add lrD1 lrD2; rewrite addrCA !addrA.
    rewrite [<<lr D2>>+_]addrC lrline; first 1 last.
    + by apply: oncurve_lr. + by apply: oncurve_lr.
    rewrite -[X in _ :~: X - _]addrA subrr addr0.
    move/ecdeqv_lr_deg0_uniq/esym; apply.
    + by rewrite degD degD1_eq0 degD2_eq0.
    + apply/allP=> p /domD_subset; rewrite mem_cat; case/orP.
      * by move/allP/(_ p): oncveD1.
      * by move/allP/(_ p): oncveD2.
  Qed.

  Lemma lrN D:
    deg D = 0 -> all oncurve (dom D) -> lr (-D) = \- (lr D).
  Proof.
    move=> degD_eq0 oncveD; have lrD := (ecdeqv_lr_deg0 degD_eq0 oncveD).
    have := ecdeqv_opp lrD; rewrite opprD opprK.
    have ->: <<lr D>> :~: -<<\- (lr D)>> + <<2%:Z *g ∞>>.
    + have /ecdeqv_lineS: oncurve (lr D) by apply oncurve_lr.
      by case=> f fE; exists f; rewrite fE subr0 opprD opprK addrA.
    rewrite opprD opprK -addrA freegUN freegUD.
    have ->: -2%:Z + 1 = -1 by [].
    rewrite -freegUN => /ecdeqv_lr_deg0_uniq/esym; apply.
    + by apply/eqP; rewrite degN oppr_eq0 degD_eq0.
    + by apply/allP=> p; rewrite domN => pD; move/allP/(_ p pD): oncveD.
  Qed.

  Lemma lrB D1 D2:
    deg D1 = 0 -> all oncurve (dom D1) ->
    deg D2 = 0 -> all oncurve (dom D2) ->
    lr (D1 - D2) = lr D1 \- lr D2.
  Proof.
    move=> degD1_eq0 oncveD1 degD2_eq0 oncveD2; rewrite lrD ?lrN //.
    + by apply/eqP; rewrite degN oppr_eq0 degD2_eq0.
    + by apply/allP=> p; rewrite domN => pD; move/allP/(_ p pD): oncveD2.
  Qed.

  Lemma oncurve_lrpi p:
    oncurve p -> all oncurve (dom (<<p>> - <<∞>> : {freeg point _})).
  Proof.
    case: (p =P ∞) => [->|/eqP]; first by rewrite subrr dom0.
    move=> nz_p oncve; apply/allP=> q /domD_subset; rewrite mem_cat.
    by case/orP; rewrite ?domN domU1 mem_seq1 => /eqP ->.
  Qed.

  Lemma lrpi p: oncurve p -> lr (<<p>> - <<∞>>) = p.
  Proof.
    move=> oncve_p; move: (ecdeqv_refl E (<<p>> - <<∞>>)).
    move/ecdeqv_lr_deg0_uniq => {2}-> //.
    + by rewrite degB !degU subrr.
    + by apply: oncurve_lrpi.
  Qed.
End LinearReduction.
