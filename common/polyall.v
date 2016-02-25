(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp
Require Import ssreflect ssrnat ssrbool eqtype ssralg ssrfun.
From mathcomp
Require Import choice seq bigop prime div.
From mathcomp
Require Export poly polydiv.
Require Export polyorder.

Import GRing.Theory.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Local Notation simp := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Section PolyAll.
  Variable R : idomainType.

  Implicit Types p q : {poly R}.

  (* ------------------------------------------------------------------ *)
  Definition coefE := (coefB, coefD , coefN, coefC ,
                       coefZ, coefMn, coefX, coefXn).

  (* ------------------------------------------------------------------ *)
  Lemma polyX_eq0: 'X != 0 :> {poly R}.
  Proof.
    by rewrite -size_poly_eq0 size_polyX.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma polyC_natr: forall n, n%:R%:P = n%:R :> {poly R}.
  Proof.
    by elim=> [|n IH] //=; rewrite -addn1 !natrD polyC_add IH.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma size_poly2P (p : {poly R}):
    reflect (exists2 c : R * R, c.1 != 0 & p = c.1 *: 'X - c.2%:P) (size p == 2).
  Proof.
    apply: (iffP idP); last first.
      case=> [[c1 c2]] /= nz_c1 ->; rewrite size_addl; last first.
        rewrite size_scale // size_polyX size_opp size_polyC.
        by case: (_ == _).
      by rewrite size_scale // size_polyX.
    move=> sz_p; pose c1 := p`_1; pose c0 := p`_0.
    exists (c1, -c0) => /=.
      rewrite /c1 (pred_Sn 1) -(eqP sz_p) /= -lead_coefE.
      by rewrite lead_coef_eq0 -size_poly_eq0 (eqP sz_p).
    apply/polyP=> i; rewrite !coefE; case: i => [|[|i]].
    + by rewrite mulr0 sub0r opprK.
    + by rewrite mulr1 subr0.
    + by rewrite subr0 mulr0 -[p]coefK (eqP sz_p) coef_poly.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma size_addr:
    forall p q,
      size (p + q) < size q -> size p = size q.
  Proof.
    move=> p q; case: (ltngtP (size p) (size q)) => //.
    + by move/size_addl; rewrite addrC=> ->; rewrite ltnn.
    + move=> H; move: (size_addl H)=> -> H'.
      by absurd false=> //; rewrite -(ltnn (size q)) (ltn_trans H).
  Qed.

  Lemma size_add_max p q:
    size p != size q -> size (p + q) = maxn (size p) (size q).
  Proof.
    move=> neq_sz; case sz_cmp: (size q < size p).
      by rewrite size_addl // maxnC /maxn sz_cmp.
    rewrite addrC size_addl; last first.
      by rewrite ltnNge leq_eqVlt sz_cmp orbF eq_sym.
    by rewrite maxnC /maxn sz_cmp.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma polyseq2:
    forall p, size p = 2 ->
        (exists2 r, (r.2 != 0) & (p = [:: r.1; r.2] :> seq R)).
  Proof.
    move=> [/= [//|x1 [//|x2 [//=| ? //]]]].
    by move=> Hx _; exists (x1, x2) => //=.
  Qed.

  Lemma sqpp_sub_polyseq (r : R):
    ('X - r%:P)^+2 = [:: r^+2; - (2%:R * r); 1] :> seq R.
  Proof.
    rewrite mulrDl !simp.
    rewrite sqrrB expr2 mulr2n -mulrDr -mulrBr mulrC.
    rewrite -polyC_exp -polyC_add -cons_poly_def.
    by rewrite polyseq_cons polyseqXsubC.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dvd_factornP p c n:
    (p == (p %/ ('X - c%:P)^+n) * ('X - c%:P)^+n) = (('X - c%:P)^+n %| p).
  Proof.
    rewrite Pdiv.Idomain.dvdp_eq lead_coef_exp lead_coefXsubC.
    by rewrite !expr1n scale1r.
  Qed.

  Lemma divp_rootn n x p:
    p != 0 -> n <= \mu_x p -> p %/ ('X - x%:P)^+n != 0.
  Proof.
    move=> nz_p Hn; case: (@mu_spec _ p x nz_p)=> q Hq Ep.
    rewrite Ep -(subnK Hn) exprD mulrA Pdiv.IdomainMonic.mulpK; last first.
    + by rewrite monic_exp // monicXsubC.
    rewrite mulf_eq0 negb_or expf_eq0 polyXsubC_eq0 andbF andbT.
    apply/negP; move/eqP=> z_q.
    by rewrite z_q mul0r in Ep; rewrite Ep eqxx in nz_p.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma size_id_exp:
    forall n p,
      p != 0 -> size (p ^+ n) = ((n * (size p)) - n).+1%N.
  Proof.
    move=> n p nz_p; elim: n => [|n IH] //.
    + by rewrite !simp expr0 subnn size_polyC oner_neq0.
    rewrite exprS size_mul ?expf_neq0 //.
    rewrite IH addnS /= addnBA -?mulSn -1?subnSK //.
    + by rewrite leq_pmulr // lt0n size_poly_eq0.
    + by rewrite leq_pmulr // lt0n size_poly_eq0.
  Qed.

  Lemma odd_size_id_exp:
    forall n p , p != 0 ->
      odd (size (p ^+ n)) = if odd n then odd (size p) else true.
  Proof.
    move=> n p nz_p; rewrite size_id_exp //=.
    rewrite odd_sub ?leq_pmulr // ?lt0n ?size_poly_eq0 // odd_mul.
    by case: (odd n)=> //=; rewrite addbT negbK.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma mu_divp_mul:
    forall x p,
      p %/ ('X - x%:P)^+(\mu_x p) * ('X - x%:P)^+(\mu_x p) = p.
  Proof.
    move=> x p /=; have [-> | nz_p] := eqVneq p 0.
    + by rewrite div0p mul0r.
    by apply/eqP; rewrite eq_sym dvd_factornP root_mu.
  Qed.

  Lemma le_mu_divp_mul:
    forall x n p,
      n <= \mu_x p -> p %/ ('X - x%:P)^+n * ('X - x%:P)^+n = p.
  Proof.
    move=> x n p le_n_mu; have [-> | nz_p] := eqVneq p 0.
    + by rewrite div0p mul0r.
    by apply/eqP; rewrite eq_sym dvd_factornP root_le_mu.
  Qed.

  Lemma divp_factor_mu_neq0:
    forall x n p,
      p != 0 -> n <= \mu_x p -> p %/ ('X - x%:P)^+n != 0.
  Proof.
    move=> x n p nz_p le_n_mu; apply/negP=> /eqP.
    move/(congr1 ( *%R^~ (('X - x%:P)^+n))).
    rewrite !simp le_mu_divp_mul // => /eqP.
    by rewrite (negbTE nz_p).
  Qed.

  Lemma rootN_div_mu:
    forall x p, p != 0 ->
      ~~(root (p %/ ('X - x%:P) ^+ (\mu_x p)) x).
  Proof.
    move=> z p nz; rewrite -mu_gt0 ?divp_rootn ?(negbT nz) //.
    by rewrite -eqn0Ngt mu_div // subnn.
  Qed.

  Lemma divp_factor_root_neq0 (p : {poly R}) x:
    p != 0 -> root p x -> p %/ ('X - x%:P) != 0.
  Proof.
    move=> nz_p root_p_x; rewrite -['X - _]expr1.
    by apply: divp_factor_mu_neq0 => //; rewrite mu_gt0.
  Qed.

  Lemma mu_factor (x c : R): \mu_x ('X - c%:P) = (x == c).
  Proof.
    have [->|x_neq_c] := eqVneq x c.
    + by rewrite eqxx mu_XsubC.
    apply/eqP; rewrite (negbTE x_neq_c) eqn0Ngt mu_gt0.
    by rewrite root_XsubC. by rewrite polyXsubC_eq0.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma mu_prod (I : Type) (r : seq I) (P : pred I) (F : I -> {poly R}) x:
       \prod_(i <- r | P i) (F i) != 0
    -> \mu_x (\prod_(i <- r | P i) (F i)) = (\sum_(i <- r | P i) (\mu_x (F i)))%N.
  Proof.
    elim: r => [|i r IH]; first by rewrite !big_nil mu_polyC.
    rewrite !big_cons; case: (P i) => nz; last by rewrite IH.
    by rewrite mu_mul // IH //; move: nz; rewrite mulf_eq0; case/norP.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma mu_deriv_char (p : {poly R}) (x : R):
       (forall i, i < size p -> i \notin [char R])
    -> root p x
    -> \mu_x (p^`()) = (\mu_x p - 1)%N.
  Proof.
    move=> chrp z_px; have [->|nz_p] := eqVneq p 0.
      by rewrite derivC mu0.
    have [q nz_qx Ep] := mu_spec x nz_p.
    case Dm: (\mu_x p) => [|m].
      by move: z_px; rewrite Ep Dm mulr1 (negPf nz_qx).
    rewrite subn1 Ep Dm !derivCE mul1r -!pred_Sn.
    rewrite mulrnAr -mulrnAl exprS mulrA -mulrDl.
    rewrite cofactor_XsubC_mu // rootE !(hornerE, hornerMn).
    rewrite subrr mulr0 add0r -mulr_natl mulf_eq0.
    rewrite -rootE negb_or nz_qx andbT natf_neq0.
    rewrite /pnat /=; apply/allP => i; rewrite mem_primes.
    case/and3P=> _ _ /dvdn_leq -/(_ (ltn0Sn _)) => le_i_Sm.
    move/(dvdp_leq nz_p): (root_mu p x); rewrite size_exp_XsubC Dm.
    by move/(leq_ltn_trans le_i_Sm)/chrp.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma lead_coef_prod (I : Type) (r : seq I) (P : pred I) (F : I -> {poly R}):
    lead_coef (\prod_(i <- r | P i) (F i)) = \prod_(i <- r | P i) (lead_coef (F i)).
  Proof.
    elim: r => [|i r IH]; first by rewrite !big_nil lead_coefC.
    by rewrite !big_cons; case: (P i); rewrite 1?lead_coefM IH.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma coprimep_prod p (qs : seq {poly R}):
    coprimep p (\prod_(q <- qs) q) = all [pred q | coprimep p q] qs.
  Proof.
    elim: qs=> [|q qs IH]; first by rewrite big_nil coprimep1.
    by rewrite big_cons coprimep_mulr IH.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma size_scale_leq (c : R) (p : {poly R}):
    size (c *: p) <= size p.
  Proof.
    have [->|nz_c] := eqVneq c 0.
      by rewrite scale0r size_poly0 leq0n.
    by rewrite size_scale.
  Qed.
End PolyAll.

(* -------------------------------------------------------------------- *)
Lemma size_polyf2P (K : fieldType) (p : {poly K}):
  reflect (exists c : K, p %= 'X - c%:P) (size p == 2).
Proof.
  apply: (iffP idP).
  + move/size_poly2P=> [[c1 c2] /= nz_c1 ->].
    exists (c2 / c1); apply/eqpf_eq; exists c1 => //.
    rewrite scalerBr; congr (_ - _); rewrite -mul_polyC polyC_mul.
    rewrite -polyC_inv mulrCA divrr ?mulr1 // poly_unitE.
    by rewrite size_polyC nz_c1 coefC /= unitfE.
  + by case=> c /eqpf_eq [c' nz_c' ->]; rewrite size_scale // size_XsubC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma roots_dvdp (K: fieldType) (p : {poly K}) (cs : seq K):
     all [pred x | count (pred1 x) cs <= \mu_x p] cs
  -> (\prod_(c <- cs) ('X - c%:P)) %| p.
Proof.
  move=> roots; apply/dvdpP; have [->|nz_p] := eqVneq p 0.
    by exists 0; rewrite mul0r.
  elim: cs p nz_p roots => [|c cs IH] p nz_p /=.
    by move=> _; exists p; rewrite big_nil mulr1.
  rewrite eqxx add1n; case/andP=> cs_mu_pc /allP cs_mu_p.
  have/factor_theorem: root p c.
    by move: cs_mu_pc; move/(leq_ltn_trans (leq0n _));
      rewrite mu_gt0.
  case=> q Ep; have := nz_p; rewrite {1}Ep.
    rewrite mulf_eq0 polyXsubC_eq0 orbF => nz_q.
  have mu_pq: forall z, (\mu_z p = \mu_z q + (z == c))%N.
    move=> z; move/(congr1 \mu_z): Ep.
    by rewrite mu_mul ?(mulf_neq0, polyXsubC_eq0) // mu_factor.
  case: (IH q)=> //.
  + apply/allP=> z /cs_mu_p /=; rewrite mu_pq.
    by rewrite eq_sym addnC; rewrite leq_add2r.
  move=> qq Eq; rewrite Ep Eq; exists qq.
  by rewrite big_cons mulrAC mulrA.
Qed.

(* -------------------------------------------------------------------- *)
Lemma copsqr (K : fieldType) (s p q : {poly K}):
  s != 0 -> coprimep p q -> s^+2 = p * q ->
    exists r, p %= r ^+ 2.
  move=> s_neq0 cpq hpq; exists (gcdp p s); set d := gcdp _ _.
  have p_neq0 : p != 0.
    apply: contraNneq s_neq0 => p_eq0.
    by move/eqP: hpq; rewrite p_eq0 mul0r expf_eq0.
  have d_neq0 : d != 0 by rewrite gcdp_eq0 (negPf p_neq0) (negPf s_neq0).
  have dvd_ds: d %| s by rewrite dvdp_gcdr.
  have dvd_dp: d %| p by rewrite dvdp_gcdl.
  have: d ^+ 2 %| s ^+ 2; first by rewrite dvdp_exp2r.
  rewrite hpq Gauss_dvdpl => [hp|]; last first.
    by rewrite (@coprimep_dvdr _ (p ^+ 2)) ?dvdp_exp2r ?coprimep_expl.
  rewrite -(divpK hp) -[X in _ %= X]mul1r eqp_mulr //.
  rewrite (dvdp_eqp1 _ (eqpxx _)) //.
  rewrite -(@Gauss_dvdpl _ _ (s ^+ 2 %/ d ^+ 2)) ?mul1r.
    rewrite -(@dvdp_mul2r _ (d ^+ 2)) ?expf_eq0 //.
    by rewrite !divpK ?dvdp_exp2r // hpq dvdp_mulr.
  rewrite -(divpK dvd_ds) exprMn mulpK ?expf_eq0 // coprimep_expr //.
  rewrite (@coprimep_dvdr _ (p %/ d)) ?coprimep_div_gcd ?p_neq0 //.
  rewrite -(@dvdp_mul2r _ (d ^+ 2)) ?expf_eq0 //.
  by rewrite divpK // mulrA divpK // dvdp_mulr.
Qed.
