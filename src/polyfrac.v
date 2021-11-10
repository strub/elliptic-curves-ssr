(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype fintype.
From mathcomp Require Import ssrfun choice seq tuple bigop ssralg.
From mathcomp Require Import ssrint ssrnum generic_quotient order.
(* ------- *) Require Import polyall fraction fracfield ssrring.

Import GRing.Theory.
Import Num.Theory.
Import Order.POrderTheory.
Import Order.TotalTheory.
Import fraction.FracField.
Import fracfield.FracField.
Import Monoid.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Reserved Notation "x %:PP"     (at level 2, format "x %:PP").
Reserved Notation "[ 'inf' ]"  (at level 0, format "[ 'inf' ]").
Reserved Notation "{ 'pp' T }" (at level 0, format "{ 'pp'  T }").

Reserved Notation "f .[! x ]" (at level 2, format "f .[! x ]").

Declare Scope polyfrac_scope.
Delimit Scope polyfrac_scope with F.

Module FracInterp.
Section Defs.
  Variable G : idomainType.

  (*~option G / use newType instead ? *)
  Inductive gproj (G : Type) : Type := GP_Finite of G | GP_Inf.

  Arguments GP_Inf {G}.

  Implicit Types p : gproj G.

  Definition gproj_eq p1 p2 :=
    match p1, p2 with
    | GP_Inf     , GP_Inf      => true
    | GP_Finite x, GP_Finite y => x == y
    | _          , _           => false
    end.

  Lemma gproj_eqP : forall p1 p2, reflect (p1 = p2) (gproj_eq p1 p2).
  Proof.
    by move=> [p1|] [p2|]; apply: (iffP idP) => //= [/eqP ->|[->]].
  Qed.

  Definition gproj_eqMixin := EqMixin gproj_eqP.
  Canonical gproj_eqtype := EqType (gproj G) gproj_eqMixin.

  Definition gproj_code   p : option G := if p is GP_Finite p then Some p      else None.
  Definition gproj_decode x : gproj  G := if x is Some x      then GP_Finite x else GP_Inf.

  Lemma gproj_codeK : cancel gproj_code gproj_decode.
  Proof. by case. Qed.

  Definition gproj_choiceMixin := CanChoiceMixin gproj_codeK.
  Canonical gproj_choiceType := Eval hnf in (ChoiceType _ gproj_choiceMixin).

  Definition zero := GP_Finite (0 : G).
  Definition one  := GP_Finite (1 : G).

  Definition add p1 p2 :=
    match p1, p2 with
    | GP_Inf     , _
    | _          , GP_Inf      => GP_Inf
    | GP_Finite x, GP_Finite y => GP_Finite (x + y)
    end.

  Definition opp p :=
    if p is GP_Finite x then GP_Finite (-x) else GP_Inf.

  Definition mul p1 p2 :=
    match p1, p2 with
    | GP_Inf     , GP_Inf      => GP_Inf
    | GP_Finite x, GP_Inf
    | GP_Inf     , GP_Finite x => if x == 0 then GP_Finite 0 else GP_Inf
    | GP_Finite x, GP_Finite y => GP_Finite (x * y)
    end.

  Lemma add0p : left_id zero add.
  Proof.
    by move=> [p|] //=; rewrite !simpm.
  Qed.

  Lemma addp0 : right_id zero add.
    by move=> [p|] //=; rewrite !simpm.
  Qed.

  Lemma addC : commutative add.
  Proof.
    by move=> [p1|] [p2|] //=; rewrite addrC.
  Qed.

  Lemma addA : associative add.
  Proof.
    by move=> [p1|] [p2|] [p3|] //=; rewrite addrA.
  Qed.

  Canonical gproj_monoid := Law addA add0p addp0.
  Canonical gproj_comoid := ComLaw addC.

  Lemma oppK : involutive opp.
  Proof. by case=> [p|] //=; rewrite opprK. Qed.

  Lemma mul0p : left_zero zero mul.
  Proof. by move=> [p|] /=; rewrite !(simpm, eqxx). Qed.

  Lemma mulp0 : right_zero zero mul.
  Proof. by move=> [p|] /=; rewrite !(simpm, eqxx). Qed.

  Lemma mul1p : left_id one mul.
  Proof.
    by move=> [p|] /=; rewrite ?(simpm, oner_eq0).
  Qed.

  Lemma mulp1 : right_id one mul.
    by move=> [p|] /=; rewrite ?(simpm, oner_eq0).
  Qed.

  Lemma mulC : commutative mul.
  Proof.
    by move=> [p1|] [p2|] //=; rewrite mulrC.
  Qed.

  Lemma mulA : associative mul.
  Proof.
    move=> [p1|] [p2|] [p3|] //=; rewrite ?simpm //.
    + have [->|nz_p1] := eqVneq p1 0.
      * by case: (p2 == 0); rewrite !simpm !eqxx.
      have [->|nz_p2] := eqVneq p2 0.
      * by rewrite simpm eqxx.
      by rewrite mulf_eq0 !(negbTE nz_p1, negbTE nz_p2).
    + have [->|nz_p3] := eqVneq p3 0.
      * by rewrite simpm mulp0.
      case: (p1 == 0); rewrite /= ?simpm //.
      by rewrite (negbTE nz_p3).
    + by case: (p1 == 0)=> //=; rewrite eqxx.
    + by rewrite mulf_eq0; case: (p2 == 0)=> //=; rewrite simpm.
    + by case: (p3 == 0); rewrite ?eqxx.
  Qed.

  Canonical gproj_mul_monoid := Law mulA mul1p mulp1.
  Canonical gproj_mul_comoid := ComLaw mulC.

  Canonical gproj_muloid := MulLaw mul0p mulp0.

  Notation "x %:PP"    := (GP_Finite x).
  Notation "[ 'inf' ]" := (GP_Inf).

  Definition gginv p :=
    match p with
    | GP_Finite x => if x == 0 then GP_Inf else GP_Finite (x^-1)
    | GP_Inf      => GP_Finite 0
    end.

  Definition isfinite p := if p is GP_Finite _ then true else false.

  Lemma isfiniteE p: isfinite p = (p != [inf]).
  Proof. by case: p. Qed.

  Definition project p := if p is GP_Finite x then x else 0.

  Definition sgp p : int := nosimpl (
    match p with
    | GP_Finite x => if x == 0 then 0 else 1
    | GP_Inf      => -1
    end).

  Lemma sgp0: sgp 0%:PP = 0.
  Proof. by rewrite /sgp eqxx. Qed.

  Lemma sgpc c: c != 0 -> sgp c%:PP = 1.
  Proof. by move=> nz_c; rewrite /sgp (negbTE nz_c). Qed.

  Lemma sgpi: sgp [inf] = -1.
  Proof. by []. Qed.

  Definition gproj_i (P : gproj G -> Prop):
       (P 0%:PP)
    -> (forall c, c != 0 -> P c%:PP)
    -> (P [inf])
    -> forall x, P x.
  Proof.
    move=> P0 Pc Pi; case=> [x|//]; case: (x =P 0).
      by move=> ->; apply: P0. by move/eqP/Pc.
  Qed.

  Lemma finite_sgp_le0 x: isfinite x -> sgp x >= 0.
  Proof.
    elim/gproj_i: x => [|c nz_c|] //= _.
      by rewrite sgp0. by rewrite sgpc.
  Qed.
End Defs.

Notation "{ 'pp' T }" := (gproj T).
Notation "x %:PP"     := (GP_Finite x) : ring_scope.
Notation "[ 'inf' ]"  := (GP_Inf    _) : ring_scope.

(* -------------------------------------------------------------------- *)
Section Theory.
  Variable R : idomainType.

  Local Notation "+%G" := (@FracInterp.add R).
  Local Notation "*%G" := (@FracInterp.mul R).
  Local Notation "%%G" := (@GP_Finite R).

  Local Notation "x \+ y" := (FracInterp.add x y).
  Local Notation "x \* y" := (FracInterp.mul x y) (at level 30).

  Lemma ggD: {morph %%G : x y / x + y >-> x \+ y}.
  Proof. by []. Qed.

  Lemma ggM: {morph %%G : x y / x * y >-> x \* y}.
  Proof. by []. Qed.
End Theory.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'polyratio' T }" (at level 0, format "{ 'polyratio'  T }").

Section PolyRatioDef.
  Variable R : fieldType.

  Definition polyratio_axiom (x : {ratio {poly R}}) :=
    (coprimep \n_x \d_x) && (\d_x \is monic).

  Record polynomialfrac := PolyRatio {
    polyratio :> {ratio {poly R}};
    _ : polyratio_axiom polyratio
  }.

  Definition polyratio_of of phant R := polynomialfrac.
  Local Notation pfrac := (polyratio_of (Phant R)).
  Identity Coercion type_pfrac_of : polyratio_of >-> polynomialfrac.

  Lemma coprime_polyratio (x : pfrac) : coprimep \n_x \d_x.
  Proof. by case: x=> pf /= /andP []. Qed.

  Lemma monic_polyratio (x : pfrac) : \d_x \is monic.
  Proof. by case: x=> pf /= /andP []. Qed.
End PolyRatioDef.

Notation "{ 'polyratio' T }" := (polyratio_of (Phant T)) (format "{ 'polyratio'  T }").

(* -------------------------------------------------------------------- *)
Section PolyRatioCanonize.
  Local Notation "p %:T" := (lead_coef p).

  Variable R : fieldType.

  Definition reducep (x : {ratio {poly R}}) : {ratio {poly R}} :=
    let: g      := gcdp \n_x \d_x in
    let: (n, d) := (\n_x %/ g, \d_x %/ g) in
    let: lc     := lead_coef d in

      Ratio (lc^-1 *: n) (lc^-1 *: d).

  Lemma reducep_axiom: forall r, polyratio_axiom (reducep r).
  Proof.
    case=> [[n d] /= nz_d]; rewrite /reducep /= /polyratio_axiom /=.
    rewrite /Ratio /insubd insubT /=.
      rewrite scaler_eq0 invr_eq0 lead_coef_eq0.
      by rewrite dvdp_div_eq0 ?(negbTE nz_d) // dvdp_gcdr.
    rewrite scaler_eq0 invr_eq0 => /norP [nz_lcg nz_gcd].
    rewrite monicE lead_coefZ mulrC divff // eqxx andbT.
    rewrite ?(coprimepZl, coprimepZr) ?invr_eq0 //.
    have [->|nz_n] := eqVneq n 0.
      by rewrite gcd0p div0p divpp // coprime0p eqpxx.
    by rewrite coprimep_div_gcd ?(nz_d, nz_n).
  Qed.

  Definition Reducep (p : {ratio {poly R}}) := @PolyRatio _ (reducep p) (reducep_axiom p).

  Lemma reducep_eqmod: forall r, reducep r = r %[mod {fraction {poly R}}].
  Proof.
    case=> [[n d] /= nz_d]; rewrite /reducep /=; set g := (gcdp _ _).
    rewrite /Ratio /insubd insubT /=.
      rewrite scaler_eq0 invr_eq0 lead_coef_eq0 dvdp_div_eq0.
        by rewrite (negbTE nz_d).
      by rewrite dvdp_gcdr.
    move=> nz_g; apply/eqmodP; rewrite /= /equivf /=.
    apply/eqP; rewrite -!scalerAl; congr (_ *: _).
    by rewrite mulrC divp_mulCA 1?mulrC // ?(dvdp_gcdl, dvdp_gcdr).
  Qed.

  Lemma polyratio_axiom_uniq:
    forall r1 r2, polyratio_axiom r1 -> polyratio_axiom r2 ->
      r1 = r2 %[mod {fraction {poly R}}] -> r1 = r2.
  Proof.
    case=> [[n1 d1] /= nz_d1] [[n2 d2] /= nz_d2] /=.
    case/andP=> /= [cop1 mon_d1] /andP /= [cop2 mon_d2].
    move/eqmodP; rewrite /= /equivf /= => /eqP eq.
    have eqp_d: d1 %= d2.
    + rewrite coprimep_sym in cop1; rewrite coprimep_sym in cop2.
      rewrite /eqp -(Gauss_dvdpr _ cop1) -(Gauss_dvdpl _ cop2).
      by rewrite eq dvdp_mulIl /= -eq dvdp_mulIr.
    have eqp_n: n1 %= n2.
    + by move: (eqp_mulr n2 eqp_d); rewrite -eq mulrC eqp_mul2l.
    case/eqpP: eqp_d => [[c1 c2]] /= /andP [nz_c1 nz_c2] eq_d.
    have/(congr1 lead_coef) := eq_d; rewrite !lead_coefZ.
    rewrite (monicP mon_d1) (monicP mon_d2) !mulr1.
    move=> eq_c; move: eq_d; rewrite eq_c => /(scalerI nz_c2).
    move=> {c1 c2 nz_c1 nz_c2 eq_c} eq_d.
    move: eq; rewrite {1}eq_d mulrC => /(mulfI nz_d2) eq_n.
    by apply/eqP; rewrite eqE /= eq_d eq_n.
  Qed.

  Lemma reducep_eq r1 r2:
    r1 = r2 %[mod {fraction {poly R}}] -> reducep r1 = reducep r2.
  Proof.
    move=> eq; apply: polyratio_axiom_uniq;
      last 1 [by rewrite !reducep_eqmod] || by apply: reducep_axiom.
  Qed.

  Lemma reducep_id r: reducep (reducep r) = reducep r.
  Proof. by apply: reducep_eq; apply: reducep_eqmod. Qed.

  Lemma polyfracW (P : {fraction {poly R}} -> Type):
       (forall (f : {polyratio R}), P (\pi_{fraction {poly R}} f))
    -> forall f, P f.
  Proof.
    move=> IH; elim/quotW=> f; move: (IH (Reducep f)).
    by rewrite reducep_eqmod.
  Qed.

  Lemma fracredW (P : {fraction {poly R}} -> Type):
       (forall (n d : {poly R}), coprimep n d -> d \is monic -> P (n // d))
    -> forall f, P f.
  Proof.
    move=> H; elim/polyfracW; case=> [[[n d] /= nz_d]] /andP [cop_nd mon_d].
    move: (embed_Ratio n d); rewrite /Ratio /insubd insubT /= => <-.
    by apply: H.
  Qed.
End PolyRatioCanonize.

(* -------------------------------------------------------------------- *)
Section Interp.
  Variable R : fieldType.

  Definition finterp (x : R) (p : {ratio {poly R}}) :=
    if \n_p == 0 then GP_Finite 0 else
      let m := minn (\mu_x \n_p) (\mu_x \d_p) in
        let n := \n_p %/ ('X - x%:P) ^+ m in
        let d := \d_p %/ ('X - x%:P) ^+ m in
          if d.[x] == 0 then [inf] else (n.[x] / d.[x])%:PP.

  Definition interp x := lift_fun1 {fraction {poly R}} (finterp x).

  Lemma pi_interp x:
    {mono \pi_{fraction {poly R}} : f / finterp x f >-> interp x f}.
  Proof.
    move=> f2; unlock interp; set f1 := (repr _).
    have: (f1 = f2 %[mod {fraction _}]) by rewrite reprK.
    case: f2 f1 => [[n2 d2] /= nz_d2] [[n1 d1] /= nz_d1] /=.
    move/eqmodP => /=; rewrite FracField.equivfE /= => eqE.
    rewrite /finterp /=; move/negbTE: nz_d1 => nz_d1; move/negbTE: nz_d2 => nz_d2.
    case z_n1: (n1 == 0); case z_n2: (n2 == 0) => //=.
    + by move: eqE; rewrite (eqP z_n1) eq_sym mul0r mulf_eq0 nz_d1 z_n2.
    + by move: eqE; rewrite (eqP z_n2) mulr0 mulf_eq0 nz_d2 z_n1.
    move/(congr1 (\mu_x)): (eqP eqE).
    rewrite !mu_mul ?mulf_eq0 ?(z_n1, z_n2, nz_d1, nz_d2) // => mu_eq.
    rewrite /minn; case: (ltnP _ _) => mu_1; case: (ltnP _ _) => mu_2.
    + rewrite -!rootE -!mu_gt0; first last.
      * by rewrite divp_rootn ?nz_d1 1?ltnW.
      * by rewrite divp_rootn ?nz_d2 1?ltnW.
      by rewrite !mu_div ?subn_gt0 ?(mu_1, mu_2) // 1?ltnW.
    + by move: mu_1; rewrite -(ltn_add2r (\mu_x d2)) mu_eq ltn_add2l ltnNge mu_2.
    + by move: mu_2; rewrite -(ltn_add2l (\mu_x n1)) mu_eq ltn_add2r ltnNge mu_1.
    rewrite -!rootE -!mu_gt0 ?divp_rootn // ?(nz_d1, nz_d2) //.
    rewrite !mu_div // !subn_gt0 !ltnn.
    congr (GP_Finite _); apply/eqP; rewrite divff_eq; last first.
    + by rewrite mulf_neq0 // -rootE rootN_div_mu //; apply/negbT.
    set tx := ('X - _); apply/eqP; rewrite -!hornerM; congr (_.[x]).
    rewrite [X in _ = X]mulrC; apply/(mulfI (x := tx ^+ (\mu_x d1))).
    + by rewrite expf_neq0 // polyXsubC_eq0.
    rewrite mulrCA mulrA le_mu_divp_mul //.
    rewrite mulrCA mulrA mu_divp_mul.
    apply/(mulIf (x := tx ^+ (\mu_x d2))).
    + by rewrite expf_neq0 // polyXsubC_eq0.
    by rewrite -!mulrA mu_divp_mul le_mu_divp_mul // (eqP eqE).
  Qed.

  Canonical pi_interp_morph x := PiMono1 (pi_interp x).

  Local Notation "f .[! x ]" := (interp x f) : ring_scope.

  Definition finterp_red (x : R) (p q : {poly R}) :=
    if q.[x] == 0 then [inf] else GP_Finite (p.[x] / q.[x]).

  Lemma finterp_cop_nzdenE (x : R) (n d : {poly R}):
    coprimep n d -> d.[x] != 0 -> interp x (n // d) = (n.[x] / d.[x])%:PP.
  Proof.
    move=> cop_nd nz_dx; have nz_d: d != 0.
      apply/eqP=> /(congr1 (horner^~ x)) /eqP.
      by rewrite horner0 (negbTE nz_dx).
    rewrite !piE /finterp !numden_Ratio //; have [->|nz_n] := altP (n =P 0).
      by rewrite horner0 mul0r.
    set k := minn _ _; have ->: k = 0%N.
      by rewrite {}/k [\mu_x d]muNroot.
    by rewrite expr0 !divp1 (negbTE (nz_dx)).
  Qed.

  Lemma finterp_copE (x : R) (n d : {poly R}):
    coprimep n d -> d != 0 -> interp x (n // d) = finterp_red x n d.
  Proof.
    move=> cop_nd nz_d; rewrite /finterp_red; case: (boolP (d.[x] == 0)); last first.
      by move=> nz_dx; apply: finterp_cop_nzdenE.
    move=> z_dx; rewrite !piE /finterp !numden_Ratio //.
    case: (boolP (n == 0)) cop_nd => [/eqP->|nz_n].
      rewrite coprime0p => /eqp_root /(_ x) /esym.
      by rewrite [root d x]rootE z_dx (negbTE (root1 _)).
    move=> cop_nd; set k := minn _ _; have {k}->: k = 0%N.
      rewrite {}/k muNroot ?min0n // rootE.
      by apply: (coprimep_root (p := d)) => //; rewrite coprimep_sym.
    by rewrite expr0 !divp1 z_dx.
  Qed.

  CoInductive finterp_spec (x : R) (p q : {poly R}): bool -> {pp R} -> Type :=
  | FINZDenEval of q.[x] != 0                                   : finterp_spec x p q false (p.[x] / q.[x])%:PP
  | FINMuGt     of q.[x] == 0 & (\mu_x p >  \mu_x q)%N & p != 0 : finterp_spec x p q true  0%:PP
  | FINMuLt     of q.[x] == 0 & (\mu_x p <  \mu_x q)%N & p != 0 : finterp_spec x p q true  [inf]
  | FINMuLtZNum of q.[x] == 0 & (\mu_x p <  \mu_x q)%N & p == 0 : finterp_spec x p q true  0%:PP
  | FINMuEq     of q.[x] == 0 & (\mu_x p == \mu_x q)%N
                   : finterp_spec x p q true ( (p %/ ('X - x%:P) ^+ (\mu_x p)).[x]
                                             / (q %/ ('X - x%:P) ^+ (\mu_x q)).[x])%:PP.

  Lemma finterpP x p q: q != 0 -> finterp_spec x p q (q.[x] == 0) (p // q).[!x].
  Proof.
    move=> nz_q; rewrite embed_Ratio !piE /finterp.
    rewrite !numden_Ratio //; case: (boolP (q.[x] == 0)); last first.
      move=> nz_qx; move: (FINZDenEval p nz_qx); case: (p =P 0) => [->|_].
        by rewrite horner0 mul0r.
      by rewrite minnC muNroot // min0n expr0 !divp1 (negbTE nz_qx).
    move=> z_qx; case: (p =P 0) => [->|/eqP nz_p].
      by apply: FINMuLtZNum => //; rewrite mu0 mu_gt0.
    case: (ltngtP (\mu_x p) (\mu_x q)) => [lt_mu_pq|gt_mu_pq|eq_mu].
    + set tx := (_ ^+ (\mu__ _)); have z_qdx: root (q %/ tx) x.
        rewrite -mu_gt0 ?divp_rootn //; last by rewrite ltnW.
        by rewrite mu_div ?subn_gt0 // ltnW.
      by rewrite (eqP z_qdx) eqxx; apply: FINMuLt.
    + set tx := (_ ^+ (\mu__ _)); have nz_qdx: (q %/ tx).[x] != 0.
        by rewrite (rootPf (rootN_div_mu x nz_q)).
      have z_pdx: root (p %/ tx) x.
        rewrite -mu_gt0 ?divp_rootn //; last by rewrite ltnW.
        by rewrite mu_div ?subn_gt0 // ltnW.
      by rewrite (negbTE nz_qdx) (eqP z_pdx) mul0r; apply: FINMuGt.
    + rewrite eq_mu (rootPf (rootN_div_mu x nz_q)).
      by rewrite -{1}eq_mu; apply: FINMuEq; last apply/eqP.
  Qed.

  Lemma finterp_nzden (x : R) (p q : {poly R}):
    q.[x] != 0 -> (p // q).[!x] = (p.[x] / q.[x])%:PP.
  Proof.
    move=> nz_qx; have nz_q: q != 0.
      apply/negP=> /eqP /(congr1 (horner^~ x)).
      by rewrite horner0 => /eqP; rewrite (negbTE nz_qx).
    by move: nz_qx; case: finterpP.
  Qed.

  Lemma finterp_nznum (x : R) (p q : {poly R}):
    q != 0 -> p.[x] != 0 -> (p // q).[!x] = finterp_red x p q.
  Proof.
    move=> nz_q nz_px; rewrite /finterp_red /=; case: finterpP => //=.
    + by move=> z_qx; rewrite [\mu_x p]muNroot.
    + by move=> _ _ /eqP z_p; rewrite z_p horner0 eqxx in nz_px.
    + move=> z_qx; rewrite muNroot // eq_sym eqn0Ngt mu_gt0 //.
      by rewrite rootE z_qx.
  Qed.

  Lemma finterp_poly (x : R) (p : {poly R}): (p%:F).[!x] = (p.[x])%:PP.
  Proof.
    by rewrite -[p%:F]divr1 finterp_nzden !hornerE ?oner_neq0 // divr1.
  Qed.

  Lemma finterp0 (x : R): 0.[!x] = 0%:PP.
  Proof. by rewrite finterp_poly horner0. Qed.

  Lemma finterp1 (x : R): 1.[!x] = 1%:PP.
  Proof. by rewrite finterp_poly hornerC. Qed.

  Lemma finterpC (x : R) (c : R): (c%:P)%:F.[!x] = c%:PP.
  Proof. by rewrite finterp_poly hornerC. Qed.

  Local Notation "x \+ y" := (FracInterp.add x y).
  Local Notation "x \* y" := (FracInterp.mul x y) (at level 30).

  Lemma finterpDfl (x : R) (f1 f2 : {fraction {poly R}}):
    isfinite f1.[!x] -> (f1 + f2).[!x] = f1.[!x] \+ f2.[!x].
  Proof.
    elim/fracredW: f1 => n1 d1 cop_n1d1 mon_d1.
    elim/fracredW: f2 => n2 d2 cop_n2d2 mon_d2.
    have nz_d1: d1 != 0 by apply: monic_neq0.
    have nz_d2: d2 != 0 by apply: monic_neq0.
    rewrite addf_div ?tofrac_eq0 // -!(tofracM, tofracD).
    set v := ((_ + _) // _).[!_]; rewrite !finterp_copE /finterp_red //.
    case: eqP => [//|/eqP nz_d1x _]; case: (boolP (d2.[x] == 0)); last first.
      move=> nz_d2x; rewrite /v finterp_nzden ?hornerM ?mulf_neq0 //.
      by rewrite !hornerE /= addf_div.
    move=> z_d2x /=; rewrite {}/v finterp_nznum ?mulf_neq0 //=.
      by rewrite /finterp_red hornerM mulf_eq0 z_d2x orbT.
    rewrite !hornerE (eqP (z_d2x)) mulr0 add0r mulf_neq0 //.
    by apply: (coprimep_root (p := d2)) => //; rewrite coprimep_sym.
  Qed.

  Lemma finterpDfr (x : R) (f1 f2 : {fraction {poly R}}):
    isfinite f2.[!x] -> (f1 + f2).[!x] = f1.[!x] \+ f2.[!x].
  Proof. by rewrite addrC addC => /finterpDfl. Qed.

  Lemma finterpM (x : R) (f1 f2 : {fraction {poly R}}):
       (sgp f1.[!x] + sgp f2.[!x])%R >= 0%R
    -> (f1 * f2).[!x] = f1.[!x] \* f2.[!x].
  Proof.
    wlog: f1 f2 / (sgp f1.[!x] <= sgp f2.[!x]).
      move=> wlog posi; case: (lerP (sgp f1.[!x]) (sgp f2.[!x])).
        by move/wlog => /(_ posi).
      by move/ltW => /wlog; rewrite addrC mulrC mulC; apply.
    elim/fracredW: f1 => n1 d1 cop_n1d1 mon_d1.
    elim/fracredW: f2 => n2 d2 cop_n2d2 mon_d2.
    have nz_d1: d1 != 0 by apply: monic_neq0.
    have nz_d2: d2 != 0 by apply: monic_neq0.
    rewrite mulf_div -!tofracM; set v := ((_ * _) // _).[!_].
    rewrite !finterp_copE /finterp_red // /sgp.
    case: (boolP (d1.[x] == 0)); case: (boolP (d2.[x] == 0)) => //=.
    + move=> nz_d2x z_d1x _; rewrite mulf_eq0 invr_eq0.
      rewrite (negbTE nz_d2x) orbF /=; case: (boolP (n2.[x] == 0))=> //=.
      move=> nz_n2x _; rewrite /v finterp_nznum ?mulf_neq0 //; last first.
        rewrite hornerM mulf_neq0 //. apply: (coprimep_root (p := d1)) => //.
        by rewrite coprimep_sym.
      * by rewrite /finterp_red /= hornerM (eqP z_d1x) mul0r eqxx.
    + by move=> _ _; case: (_ == 0).
    + move=> nz_d2x nz_d1x _ _; rewrite /v finterp_nzden; last first.
        by rewrite hornerM mulf_neq0.
      by rewrite !hornerE /= mulrAC invfM -!mulrA [_ * n2.[x]]mulrC.
  Qed.

  Lemma finterpMf (x : R) (f1 f2 : {fraction {poly R}}):
       isfinite f1.[!x]
    -> isfinite f2.[!x]
    -> (f1 * f2).[!x] = f1.[!x] \* f2.[!x].
  Proof.
    move/finite_sgp_le0=> sgp1; move/finite_sgp_le0=> sgp2.
    by apply: finterpM; rewrite addr_ge0.
  Qed.

  Lemma finterp_eqinf (x : R) (p q : {poly R}): p != 0 ->
    (root q x && (\mu_x p < \mu_x q)%N) = ((p // q).[!x] == [inf]).
  Proof.
    move=> nz_p; have [->|nz_q] := eqVneq q 0.
      by rewrite root0 mu0 invr0 mulr0 finterp0.
    case: finterpP => //= nz_qx.
    + by rewrite rootE (negbTE nz_qx).
    + by move/ltnW; rewrite leqNgt andbC => /negbTE ->.
    + by move=> -> _; rewrite rootE (eqP nz_qx) eqxx.
    + by rewrite (negbTE nz_p).
    + by move/eqP=> ->; rewrite ltnn andbF.
  Qed.
End Interp.
End FracInterp.

Notation "{ 'pp' T }" := (FracInterp.gproj T).
Notation "x %:PP"     := (FracInterp.GP_Finite x) : ring_scope.
Notation "[ 'inf' ]"  := (FracInterp.GP_Inf    _) : ring_scope.
Notation gproject     := FracInterp.project.

Notation "f .[! x ]" := (FracInterp.interp x f) : ring_scope.

(* -------------------------------------------------------------------- *)
Section PolyFracMap.
  Variable aR rR : fieldType.

  Definition map_polyfrac (f : aR -> rR) (r : {fraction {poly aR}}) : {fraction {poly rR}} :=
    rlift (map_poly f) r.

  Variable f : {rmorphism aR -> rR}.

  Lemma map_poly_is_rimorphism: injrmorphism (map_poly f).
  Proof.
    split; [exact: map_poly_is_rmorphism | exact: map_poly_inj].
  Qed.
  Canonical map_poly_rimorphism := InjRMorphism map_poly_is_rimorphism.

  Lemma map_polyfracF p: map_polyfrac f p%:F = (map_poly f p)%:F.
  Proof. exact: rliftF. Qed.

  Lemma map_polyfracE p q: map_polyfrac f (p // q) = (map_poly f p) // (map_poly f q).
  Proof. exact: rliftE. Qed.

  Lemma map_polyfrac_is_additive: additive (map_polyfrac f).
  Proof. exact: rlift_is_additive. Qed.
  Canonical map_polyfrac_additive := Additive map_polyfrac_is_additive.

  Lemma map_polyfrac_is_multiplicative: multiplicative (map_polyfrac f).
  Proof. exact: rlift_is_multiplicative. Qed.
  Canonical map_polyfrac_rmorhism := AddRMorphism map_polyfrac_is_multiplicative.
End PolyFracMap.

(* -------------------------------------------------------------------- *)
Section PolyFracComp.
  Variable R : fieldType.

  Definition comp_poly_polyfrac (p : {poly R}) (f : {fraction {poly R}}) :=
    (map_poly ((tofrac (R := _)) \o polyC) p).[f].

  Definition comp_polyfrac (f g : {fraction {poly R}}) : {fraction {poly R}} :=
    gproject (map_polyfrac ((tofrac (R := _)) \o polyC) f).[!g].
End PolyFracComp.

Reserved Notation "p \PFo f" (at level 50).
Reserved Notation "f \Fo g"  (at level 50).

Notation "p \PFo f" := (comp_poly_polyfrac p f).
Notation "f \Fo g"  := (comp_polyfrac f g).

(* -------------------------------------------------------------------- *)
Section PolyFracDeg.
  Variable R : idomainType.

  Definition fdeg_r (f : {ratio {poly R}}) : int :=
    if \n_f == 0 then 0 else (size \n_f)%:Z - (size \d_f)%:Z.

  Definition fdeg := lift_fun1 {fraction {poly R}} fdeg_r.

  Local Notation sizep := (size : {poly _} -> _).

  Lemma pi_fdeg: {mono \pi_{fraction {poly R}} : f / fdeg_r f >-> fdeg f}.
  Proof.
    move=> f; unlock fdeg; set g := (repr _); apply/eqP.
    have: (f = g %[mod {fraction _}]) by rewrite reprK.
    case: f g => [[nf df] /= nz_df] [[ng dg] /= nz_dg].
    move/eqmodP=> /=; rewrite equivfE /fdeg_r /=.
    case: (boolP (nf == 0)) => [/eqP->|].
      by rewrite mul0r eq_sym mulf_eq0 (negbTE nz_df) => /= ->.
    move=> nz_nf; case: (boolP (ng == 0)) => [/eqP->|].
      by rewrite mulr0 mulf_eq0 (negbTE nz_dg) (negbTE nz_nf).
    move=> nz_ng => /eqP /(congr1 sizep); rewrite !size_mul //.
    move/(congr1 S); rewrite !prednK ?addr_cross; first last.
    + by rewrite addn_gt0 lt0n size_poly_eq0 nz_nf.
    + by rewrite addn_gt0 lt0n size_poly_eq0 nz_df.
    by rewrite -!PoszD => ->; rewrite addnC.
  Qed.

  Canonical pi_fdeg_morph := PiMono1 pi_fdeg.

  Lemma fdegE (n d : {poly R}):
    n * d != 0 -> fdeg (n // d) = (size n)%:Z - (size d)%:Z.
  Proof.
    rewrite mulf_eq0 => /norP [nz_n nz_d].
    by rewrite embed_Ratio !piE /fdeg_r !numden_Ratio // (negbTE nz_n).
  Qed.

  Lemma fdegF (p : {poly R}): fdeg p%:F = (size p).-1.
  Proof.
    rewrite !piE /Ratio /insubd insubT ?oner_eq0 //=.
    rewrite /fdeg_r /= => _; case: (boolP (p == 0)).
      by move/eqP=> ->; rewrite size_poly0.
    move=> nz_p; rewrite size_poly1 -subn1 subzn //.
    by rewrite lt0n size_poly_eq0.
  Qed.

  Lemma fdeg0: fdeg 0 = 0.
  Proof. by rewrite -tofrac0 fdegF size_poly0. Qed.

  Lemma fdegC (c : R): fdeg (c%:P)%:F = 0.
  Proof. by rewrite fdegF size_polyC; case: (_ == _). Qed.

  Lemma fdegN (f : {fraction {poly R}}): fdeg (-f) = fdeg f.
  Proof.
    elim/fracW: f => n d nz_d; case: (boolP (n == 0)) => [/eqP->|].
      by rewrite !mul0r oppr0.
    move=> nz_n; rewrite -mulNr -tofracN.
    by rewrite !fdegE ?(mulf_neq0, oppr_eq0) // size_opp.
  Qed.

  Lemma Posz_maxn: {morph Posz : n m / (maxn n m)%N >-> Num.max n m}.
  Proof.
    move=> n m; rewrite /maxn /Num.max ltz_nat.
    by rewrite ltnNge; case: (_ <= _)%N.
  Qed.

  Lemma Posz_minn: {morph Posz : n m / (minn n m)%N >-> Num.min n m}.
  Proof.
    move=> n m; rewrite /minn /Num.min ltz_nat ltn_neqAle andbC.
    by case: ltnP => //= _; case: eqP => [->|].
  Qed.

  Lemma fdegDl (f1 f2 : {fraction {poly R}}):
    f1 != 0 -> fdeg f2 < fdeg f1 -> fdeg (f1 + f2) = fdeg f1.
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1; elim/fracW: f2 => n2 d2 nz_d2.
    rewrite mulf_eq0 invr_eq0 !tofrac_eq0 => /norP [nz_n1 _].
    case: (boolP (n2 == 0)) => [/eqP->|]; first by rewrite !mul0r addr0.
    move=> nz_n2; rewrite !fdegE ?mulf_neq0 //= => nz_sz.
    rewrite addf_div ?tofrac_eq0 // -!(tofracM, tofracD).
    have nzD: size (n1 * d2 + n2 * d1) = size (n1 * d2).
      rewrite size_addl // -ltz_nat !size_mul // !predn_int; first last.
      + by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_n2).
      + by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_n1).
      rewrite ltr_add2r !PoszD [X in _ < X]addrC.
      rewrite -(ltr_add2r (-(size d1)%:Z)) -addrA subrr addr0.
      by rewrite -(ltr_add2l (-(size d2)%:Z)) !addrA addNr add0r addrC.
    rewrite fdegE ?mulf_neq0 //; last first.
      rewrite -size_poly_eq0 nzD size_poly_eq0 mulf_eq0.
      by rewrite (negbTE nz_n1) (negbTE nz_d2).
    rewrite nzD !size_mul // !predn_int; first last.
    + by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_n1).
    + by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_d1).
    rewrite !PoszD addrAC !opprD -!addrA opprK subrr addr0.
    by rewrite [X in _ + X]addrCA subrr addr0.
  Qed.

  Lemma fdegD (f1 f2 : {fraction {poly R}}):
    f1 + f2 != 0 -> fdeg (f1 + f2) <= Num.max (fdeg f1) (fdeg f2).
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1; elim/fracW: f2 => n2 d2 nz_d2.
    case: (boolP (n1 == 0)) => [/eqP->|nz_n1].
      by rewrite !(mul0r, add0r) lexU lexx orbT.
    case: (boolP (n2 == 0)) => [/eqP->|nz_n2].
      by rewrite !(mul0r, addr0) lexU lexx.
    rewrite addf_div ?tofrac_eq0 // -!(tofracM, tofracD).
    rewrite !(mulf_eq0, invr_eq0, tofrac_eq0).
    rewrite (negbTE nz_d1) (negbTE nz_d2) !orbF => nz_p.
    rewrite !fdegE ?mulf_neq0 // size_mul //.
    move: (size_add (n1 * d2) (n2 * d1)).
    rewrite -lez_nat Posz_maxn !size_mul // 2?predn_int; first last.
    + by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_n1).
    + by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_n2).
    rewrite -addr_maxl -(ler_add2r (- (size d1 + size d2).-1%:Z)).
    rewrite addrAC -addrA predn_int; last first.
      by rewrite lt0n addn_eq0 size_poly_eq0 (negbTE nz_d1).
    rewrite opprB addrAC subrr sub0r addr_maxl !PoszD.
    rewrite [(_ + _) - _]addrAC {2}opprD -2!addrA addNr addr0.
    rewrite {2}opprD -!addrA [-_ - _]addrC.
    by rewrite [_ + (-_ - _)]addrCA subrr addr0.
  Qed.

  Lemma fdegM (f1 f2 : {fraction {poly R}}):
    f1 * f2 != 0 -> fdeg (f1 * f2) = (fdeg f1) + (fdeg f2).
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1; elim/fracW: f2 => n2 d2 nz_d2.
    rewrite !(mulf_eq0, invr_eq0, tofrac_eq0) !(negbTE nz_d1, negbTE nz_d2).
    rewrite !orbF => /norP [nz_n1 nz_n2].
    rewrite mulf_div -!tofracM !fdegE ?mulf_neq0 //.
    rewrite !size_mul // !predn_int; first last.
    + by rewrite addn_gt0 lt0n size_poly_eq0 nz_n1.
    + by rewrite addn_gt0 lt0n size_poly_eq0 nz_d1.
    by rewrite !PoszD; ssring.
  Qed.
End PolyFracDeg.

(* -------------------------------------------------------------------- *)
Reserved Notation "f1 %F= f2" (at level 70, format "f1  %F=  f2").

Section PolyFracPropt.
  Variable R : idomainType.

  Definition eqf_r (f1 f2 : {ratio {poly R}}) :=
    \n_f1 * \d_f2 %= \n_f2 * \d_f1.

  Definition eqf := lift_fun2 {fraction {poly R}} eqf_r.

  Local Notation domP := denom_ratioP.

  Lemma pi_eqf: {mono \pi_{fraction {poly R}} : f1 f2 / eqf_r f1 f2 >-> eqf f1 f2}.
  Proof.
    move=> f1 f2 /=; unlock eqf; rewrite /eqf_r /=.
    rewrite -(eqp_mul2l (r := \d_f1)) ?domP // mulrA -equivf_r.
    rewrite mulrAC !mulrA eqp_mul2r ?domP // [X in _ %= X]mulrC.
    rewrite -(eqp_mul2l (r := \d_f2)) ?domP // !mulrA -equivf_r.
    by rewrite [X in _ %= X]mulrAC eqp_mul2r ?domP // [X in X %= _]mulrC.
  Qed.

  Canonical pi_eqf_mono := PiMono2 pi_eqf.

  Local Notation "f1 %F= f2" := (eqf f1 f2).

  Local Notation "c %:PF" := (c%:P)%:F (at level 2, format "c %:PF").

  Lemma eqf0 (f : {fraction {poly R}}): (f %F= 0) = (f == 0).
  Proof.
    elim/fracW: f => n d nz_d; rewrite !piE /eqf_r equivfE.
    by rewrite !numden_Ratio ?oner_eq0 // !simpm eqp0.
  Qed.

  Lemma eqf_sym: symmetric eqf.
  Proof.
    elim/fracW=> n1 d1 nz_d1; elim/fracW=> n2 d2 nz_d2.
    by rewrite !piE /eqf_r eqp_sym.
  Qed.

  Lemma eqfE (n1 d1 n2 d2 : {poly R}):
    d1 * d2 != 0 -> (n1 // d1 %F= n2 // d2) = (n1 * d2 %= n2 * d1).
  Proof.
    rewrite mulf_eq0 => /norP [nz_d1 nz_d2].
    by rewrite !piE /eqf_r !numden_Ratio.
  Qed.

  Lemma eqfP (f1 f2 : {fraction {poly R}}):
    reflect
      (exists2 c : R * R,
        (c.1 != 0) && (c.2 != 0) & c.1%:PF * f1 = c.2%:PF * f2)
      (f1 %F= f2).
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1; elim/fracW: f2 => n2 d2 nz_d2.
    have H c:
         ((c.1)%:PF *  (n1 // d1) == (c.2)%:PF *  (n2 // d2))
      =  ((c.1)     *: (n1  * d2) == (c.2)     *: (n2  * d1)).
    + by rewrite !mulrA -!tofracM !mul_polyC frac_eq ?mulf_neq0 // !scalerAl.
    rewrite eqfE ?mulf_neq0 //; apply: (iffP idP).
    + by move/eqpP=> [c nz_c eq]; exists c => //; apply/eqP; rewrite H eq.
    + by case=> [c nz_c eq]; apply/eqpP; exists c => //; apply/eqP; rewrite -H eq.
  Qed.
End PolyFracPropt.

Notation "f1 %F= f2" := (eqf f1 f2).

Section PolyFracProptField.
  Variable K : fieldType.

  Local Notation "c %:PF" := (c%:P)%:F (at level 2, format "c %:PF").

  Lemma eqffP (f1 f2 : {fraction {poly K}}):
    reflect (exists2 c : K, c != 0 & f1 = c%:PF * f2) (f1 %F= f2).
  Proof.
    apply: (iffP idP) => [/eqfP [c nz_c eq]|[c nz_c eq]].
    + exists (c.2 / c.1).
        by rewrite mulf_eq0 invr_eq0 negb_or andbC.
      case/andP: nz_c => nz_c1 nz_c2; apply/(mulfI (x := c.1%:PF)).
        by rewrite tofrac_eq0 polyC_eq0.
      rewrite eq mulrCA !mulrA; congr (_ * f2).
      by rewrite -!tofracM -polyCM mulrAC -mulrA divff // mulr1.
    + apply/eqfP; exists (1, c) => /=; first by rewrite oner_eq0.
      by rewrite mul1r.
  Qed.
End PolyFracProptField.

(* -------------------------------------------------------------------- *)
Section PolyFracDeriv.
  Variable R : idomainType.

  Definition fderivf (f : {ratio {poly R}}) : {ratio {poly R}}
    := Ratio (\n_f^`() * \d_f - \n_f * \d_f^`()) (\d_f^+2).

  Definition fderiv := lift_op1 {fraction {poly R}} fderivf.

  Local Notation "f ^` ()" := (fderiv f) : polyfrac_scope.

  Lemma pi_fderiv : {morph \pi_{fraction {poly R}} : f / fderivf f >-> fderiv f}.
  Proof.
    move=> f2; unlock fderiv; set f1 := (repr _).
    have: (f1 = f2 %[mod {fraction _}]) by rewrite reprK.
    case: f2 f1 => [[n2 d2] /= nz_d2] [[n1 d1] /= nz_d1] /=.
    move/eqmodP=> /=; rewrite equivfE /fderivf /= => /eqP eq.
    apply/eqmodP; rewrite /= equivfE /= !numden_Ratio ?expf_neq0 //.
    rewrite !(mulrDr, mulrDl, mulNr, mulrN).
    have ->: n2 * d2^`() * d1^+2   = n1 * d2 * d1  * d2^`() by rewrite  eq; ssring.
    have ->: d2^+2 * (n1 * d1^`()) = d1 * n2 * d2 * d1^`()  by rewrite -eq; ssring.
    move/(congr1 (@deriv _)): eq; rewrite !derivE => /eqP.
    rewrite [X in _ == X]addrC -subr_eq => /eqP/esym eq.
    rewrite [X in X - _ == _]mulrAC !mulrA [n2^`()*d1]mulrC.
    by apply/eqP; rewrite eq; ssring.
  Qed.

  Canonical pi_fderiv_morph := PiMorph1 pi_fderiv.

  Lemma fderivE n d: ((n // d)^`())%F = (n^`() * d - n * d^`()) // d^+2.
  Proof.
    have [->|nz_d] := eqVneq d 0.
      rewrite embed_Ratio !piE Ratio0 /fderivf /= !simpm.
      by rewrite deriv0 subrr !(simpm, oppr0) !Ratio0r.
    by rewrite embed_Ratio !piE /fderivf !numden_Ratio.
  Qed.

  Lemma fderivF p: ((p%:F)^`())%F = (p^`())%:F.
  Proof.
    rewrite -[_%:F]divr1 -[1]tofrac1 fderivE.
    by rewrite derivC mulr0 subr0 mulr1 expr1n divr1.
  Qed.

  Lemma fderivC c: (((c%:P)%:F)^`())%F = 0.
  Proof. by rewrite fderivF derivC. Qed.

  Lemma fderiv_is_additive: {morph fderiv : f1 f2 / f1 - f2 >-> f1 - f2}.
  Proof.
    elim/fracW=> n1 d1 nz_d1; elim/fracW=> n2 d2 nz_d2.
    rewrite -mulNr -tofracN addf_div ?tofrac_eq0 //.
    rewrite -!(tofracD, tofracM) mulNr !fderivE.
    rewrite -[X in _=_+X]mulNr -tofracN addf_div ?(tofrac_eq0, expf_neq0) //.
    rewrite -!(tofracD, tofracM); congr (_ // _); last by rewrite exprMn.
    by rewrite !derivE; ssring.
  Qed.

  Canonical fderiv_additive := Additive fderiv_is_additive.

  Lemma fderiv0     : fderiv 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma fderivN     : {morph fderiv: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma fderivD     : {morph fderiv: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma fderivB     : {morph fderiv: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma fderivMn  n : {morph fderiv: x / x *+ n} . Proof. exact: raddfMn. Qed.
  Lemma fderivMNn n : {morph fderiv: x / x *- n} . Proof. exact: raddfMNn. Qed.

  Lemma fderivM (f1 f2 : {fraction {poly R}}):
    ((f1 * f2)^`())%F = f1^`()%F * f2 + f1 * f2^`()%F.
  Proof.
    elim/fracW: f1 => n1 d1 nz_d1; elim/fracW: f2 => n2 d2 nz_d2.
    rewrite mulf_cross -invfM -!tofracM !fderivE.
    do 2! rewrite mulf_cross -invfM -!tofracM.
    set x1 := ((_ - _) * n2); set x2 := (n1 * (_ - _)).
    have ->: x1 // (d1 ^+ 2 * d2) = (x1 * d2) // (d1 * d2)^+2.
      rewrite exprMn [d2^+_]expr2 !mulrA ![(_*d2)%:F]tofracM.
      by rewrite -mulf_div divff ?tofrac_eq0 // mulr1.
    have ->: x2 // (d1 * d2 ^+ 2) = (x2 * d1) // (d1 * d2)^+2.
      rewrite ![d1*_]mulrC exprMn [d2^+_]expr2 !mulrA ![(_*d1)%:F]tofracM.
      by rewrite -mulf_div divff ?(tofrac_eq0, mulr1).
    by rewrite -mulrDl -tofracD; congr (_ // _); rewrite !derivE; ssring.
  Qed.
End PolyFracDeriv.

(* -------------------------------------------------------------------- *)
Require Import polydec.

Section FinterpAllFinite.
  Variable K : closedFieldType.

  Import FracInterp.

  (*XXX*)
  Lemma finterp_all_finite n d:
     n // d != 0 ->
     (forall x : K, isfinite ((n // d).[!x]))
  -> exists p, n = p * d.
  Proof.
  move=> nd_Nz eval_fin.
  have := nd_Nz; rewrite mulf_eq0 invr_eq0 !tofrac_eq0.
  case/norP=> nNz dNz.
  have Hmu x : (\mu_x d <= \mu_x n)%N.
  case: (@FracInterp.finterpP K x n d).
  + by [].
  + move/rootP; move/rootP=> Nrootdx.
    move: (@cofactor_XsubC_mu K x d 0 Nrootdx).
    rewrite expr0 mulr1 => ->.
    rewrite leq0n //.
  + move=> _ Hmu _; by apply: ltnW.
  + move => h1 h2 h3.
    move: (eval_fin x); rewrite isfiniteE.
    by rewrite -(finterp_eqinf _) // rootE h1 h2.
  + move=> _ _ n0; move: nNz; by rewrite (eqP n0) eqxx.
  + move=> _ eq; by rewrite (eqP eq) leqnn.
  exists (n %/ d); rewrite {1}(divp_eq n d).
  rewrite -[X in _ = X]addr0; congr (_ + _).
  apply/modp_eq0P; rewrite [d]roots_factor_theorem_f //.
  rewrite dvdpZl ?lead_coef_eq0 //.
  apply: roots_dvdp; apply/allP=> x x_root_d /=.
  by rewrite -roots_mu.
  Qed.
End FinterpAllFinite.

(* -------------------------------------------------------------------- *)
Section PolyFracCnt.
  Variable R : idomainType.

  Definition isfcnt_r (f : {ratio {poly R}}) := (\n_f == 0) || (\n_f %= \d_f).

  Definition isfcnt := lift_fun1 {fraction {poly R}} isfcnt_r.

  Lemma pi_isfcnt: {mono \pi_{fraction {poly R}} : f / isfcnt_r f >-> isfcnt f}.
  Proof.
    move=> f; unlock isfcnt; set g := (repr _); apply/eqP.
    have: (f = g %[mod {fraction _}]) by rewrite reprK.
    case: f g => [[nf df] /= nz_df] [[ng dg] /= nz_dg].
    move/eqmodP; rewrite /= equivfE /isfcnt_r /= => /eqP eq.
    apply/eqP; congr (_ || _).
    + move/esym/(congr1 (eq_op^~ 0)): eq.
      by rewrite !mulf_eq0 (negbTE nz_df) (negbTE nz_dg) !(orbF, orFb).
    + by rewrite -(eqp_mul2r (r := df)) // mulrC -eq mulrC eqp_mul2l.
  Qed.

  Canonical isfnct_mono := PiMono1 pi_isfcnt.

  Lemma isfcntE (n d : {poly R}): n != 0 -> d != 0 -> (isfcnt (n // d)) = (n %= d).
  Proof.
    by move=> nz_n nz_d; rewrite !piE /isfcnt_r !numden_Ratio // (negbTE nz_n).
  Qed.

  Lemma isfcnt0: isfcnt 0.
  Proof.
    by rewrite !piE /isfcnt_r !numden_Ratio ?oner_eq0 // eqxx.
  Qed.

  Lemma isfnctC (n d : R): isfcnt (n%:P // d%:P).
  Proof.
    have [->|nz_n] := altP (n =P 0); first by rewrite tofrac0 mul0r isfcnt0.
    have [->|nz_d] := altP (d =P 0); first by rewrite tofrac0 invr0 mulr0 isfcnt0.
    rewrite isfcntE ?polyC_eq0 //; apply/eqpP; exists (d, n) => /=.
    + by rewrite nz_d nz_n.
    + by rewrite -!mul_polyC mulrC.
  Qed.

  Lemma isfcntP (f : {fraction {poly R}}):
    reflect (exists2 c : R * R, c.2 != 0 & f = (c.1)%:P // (c.2)%:P) (isfcnt f).
  Proof.
    elim/fracW: f => n d nz_d; have [->|nz_n] := altP (n =P 0).
      rewrite mul0r isfcnt0; constructor; exists (0, 1) => /=.
        by rewrite oner_eq0. by rewrite tofrac0 mul0r.
    rewrite isfcntE //; apply: (iffP idP).
    + move/eqpP=> [[c1 c2] /=] /andP [nz_c1 nz_c2] /(congr1 (@tofrac _)).
      move/eqP; rewrite -!mul_polyC !tofracM mulrC -divff_eq; last first.
        by rewrite mulf_neq0 // tofrac_eq0 ?polyC_eq0.
      by move/eqP=> ->; exists (c2, c1).
    + case=> [[c1 c2] /= nz_c2] /eqP; rewrite frac_eq ?mulf_neq0 ?polyC_eq0 //.
      rewrite mulrC !mul_polyC => /eqP /esym eq;apply/eqpP; exists (c2, c1) => //=.
      rewrite nz_c2 /=; move/(congr1 (eq_op^~ 0)): eq.
      rewrite -!mul_polyC !mulf_eq0 !polyC_eq0 (negbTE nz_c2) /=.
      by rewrite (negbTE nz_d) (negbTE nz_n) orbF => ->.
  Qed.

  Lemma isfnctN_size (n d : {poly R}):
    ~~ (isfcnt (n // d)) -> (size n > 1)%N || (size d > 1)%N.
  Proof.
    have [->|nz_n] := altP (n =P 0); first by rewrite mul0r isfcnt0.
    have [->|nz_d] := altP (d =P 0); first by rewrite invr0 mulr0 isfcnt0.
    rewrite isfcntE // !ltnNge /= ![(size _ <= _)%N]leq_eqVlt.
    rewrite !ltnS !leqn0 !size_poly_eq0 (negbTE nz_n) (negbTE nz_d) !orbF.
    rewrite !size_poly_eq1 -negb_and => eqpN_nd; apply/negP.
    rewrite andbC => /andP []; rewrite eqp_sym => eqp_d_1 /eqp_trans.
    by move/(_ _ eqp_d_1); rewrite (negbTE eqpN_nd).
  Qed.
End PolyFracCnt.

Section PolyFracCntField.
  Variable K : fieldType.

  Lemma isfcntfP (f : {fraction {poly K}}):
    reflect (exists c : K, f = (c%:P)%:F) (isfcnt f).
  Proof.
    apply: (iffP idP).
    + move/isfcntP; case=> [[c1 c2] /= nz_c2 Ef]; exists (c1 / c2).
      rewrite Ef polyCM -polyCV tofracM tofracrV //.
      by rewrite poly_unitE coefC eqxx unitfE size_polyC nz_c2.
    + case=> c Ef; apply/isfcntP; exists (c, 1) => /=.
        by rewrite oner_eq0. by rewrite tofrac1 divr1.
  Qed.
End PolyFracCntField.

(* -------------------------------------------------------------------- *)
Section PolyFracCompTheory.
  Variable K : fieldType.

  Local Notation PF := ((@tofrac _) \o polyC).

  Import FracInterp.

  Lemma comp_ppf0 (f : {fraction {poly K}}): 0 \PFo f = 0.
  Proof. by rewrite /comp_poly_polyfrac map_poly0 horner0. Qed.

  Lemma comp_0f (f : {fraction {poly K}}): 0 \Fo f = 0.
  Proof. by rewrite /comp_polyfrac rmorph0 finterp0. Qed.

  Lemma comp_poly_fracE (p : {poly K}) (A B : {poly K}): B != 0 ->
      p \PFo (A // B)
    = (\sum_(i < size p) p`_i *: (A ^+ i * B ^+ (size p - i.+1))) // (B ^+ (size p).-1).
  Proof.
    move=> nz_B; rewrite /comp_poly_polyfrac; elim/poly_ind: p => [|p c IH].
      by rewrite size_poly0 big_ord0 map_poly0 horner0 mul0r.
    have [->|nz_p] := altP (p =P 0); first rewrite mul0r add0r.
      rewrite map_polyC /= hornerC; have [->|nz_c] := altP (c =P 0).
        by rewrite tofrac0 size_poly0 big_ord0 mul0r.
      rewrite size_polyC nz_c big_ord_recl big_ord0.
      by rewrite coefC eqxx subnn !expr0 invr1 !simpm alg_polyC.
    do! rewrite !(rmorphM, rmorphD, map_polyC, map_polyX) /=.
    rewrite !hornerE size_MXaddC (negbTE nz_p) /= big_ord_recl.
    rewrite coefD coefC coefMX !eqxx add0r expr0 mul1r subSS subn0.
    rewrite [X in _ = X // _]addrC tofracD mulrDl -mul_polyC.
    rewrite tofracM -[X in _ = _ + X]mulrA mulfV ?mulr1; last first.
      by rewrite tofrac_eq0 expf_eq0 lt0n size_poly_eq0 nz_p.
    pose F (i : 'I_(size p)) := A * (p`_i *: (A ^+ i * B ^+ (size p - i.+1))).
    rewrite (eq_bigr F); last first.
      move=> i _; rewrite lift0 coefD coefMX coefC /= addr0 subSS.
      by rewrite exprS -mulrA scalerAr.
    rewrite {}/F -big_distrr /= tofracM -!mulrA mulrCA.
    congr (_ * _ + _); rewrite IH -mulrA -invfM -tofracM.
    by rewrite [_ * B]mulrC -exprS prednK // lt0n size_poly_eq0.
  Qed.

  Lemma L (p q : {poly K}) (n : nat) (rs : n.-tuple K):
       coprimep p q
    -> (size p > 1)%N || (size q > 1)%N
    -> has (predC1 0) rs
    -> \sum_(i < n) ((tnth rs i) *: (p ^+ i * q ^+ (n-i.+1))) != 0.
  Proof.
    wlog: p q n rs / (size p > 1)%N.
      move=> wlog cop_pq sz_pq nz_rs; have := sz_pq.
      case/orP; first by move/wlog; apply.
      move=> sz_q; set rs' := [tuple of (rev rs)].
      have nz_rs': has (predC1 0) rs'.
        case/hasP: nz_rs=> x x_in_rs /= nz_x.
        by apply/hasP; exists x => //=; rewrite mem_rev.
      rewrite 1?coprimep_sym 1?orbC in cop_pq, sz_pq.
      move: (wlog q p n rs' sz_q cop_pq sz_pq nz_rs').
      rewrite (reindex_inj rev_ord_inj) /= => neq.
      apply/negP=> eq; apply: (negP neq); rewrite -{2}(eqP eq).
      apply/eqP; apply: eq_bigr => i _.
      rewrite mulrC subnSK // subKn 1?ltnW // /rs'.
      rewrite !(tnth_nth 0) /= nth_rev ?size_tuple ?rev_ord_proof //.
      by rewrite subnSK // subKn 1?ltnW.
    move=> sz_p cop_pq _; have nz_p: p != 0.
      by rewrite -size_poly_eq0 -lt0n ltnW.
    have nz_q: q != 0.
      case: (q =P 0) cop_pq => [->/=|//].
        by rewrite coprimep0 -size_poly_eq1 eqn_leq leqNgt sz_p.
    case: rs=> /= rs sz_rs nz_rs.
    pose F (i : 'I_n) : {poly K} := rs`_i *: (p ^+ i * q ^+ (n-i.+1)).
    rewrite (eq_bigr F); last first.
      by move=> i _; rewrite (tnth_nth 0).
    rewrite {}/F; elim: rs nz_rs n sz_rs => [//|r rs IH] /=.
    have [->|nz_r] := altP (r =P 0) => /=.
      move=> nz_rs n /eqP <-; rewrite big_ord_recl /= scale0r add0r.
      pose F (i : 'I_(size rs)) := p * (rs`_i *: (p ^+ i * q ^+ ((size rs) - i.+1))).
      rewrite (eq_bigr F); last first.
        by move=> i _; rewrite /bump /= add1n subSS exprS -mulrA scalerAr.
      by rewrite {}/F -big_distrr /= mulf_eq0 (negbTE nz_p) /=; apply: IH.
    move=> _ n /eqP <-; rewrite big_ord_recl /=.
    move: (size rs) => {IH} k; rewrite expr0 mul1r subn1 /=.
    rewrite -[X in _ + X]opprK subr_eq0 -sumrN.
    pose F (i : 'I_k) := p * ((-rs`_i) *: (p ^+ i * q ^+ (k - i.+1))).
    rewrite (eq_bigr F); last first.
      move=> i _; rewrite -scaleNr /bump /= add1n subSS.
      by rewrite exprS -mulrA scalerAr.
    rewrite {}/F -big_distrr /=; apply/negP => /eqP /esym.
    set S := (\sum_(i < k) _) => eq.
    have: p %| (r *: q ^+ k.+1).
      apply/dvdpP; exists (q * S) => /=.
      by rewrite -mulrA [S * _]mulrC eq -scalerAr exprS.
    rewrite dvdpZr // => dvd_p_qSk.
    have := cop_pq; rewrite -(coprimep_pexpr (k := k.+1)) //.
    move/coprimepP => -/(_ p (dvdpp _) dvd_p_qSk).
    by rewrite -size_poly_eq1 eqn_leq leqNgt sz_p.
  Qed.

  Lemma comp_poly_frac_Nfcnt_neq0 (p : {poly K}) (f : {fraction {poly K}}):
    p != 0 -> ~~ (isfcnt f) -> (p \PFo f) != 0.
  Proof.
    elim/FracInterp.fracredW: f => n d cop_nd mon_d nz_p.
    pose k := (size p).-1; pose x0 := @inord k 0%N.
    move: x0; rewrite /k prednK => [{k} x0|]; last first.
      by rewrite lt0n size_poly_eq0.
    have [->|nz_n] := altP (n =P 0); first by rewrite mul0r isfcnt0.
    have nz_d: d != 0 by apply: monic_neq0.
    move/isfnctN_size => {mon_d} sz_nd; rewrite comp_poly_fracE //.
    rewrite mulf_eq0 invr_eq0 !tofrac_eq0 expf_eq0 (negbTE nz_d).
    rewrite andbF orbF; pose rs := [tuple p`_i | i < size p].
    have nz_rs: has (predC1 0) rs.
      rewrite /rs /=; set ps := (map _ _); have ->: ps = p.
        rewrite /ps; apply: (eq_from_nth (x0 := 0)).
        + by rewrite size_map size_enum_ord.
        + move=> i; rewrite size_map size_enum_ord => lt_i_szp.
          by rewrite (nth_map x0) ?size_enum_ord // nth_enum_ord.
      apply/hasP; exists (last 1 p).
      + case: rs; case => [|r rs] /=.
        * by rewrite eq_sym size_poly_eq0 (negbTE nz_p).
        * move: (size rs); case: {nz_p ps rs x0} p => p /= _ k.
          by rewrite eq_sym; case: p => [|c p] //=; rewrite mem_last.
      + by case: {nz_p rs ps x0} p.
    move/L: sz_nd => -/(_ (size p) rs cop_nd nz_rs).
    move=> neq; apply/negP=> eq; apply: (negP neq); rewrite -{2}(eqP eq).
    apply/eqP; apply: eq_bigr => i _; rewrite (tnth_nth 0) /rs.
    by rewrite (nth_map x0) ?size_enum_ord // nth_enum_ord.
  Qed.

  Lemma comp_frac_NfcntE (n d : {poly K}) (f : {fraction {poly K}}):
    ~~ (isfcnt f) -> (n // d) \Fo f = (n \PFo f) / (d \PFo f).
  Proof.
    have [->|nz_n] := altP (n =P 0); first by rewrite comp_ppf0 !mul0r comp_0f.
    have [->|nz_d] := altP (d =P 0); first by rewrite comp_ppf0 !invr0 !mulr0 comp_0f.
    move=> Nfcnt_f; rewrite /comp_polyfrac map_polyfracE /=.
    by rewrite finterp_nzden //= comp_poly_frac_Nfcnt_neq0.
  Qed.

  Lemma comp_frac_fcntE (f : {fraction {poly K}}) (c : K):
    f \Fo (c%:P)%:F = ((gproject f.[!c])%:P)%:F.
  Proof.
    elim/fracredW: f => n d cop_nd mon_d; rewrite /comp_polyfrac.
    rewrite map_polyfracE /= !finterp_copE //; first last.
    + by rewrite map_poly_eq0; apply: monic_neq0.
    + by rewrite coprimep_map.
    + by apply: monic_neq0.
    rewrite /finterp_red !horner_map /= !(tofrac_eq0, polyC_eq0).
    have [//|nz_dc] := altP (d.[c] =P 0).
    rewrite polyCM -polyCV tofracM tofracrV //.
    by rewrite poly_unitE coefC eqxx unitfE size_polyC nz_dc.
  Qed.
End PolyFracCompTheory.
