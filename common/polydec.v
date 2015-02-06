(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype ssralg ssrfun.
Require Import choice tuple fintype xseq bigop polyall.

Import GRing.Theory.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation simp := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Lemma expr0n (R : ringType) n: 0 ^+ n = (n == 0%N)%:R :> R.
Proof. by case: n => [//|n]; rewrite exprS mul0r. Qed.

Lemma eqr_sqr (R : idomainType) (x y : R):
  (x ^+ 2 == y ^+ 2) = (x == y) || (x == -y).
Proof.
  by rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0.
Qed.

Lemma sqr_eqr_sign (R : idomainType) (x y : R):
  x ^+ 2 = y ^+ 2 -> exists s:bool, x = (-1) ^+ s * y.
Proof.
  move/eqP; rewrite eqr_sqr; case/orP=> /eqP ->.
  + by exists false; rewrite expr0 mul1r.
  + by exists true; rewrite expr1 mulN1r.
Qed.

(* -------------------------------------------------------------------- *)
Lemma root_XnsubC (K : fieldType) n (c k : K):
  (root ('X ^+ n - c%:P) k) = (k ^+ n == c).
Proof.
  by rewrite rootE !(hornerE, horner_exp) subr_eq0.
Qed.

Lemma size_XnsubC (K : fieldType) c n:
  (n > 0)%N -> size (('X : {poly K})^+ n - c%:P) = n.+1.
Proof.
  move=> n_gt0; rewrite size_addl size_polyXn //.
  by rewrite size_opp size_polyC; case: (c == 0).
Qed.

Lemma XnsubC_eq0 (K : fieldType) c n:
  (n > 0)%N -> (('X : {poly K})^+ n - c%:P) != 0.
Proof.
  by move=> n_gt0; rewrite -size_poly_eq0 size_XnsubC.
Qed.

(* -------------------------------------------------------------------- *)
Section PolyDec.
  Variable K : decFieldType.

  Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).
  Local Notation "x =pl y" := (perm_eql x y) (at level 70, no associativity).

  (* ------------------------------------------------------------------ *)
  Definition tm_evalpoly (p : {poly K}) :=
    (foldr (fun c f => f * 'X_0 + c%:T) (0%R)%:T p)%T.

  Definition fm_isroot  (p : {poly K}) := (tm_evalpoly p == (0%R)%:T)%T.
  Definition fm_hasroot (p : {poly K}) := ('exists 'X_0, fm_isroot p)%T.

  Lemma tm_evalpoly_horner p i: GRing.eval i (tm_evalpoly p) = p.[i`_0].
  Proof.
    set v := i`_0; case: p => p Hp; rewrite /horner /tm_evalpoly /=.
    by elim: {Hp} p => [|p ps IH] //=; rewrite IH.
  Qed.

  Lemma fm_isrootP (p : {poly K}) i:
    reflect (GRing.holds i (fm_isroot p)) (root p i`_0).
  Proof.
    by apply: (iffP eqP); rewrite /fm_isroot /= tm_evalpoly_horner.
  Qed.

  Lemma fm_hasrootP (p : {poly K}) i:
    (GRing.holds i (fm_hasroot p)) <-> (exists x, root p x).
  Proof.
    rewrite /fm_hasroot /=; split; case=> [x Hx]; exists x.
    + by move/fm_isrootP: Hx; case: i.
    + by apply/fm_isrootP; case: i.
  Qed.

  Goal forall p,
    reflect (exists x, root p x) (GRing.sat [::] (fm_hasroot p)).
  Proof.
    move=> p; apply: (iffP satP).
    + by move/fm_hasrootP.
    + by move=> ?; apply/fm_hasrootP.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma root1P: forall (p : {poly K}), {x | (root p x)} + {~(exists x, root p x)}.
  Proof.
    move=> p; move: (@satP K [::] (fm_hasroot p)); case.
    + by move/fm_hasrootP=> H; left; exists (xchoose H); apply xchooseP.
    + by move/fm_hasrootP; right.
  Qed.

  Definition hasroot (p : {poly K}) :=
    if root1P p is inleft _ then true else false.

  Lemma root_hasroot: forall p x, root p x -> hasroot p.
  Proof.
    move=> p x; rewrite /hasroot; case: root1P=> //.
    move=> HA root_p_x; absurd False=> //; apply HA.
    by exists x.
  Qed.

  Definition root1 (p : {poly K}) :=
    if   p == 0
    then 0
    else if root1P p is inleft x then projT1 x else 0.

  Lemma root1_root:
    forall (p : {poly K}), hasroot p -> root p (root1 p).
  Proof.
    move=> p; rewrite /root1; have [->|nz_p] := eqVneq p 0.
    + by rewrite eqxx root0.
    + rewrite /hasroot; rewrite (negbTE nz_p).
      by case: (root1P p) => [[x P]|H] _ //=.
  Qed.

  Lemma hasrootP (p : {poly K}):
    reflect (exists x, root p x) (hasroot p).
  Proof.
    apply: (iffP idP).
    + by move/root1_root => H; exists (root1 p).
    + by case=> x; move/root_hasroot.
  Qed.

  Lemma root1_0: root1 0 = 0.
  Proof. by rewrite /root1 eqxx. Qed.

  Lemma root1_factor_theorem:
    forall p, hasroot p ->
      p = (p %/ ('X - (root1 p)%:P)) * ('X - (root1 p)%:P).
  Proof.
    move=> p; have [->|nz_p] := eqVneq p 0.
    + by rewrite div0p mul0r.
    move=> rootp; rewrite -['X - _]expr1 le_mu_divp_mul //.
    by rewrite mu_gt0 // root1_root.
  Qed.

  (* ------------------------------------------------------------------ *)
  Fixpoint roots_rec (p : {poly K}) n :=
    match n with
    | 0   => [::]
    | S n => if   hasroot p
             then (root1 p) :: (roots_rec (p %/ ('X - (root1 p)%:P)) n)
             else [::]
    end.

  Lemma roots_root:
    forall (p : {poly K}) n x, x \in (roots_rec p n) -> root p x.
  Proof.
    move=> p n; elim: n p => [|n IH] // p x /=.
    case hroot_p: (hasroot p); last by rewrite in_nil.
    have root1_rp: root p (root1 p) by rewrite root1_root.
    rewrite in_cons; case/orP; [by move/eqP=> -> | have := root1_rp].
    rewrite -dvdp_XsubCl -['X - _]expr1 -dvd_factornP expr1.
    by move/eqP=> Ep H; rewrite Ep rootM IH.
  Qed.

  Definition roots p := nosimpl (roots_rec p (size p).-1).

  Lemma roots_mu p x:
    p != 0 -> \mu_x p = count (pred1 x) (roots p).
  Proof.
    move=> nz_p; rewrite /roots.
    move: {-2}p (erefl (size p)) nz_p; elim: (size p) x => [|n IH] x q.
    + by move/eqP; rewrite size_poly_eq0 => ->.
    case: n IH => [|n] IH sz_q; rewrite sz_q /=.
    + by move/eqP: sz_q; case/size_poly1P=> c _ -> _; rewrite mu_polyC.
    move=> nz_q; case rootq: (hasroot q) => /=; last first.
    + apply/eqP; rewrite eqn0Ngt mu_gt0 //.
      by apply/negP; move/root_hasroot; rewrite rootq.
    rewrite {1}(root1_factor_theorem rootq) mu_mul; last first.
    + rewrite mulf_neq0 ?polyXsubC_eq0 //.
      by rewrite divp_factor_root_neq0 // root1_root.
    rewrite mu_factor addnC eq_sym; congr (_ + _)%N.
    have nz_qdiv: q %/ ('X - (root1 q)%:P) != 0.
    + by rewrite divp_factor_root_neq0 ?root1_root.
    have sz_qdiv: size (q %/ ('X - (root1 q)%:P)) = n.+1.
    + move: sz_q; rewrite {1}(root1_factor_theorem rootq).
      rewrite size_proper_mul; last first.
      * by rewrite mulf_neq0 ?(lead_coef_eq0, polyXsubC_eq0).
      by rewrite size_XsubC addn2 /=; case.
    by rewrite IH // sz_qdiv.
  Qed.

  Lemma rootsP p: p != 0 -> (roots p) =i (root p).
  Proof.
    move=> nz_p x; rewrite mem_root -rootE -mu_gt0 //.
    by rewrite roots_mu // lt0n count_pred1.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma roots0: roots 0 = [::] :> (seq K).
  Proof. by rewrite /roots size_poly0. Qed.

  Lemma rootsC c: roots c%:P = [::] :> (seq K).
  Proof.
    by rewrite /roots; rewrite size_polyC; case: (c == _).
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma roots_factor_theorem (p : {poly K}):
    p != 0 ->
      exists2 qq,
        (p = qq * \prod_(c <- roots p) ('X - c%:P))
      & ~~(hasroot qq).
  Proof.
    move: {-2}p (erefl (size p)); elim: (size p) => [|[|n] IH] => {p} p.
    + by move/eqP; rewrite size_poly_eq0 => ->.
    + move/eqP; case/size_poly1P => c nz_c -> _; rewrite rootsC.
      exists c%:P; first by rewrite big_nil mulr1.
      by apply/negP; move/root1_root; rewrite rootC (negbTE nz_c).
    move=> sz_p nz_p; rewrite /roots sz_p /=.
    case rootp: (hasroot p); last first.
    + by rewrite big_nil; exists p; rewrite ?rootp // mulr1.
    have nz_pdiv: p %/ ('X - (root1 p)%:P) != 0.
    + by rewrite divp_factor_root_neq0 // root1_root.
    have sz_pdiv: size (p %/ ('X - (root1 p)%:P)) = n.+1.
    + move: sz_p; rewrite {1}(root1_factor_theorem rootp).
      rewrite size_proper_mul; last first.
      * by rewrite mulf_neq0 ?(lead_coef_eq0, polyXsubC_eq0).
      by rewrite size_XsubC addn2 /=; case.
    case: (IH _ sz_pdiv nz_pdiv) => qq pdivE root_qq; exists qq => //.
    rewrite big_cons mulrCA [n]pred_Sn -sz_pdiv -pdivE.
    move/root1_root: rootp; rewrite root_factor_theorem -eqp_div_XsubC.
    by rewrite mulrC => /eqP.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma hasroot_factor (c : K): hasroot ('X - c%:P).
  Proof.
    by apply: (@root_hasroot _ c); rewrite root_XsubC.
  Qed.

  Lemma root1_factor c: root1 ('X - c%:P) = c :> K.
  Proof.
    by move/root1_root: (hasroot_factor c); rewrite root_XsubC => /eqP.
  Qed.

  Lemma roots_factor c: roots ('X - c%:P) = [:: c] :> (seq K).
  Proof.
    by rewrite /roots size_XsubC /= root1_factor hasroot_factor.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma roots_mul (p q : {poly K}):
    (p * q) != 0 -> roots (p * q) =pl (roots p) ++ (roots q).
  Proof.
    rewrite mulf_eq0; case/norP => nz_p nz_q.
    apply/perm_eqlP; rewrite /perm_eq; apply/allP => x _.
    rewrite /= count_cat -!roots_mu ?mulf_neq0 //.
    by rewrite mu_mul ?mulf_neq0.
  Qed.

  Lemma perm_eq_roots_mul (p q : {poly K}):
    (p * q) != 0 -> roots (p * q) =p (roots p) ++ (roots q).
  Proof.
    by move=> nz_pq; apply/perm_eqlP; apply: roots_mul.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma roots_mulC (c : K) (p : {poly K}):
    c != 0 -> (roots (c *: p)) =pl (roots p).
  Proof.
    have [->|nz_p] := eqVneq p 0; first by rewrite scaler0 roots0.
    move=> nz_c; apply/perm_eqlP; rewrite -mul_polyC.
    by rewrite roots_mul ?(mulf_neq0, polyC_eq0) // rootsC.
  Qed.

  Lemma perm_eq_roots_mulC (c : K) (p : {poly K}):
    c != 0 -> (roots (c *: p)) =p (roots p).
  Proof.
    by move=> nz_c; apply/perm_eqlP; apply: roots_mulC.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma roots_exp (n : nat) (p : {poly K}):
    (0 < n)%N -> roots (p ^+ n) =pl flatten (nseq n (roots p)).
  Proof.
    have [->|nz_p] := eqVneq p 0.
    + move=> n_gt0; rewrite expr0n eqn0Ngt n_gt0 /=.
      by rewrite roots0; elim: n {n_gt0} => [|n IH].
    elim: n => [|[|n] IH] // _; rewrite exprS.
    + by rewrite expr0 mulr1 /= cats0.
    apply/perm_eqlP; rewrite roots_mul ?(mulf_neq0, expf_neq0) //=.
    by rewrite perm_cat2l IH.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma perm_eq_roots_factors (cs : seq K):
    (roots (\prod_(c <- cs) ('X - c%:P))) =p cs.
  Proof.
    elim: cs => [|c cs IH]; first by rewrite big_nil rootsC.
    rewrite big_cons roots_mul ?(mulf_neq0, polyXsubC_eq0) //.
    + by rewrite roots_factor /= perm_cons.
    + by rewrite -size_poly_eq0 size_prod_XsubC.
  Qed.

  (* ------------------------------------------------------------------ *)
  Definition sqrt (c : K) := root1 ('X ^+ 2 - c%:P).

  Definition hassqrt (c : K) := hasroot ('X ^+ 2 - c%:P).

  CoInductive roots_sqr (c : K) : bool -> Set :=
  | AR_SqrNone of   (roots ('X ^+ 2 - c%:P)) =p [::]
                  : roots_sqr c false

  | AR_SqrSome of   (exists2 k, (k^+2 = c)
                  & (roots ('X ^+ 2 - c%:P) =p [:: k; -k]))
                  : roots_sqr c true.

  Lemma roots_sqrP (c : K) : roots_sqr c (hasroot ('X ^+ 2 - c%:P)).
  Proof.
    case Hsqrt: (hasroot ('X ^+ 2 - c%:P)); constructor; last first.
    + by rewrite /roots size_XnsubC //= Hsqrt.
    set k := root1 ('X ^+ 2 - c%:P); have Ec: c = k ^+ 2.
    + by apply/eqP; rewrite eq_sym -root_XnsubC; apply root1_root.
    exists k=> //; rewrite Ec polyC_exp subr_sqr -{2}[k]opprK polyC_opp.
    by rewrite roots_mul ?(mulf_neq0, polyXsubC_eq0) // !roots_factor /=.
  Qed.

  Lemma sqrtN (c k : K):
    root ('X ^+ 2 - c%:P) (-k) = root ('X ^+ 2 - c%:P) k.
  Proof. by rewrite !rootE !hornerE mulrNN. Qed.

  Lemma sqrt_sqr (c : K) : (c == sqrt (c ^+ 2)) || (c == - (sqrt (c ^+ 2))).
  Proof.
    have/root1_root: hasroot ('X^2 - (c ^+ 2)%:P).
      by apply/hasrootP; exists c; rewrite rootE !hornerE subrr.
    by rewrite -/(sqrt _) rootE !hornerE subr_eq0 eq_sym eqr_sqr.
  Qed.

  Lemma sqrt0: sqrt 0 = 0 :> K.
  Proof.
    move: (sqrt_sqr 0); rewrite expr0n /=.
    by rewrite ![0 == _]eq_sym oppr_eq0 orbb => /eqP.
  Qed.
End PolyDec.

Module PolyClosed.
Section PolyClosed.
  Variable K : decFieldType.

  Hypothesis closed : GRing.ClosedField.axiom K.

  Import PreClosedField.

  Lemma hasroot_size_neq1 (p : {poly K}): hasroot p = (size p != 1%N).
  Proof. by apply/hasrootP/(closed_rootP closed). Qed.

  Lemma roots_factor_theorem_f (p : {poly K}):
    p = (lead_coef p) *: \prod_(c <- roots p) ('X - c%:P).
  Proof.
    have [->|nz_p] := eqVneq p 0.
    * by rewrite lead_coef0 scale0r.
    case: (roots_factor_theorem nz_p) => qq Ep root_qq.
    rewrite {1 2}Ep lead_coef_Mmonic ?monic_prod_XsubC //.
    move: root_qq; rewrite hasroot_size_neq1 negbK.
    by case/size_poly1P=> c nz_c ->; rewrite lead_coefC mul_polyC.
  Qed.

  Lemma roots_factor_theorem_mu_f (p : {poly K}):
    p = (lead_coef p) *: \prod_(c <- undup (roots p)) ('X - c%:P) ^+ (\mu_c p).
  Proof.
    have h (r1 r2 : {poly K}): r1 * r2 != 0 ->
      reflect (forall x, \mu_x r1 = \mu_x r2) (r1 %= r2).
      rewrite mulf_eq0; case/norP => nz_r1 nz_r2; apply: (iffP idP).
      + by case/eqpf_eq => c nz_c -> x; rewrite mu_mulC.
      + move=> h; rewrite [r1]roots_factor_theorem_f [r2]roots_factor_theorem_f.
        have: perm_eq (roots r1) (roots r2).
          by apply/allP => x _; rewrite /= -!roots_mu // h.
        move=> eq; rewrite (eq_big_perm _ eq) /=.
        apply (@eqp_trans _ (\prod_(i <- roots r2) ('X - i%:P))).
        * by apply/eqp_scale; rewrite lead_coef_eq0.
        * by rewrite eqp_sym; apply/eqp_scale; rewrite lead_coef_eq0.
    have [->|nz_p] := eqVneq p 0; first by rewrite lead_coef0 scale0r.
    set q : {poly K} := (_ *: _); have: p %= q.
      apply/h.
        rewrite mulf_neq0 // {}/q scaler_eq0 lead_coef_eq0 (negbTE nz_p) /=.
        rewrite prodf_seq_neq0; apply/allP=> x _; apply/implyP=> _.
        by rewrite expf_neq0 // polyXsubC_eq0.
      move=> x; rewrite {}/q mu_mulC ?lead_coef_eq0 // mu_prod; last first.
        rewrite prodf_seq_neq0; apply/allP=> c _; apply/implyP=> _.
        by rewrite expf_neq0 // polyXsubC_eq0.
      have [root_px|] := (boolP (x \in (roots p))); last first.
        rewrite rootsP // => Nroot_px; rewrite muNroot //.
        rewrite big_seq big1 // => c; rewrite mem_undup rootsP // => root_pc.
        rewrite mu_exp mu_factor; case: eqP; last by rewrite mul0n.
        by move=> eq_xc; rewrite eq_xc root_pc in Nroot_px.
      rewrite (bigD1_seq x) ?(mem_undup, undup_uniq) //=.
      rewrite mu_exp mu_XsubC mul1n big1 ?addn0 //.
      move=> c ne_cx; rewrite mu_exp mu_factor eq_sym.
      by rewrite (negbTE ne_cx) mul0n.
    move/eqp_eq; rewrite {1}/q lead_coefZ lead_coef_prod.
    rewrite big1 ?mulr1; last first.
      by move=> c _; rewrite lead_coef_exp lead_coefXsubC expr1n.
    by move/scalerI => ->//; rewrite lead_coef_eq0.
  Qed.

  Lemma roots_size (p : {poly K}): size (roots p) = (size p).-1.
  Proof.
    have [->|nz_p] := eqVneq p 0.
    + by rewrite roots0 size_poly0.
    have nz_lcp: lead_coef p != 0 by rewrite lead_coef_eq0.
    have Ep := (roots_factor_theorem_f p); rewrite {2}Ep.
    by rewrite size_scale // size_prod_XsubC.
  Qed.
End PolyClosed.
End PolyClosed.

Section PolyClosedField.
  Variable K : closedFieldType.

  Import PolyClosed.

  Local Hint Extern 0 (GRing.ClosedField.axiom _) => exact: solve_monicpoly.

  Lemma hasroot_size_neq1 (p : {poly K}): hasroot p = (size p != 1%N).
  Proof. by apply: hasroot_size_neq1. Qed.

  Lemma roots_factor_theorem_f (p : {poly K}):
    p = (lead_coef p) *: \prod_(c <- roots p) ('X - c%:P).
  Proof. by apply: roots_factor_theorem_f. Qed.

  Lemma roots_size (p : {poly K}): size (roots p) = (size p).-1.
  Proof. by apply: roots_size. Qed.

  Lemma sqr_sqrt (c : K): (sqrt c) ^+ 2 = c.
  Proof.
    have: hasroot ('X^2 - c%:P).
      by rewrite hasroot_size_neq1 size_XnsubC.
    move/root1_root; rewrite rootE !hornerE -/(sqrt _).
    by rewrite subr_eq0=> /eqP.
  Qed.

  Lemma expfS_eq0 (c : K) n: (c ^+ n.+1 == 0) = (c == 0).
  Proof. by rewrite expf_eq0. Qed.

  Lemma sqrt_eq0 (c : K): (sqrt c == 0) = (c == 0).
  Proof.
    by rewrite -[X in X = _](@expfS_eq0 _ 1) sqr_sqrt.
  Qed.

  Lemma cf_copsqr (p q1 q2 : {poly K}):
    p != 0 -> coprimep q1 q2 -> p^+2 = q1 * q2 ->
      exists r, q1 = r ^+ 2.
  Proof.
    move=> nz_p cop eq; case: (copsqr nz_p cop eq).
    move=> r /eqpP [[c1 c2] /= /andP [nz_c1 nz_c2]] {eq} eq.
    exists ((sqrt (c2 / c1)) *: r).
    rewrite exprZn sqr_sqrt; apply: (mulfI (x := c1%:P)).
      by rewrite polyC_eq0.
    by rewrite !mul_polyC scalerA mulrCA divff // mulr1.
  Qed.
End PolyClosedField.
