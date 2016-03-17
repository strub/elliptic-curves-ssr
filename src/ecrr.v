(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq.
From mathcomp Require Import fintype choice fingroup tuple perm zmodp.
From mathcomp Require Import ssrfun bigop ssralg ssrint ssrnum.
From mathcomp Require Import generic_quotient.

Require Import xseq xmatrix polyall polydec polyfrac.
Require Import fraction fracfield SsrMultinomials.freeg.
Require Import ec ecpoly eceval ecorder ecdiv ecpolyfrac.

(* -------------------------------------------------------------------- *)
Import GRing.Theory.
Import Num.Theory.
Import fraction.FracField.
Import fracfield.FracField.
Import FracInterp.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Local Notation "n %:I" := (inord n) (at level 2, format "n %:I").

Local Notation "A ^+m n" := (map_mx ((@GRing.exp _)^~ n) A) (at level 2).
Local Notation "A %:MP"  := (map_mx polyC A) (at level 2, format "A %:MP").

(* -------------------------------------------------------------------- *)
Section BigOpToNat.
  Import Monoid.

  Lemma big_ord_to_nat
    (R : Type) (idx : R) (op : Monoid.law idx) (n : nat) (F : 'I_n.+1 -> R):
      \big[op/idx]_(i < n.+1) F i = \big[op/idx]_(0 <= i < n.+1) F i%:I.
  Proof.
    elim: n F => [|n IH] F.
      rewrite big_ord1 big_nat_recr //big_geq // mul1m.
      by congr (F _); apply/eqP; rewrite eqE /= inordK.
    rewrite big_nat_recr // big_ord_recr IH; congr (op _ _); last first.
      by congr (F _); apply/eqP; rewrite eqE /= inordK.
      rewrite !big_nat; apply: eq_bigr=> i /andP [_ le_i]; congr (F _).
    by apply/eqP; rewrite eqE /= !inordK // (ltn_trans le_i).
  Qed.
End BigOpToNat.

(* -------------------------------------------------------------------- *)
Section ECRR_2_39.
  Variable K : closedFieldType.

  Hypothesis chiN2: 2 \notin [char K].

  Local Notation simpm := Monoid.simpm.
  Local Notation sizep := (size : {poly _} -> _).

  Local Notation "x ~ i" := (x i%:I 0) (at level 8, format "x ~ i").

  Lemma L_2_39 (A : 'M[K]_(4, 2)) (b : 'cV[{poly K}]_2) (c : 'cV[{poly K}]_4):
    let: p := b~0 in
    let: q := b~1 in
         (forall (i j : 'I_4), i != j -> row_free (rows [tuple i; j] A))
      -> A%:MP *m b = c ^+m 2
      -> coprimep p q
      -> (size p <= 1)%N && (size q <= 1)%N.
  Proof.
    have:
      let: p := b~0 in
      let: q := b~1 in
           (forall (i j : 'I_4), i != j -> row_free (rows [tuple i; j] A))
        -> (exists c, A%:MP *m b = c ^+m 2)
        -> coprimep p q
        -> (size p <= 1)%N && (size q <= 1)%N;
      last by move=> H A2rfree eq_Ab_c2 cop_pq; apply: H=> //; by exists c.

    move: {-2}(b~0) (erefl (b~0)) => p Ep.
    move: {-2}(b~1) (erefl (b~1)) => q Eq.
    case: (leqP (maxn (size p) (size q)) 1).
      move=> sz_pq_1 _ _ _; apply/andP; split.
      + by apply: (leq_trans (leq_maxl (size p) (size q))).
      + by apply: (leq_trans (leq_maxr (size p) (size q))).
    move=> sz_pq; rewrite [X in X && _]leqNgt [X in _ && X]leqNgt.
    rewrite -negb_or -leq_max sz_pq /=.
    move: {2}(maxn _ _) (leqnn (maxn (size p) (size q))) sz_pq => sz.

    elim: sz A b p Ep q Eq=> [|sz IH] A b _ -> _ ->.
      by rewrite leqn0 => /eqP ->.

    move=> {c}; wlog: A b / (size (b~0) <= size (b~1))%N.
      set p := (b~0); set q := (b~1).
      move=> wlog sz_pq Ncpq A2rfree eq_Ab_c2 cop_pq.
      case: (leqP (size p) (size q)).
        by move=> leq_sz_pq; apply: (wlog A b).
      pose A' := col_perm (tperm 0%:I 1%:I) A.
      pose b' := row_perm (tperm 0%:I 1%:I) b.
      move/ltnW=> leq_sz_qp; move: (wlog A' b').
      rewrite !mxE ?(tpermL, tpermR); apply=> //; last 2 first.
      + case: eq_Ab_c2 => [c eq_Ab_c2]; exists c.
        by rewrite map_col_perm mul_col_perm -row_permM mulVg row_perm1.
      + by rewrite coprimep_sym.
      + by rewrite maxnC.
      + by rewrite maxnC.
      move=> i j ne_ij; rewrite /A' col_permE rows_mul.
      rewrite /row_free mxrankMfree; first by apply: A2rfree.
      by rewrite row_free_unit unitmx_perm.

    set p := (b~0); set q := (b~1) => le_sz_pq sz_pq Nc_pq.
    move=> A2rfree [c eq_Ab_c2] cop_pq.

    pose a (i1 i2 j : 'I_4) :=
      let M := A *m (rows [tuple i1; i2] A)^-1 in
        (sqrt (M j 0%:I), sqrt (- (M j 1%:I))).

    have fact1 (i j : 'I_4): i != j -> coprimep (c i 0) (c j 0).
      move=> ne_ij; set u := (c i 0); set v := (c j 0).
      apply/Pdiv.ClosedField.coprimepP=> x root_x_ci.
      rewrite -rootE; apply/negP=> root_x_cj.
      have root_x_c: forall k, root (c (tnth [tuple i; j] k) 0) x.
        move=> k; move: (mem_ord k); rewrite mem_seq2.
        by case/orP=> /eqP ->; rewrite (tnth_nth 0) inordK.
      move/(congr1 (rows [tuple i; j])): eq_Ab_c2.
      rewrite rows_mul; set M := (rows _ _).
      move/(congr1 (mulmx M^-1)); rewrite mulmxA mulVmx; last first.
        by rewrite /M -map_rows map_unitmx -row_free_unit A2rfree.
      rewrite mul1mx; move=> eq_b; have: forall k, root (b k 0) x.
        move=> k; move/matrixP/(_ k 0)/(congr1 (horner^~ x)): eq_b.
        rewrite !mxE big_ord_to_nat unlock /= !mxE !hornerE /=.
        by rewrite !(rootP (root_x_c _)) !simpm rootE => /eqP.
      move=> root_b_x; move/Pdiv.ClosedField.coprimepP: cop_pq.
      by move=> /(_ x (root_b_x 0%:I)); rewrite -rootE root_b_x.

    have fact2 (i j : 'I_4):
      (size (c i 0%R) <= 1 -> size (c j 0%R) <= 1 -> i = j)%N.
      move=> /size1_polyC ciE /size1_polyC cjE.
      apply/eqP; have [//|/eqP ne_ij] := (i =P j).
      move/(congr1 (rows [tuple i; j])): eq_Ab_c2.
      rewrite rows_mul -!map_rows; set M := rows _ _.
      move/(congr1 (mulmx (M^-1)%:MP)); rewrite mulmxA.
      rewrite -map_mxM /= mulVmx ?(map_mx1, mul1mx); last first.
        by rewrite -row_free_unit A2rfree.
      move/matrixP/(_~1); rewrite !mxE big_ord_to_nat /=.
      rewrite unlock /= addr0 !mxE !(tnth_nth 0) !inordK //=.
      rewrite ciE cjE -!(rmorphX, rmorphM, rmorphD).
      move: (_ + _) => z /= qE; have := Nc_pq.
      rewrite maxnC /maxn [(size _ < _)%N]ltnNge le_sz_pq /=.
      by rewrite /q qE size_polyC; case: (_ == _).

    have fact3 (i j : 'I_4): i != j -> ~~(c i 0 %= c j 0).
      move=> ne_ij; apply/negP=> eqp_ij.
      case root_ci: (hasroot (c i 0)).
        move/root1_root: root_ci=> root_ci.
        move/Pdiv.ClosedField.coprimepP: (fact1 _ _ ne_ij) => /(_ _ root_ci).
        by rewrite -rootE -(eqp_root eqp_ij) root_ci.
      move/negbT: root_ci; rewrite hasroot_size_neq1 negbK.
      move/eqp_size: eqp_ij=> size_ij size_ci.
      have := size_ci; rewrite eqn_leq andbC=> /andP [_ /fact2].
      move/(_ j); rewrite -size_ij (eqP size_ci) => /(_ (erefl true)).
      by move=> eq_ij; rewrite eq_ij eqxx in ne_ij.

    have fact4 (i : 'I_4): c i 0 != 0.
      have: exists j : 'I_4, (i != j).
        case: i=> i lt_i4; rewrite eqE /=.
        by case: i lt_i4=> [|i]; [exists 1|exists 0].
      case=> j ne_ij; apply/negP=> /eqP z_ci.
      have sz_cj: (size (c j 0%R) > 1)%N.
        rewrite ltnNge; apply/negP=> /fact2 -/(_ i).
        rewrite z_ci size_poly0 => /(_ (erefl true)).
        by move=> eq_ji; rewrite eq_ji eqxx in ne_ij.
      have/root1_root root_cj: hasroot (c j 0).
        by rewrite hasroot_size_neq1 eqn_leq leqNgt sz_cj.
      move/Pdiv.ClosedField.coprimepP: (fact1 _ _ ne_ij) => /(_ (root1 (c j 0))).
      rewrite rootE z_ci horner0 eqxx => /(_ (erefl true)).
      by rewrite -rootE root_cj /=.

    have fact5 (i1 i2 j : 'I_4) (a1 a2 : K):
         uniq [:: i1; i2; j]
      -> (c j 0) ^+ 2 = a1 *: (c i1 0) ^+ 2 + a2 *: (c i2 0) ^+ 2
      -> a1 * a2 != 0.
      move=> uq_ids eq; rewrite mulf_eq0; apply/negP=> z_a.
      wlog: i1 i2 a1 a2 z_a uq_ids eq / a1 == 0.
        move=>wlog; have/orP := z_a; case.
          by move/wlog=> /(_ i1 i2 a2 z_a uq_ids).
        move/wlog=> /(_ i2 i1 a1); rewrite addrC; apply=> //.
          by rewrite orbC.
        set s := [:: _; _; _]; have: perm_eq [:: i1; i2; j] s.
          by apply/perm_eqP=> /= P; ring.
        by move/perm_eq_uniq=> <-.
      move/eqP=> z_a1; move: eq; rewrite z_a1 scale0r add0r.
      have [->|/eqP nz_a2 eq] := (a2 =P 0).
        by move/eqP; rewrite scale0r expf_eq0 /= (negbTE (fact4 j)).
      move/eqP: eq; rewrite -[a2]sqr_sqrt -mul_polyC polyC_exp -exprMn.
      rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0.
      rewrite mul_polyC -scaleNr => eq.
      have: exists b:bool, c j 0 = ((-1) ^+ b * (sqrt a2)) *: (c i2 0).
        case/orP: eq=> eq; [exists false|exists true].
        + by rewrite expr0 mul1r; apply/eqP.
        + by rewrite expr1 mulN1r; apply/eqP.
      case=> s cjE; have: c j 0 %= c i2 0.
        apply/eqpP; exists (1, (-1) ^+ s * (sqrt a2))=> /=.
          rewrite oner_eq0 /= mulf_eq0 expf_eq0 oppr_eq0 oner_eq0.
          by rewrite andbF /= sqrt_eq0.
        by rewrite scale1r.
      move=> eqp_ji2; have/fact3: (j != i2).
        by rewrite (@nth_uniq _ 0 _ 2 1 _ _ uq_ids).
      by rewrite eqp_ji2.

    have fact6 (i1 i2 j : 'I_4):
      uniq [:: i1; i2; j] ->
        (c j 0)^+2 =   ((a i1 i2 j).1 *: (c i1 0))^+2
                     - ((a i1 i2 j).2 *: (c i2 0))^+2.
      pose ids := [:: i1; i2; j] => uq_idx.
      pose M := rows [tuple i1; i2] A.
      have/(congr1 (rows [tuple i1; i2])) := eq_Ab_c2.
      rewrite rows_mul -!map_rows -/M => /(congr1 (mulmx (M^-1)%:MP)).
      rewrite mulmxA -map_mxM /= mulVmx; last first.
        by rewrite -row_free_unit A2rfree // (@nth_uniq _ 0 ids 0 1).
      rewrite map_mx1 mul1mx => eq_b; move/matrixP/(_ j 0): eq_Ab_c2.
      rewrite eq_b mulmxA; rewrite -map_mxM /=; set N := (A *m _).
      move: N=> N; rewrite !mxE big_ord_to_nat unlock /= addr0.
      rewrite !mxE !(tnth_nth 0) !inordK //= => <-.
      by rewrite !exprZn !mul_polyC !sqr_sqrt scaleNr opprK.

    have fact7 (i1 i2 j : 'I_4): uniq [:: i1; i2; j] ->
        (a i1 i2 j).1 * (a i1 i2 j).2 != 0.
      move=> uq; have/fact6 := uq; case: (a i1 i2 j)=> a1 a2 /=.
      rewrite !exprZn -scaleNr => /fact5 -/(_ uq).
      by rewrite mulf_eq0 oppr_eq0 !expf_eq0 /= mulf_eq0.

    have fact8 (i1 i2 j : 'I_4): uniq [:: i1; i2; j] ->
      let (a1, a2) := a i1 i2 j in
        coprimep
          (a1 *: (c i1 0) + a2 *: (c i2 0))
          (a1 *: (c i1 0) - a2 *: (c i2 0)).

      move=> uq; case aE: (a _ _ _)=> [a1 a2] /=.
      move: (fact7 _ _ _ uq); rewrite aE /= mulf_eq0=> /norP [nz_a1 nz_a2].
      apply/Pdiv.ClosedField.coprimepP=> x; rewrite rootE !hornerE => root_x_s1.
      case root_x_ci2: (root (c i2 0) x).
        have := root_x_ci2; rewrite rootE => /eqP ->; rewrite mulr0 subr0.
        rewrite mulf_eq0 (negbTE nz_a1) /=.
        apply/(Pdiv.ClosedField.coprimepP (c i2 0))=> //.
        by apply: fact1; rewrite (@nth_uniq _ 0 _ 1 0 _ _ uq).
      rewrite -(eqP root_x_s1); apply/negP=> /eqP /addrI.
      move/esym/eqP; rewrite -addr_eq0 -mulr2n -mulr_natl.
      have := chiN2; rewrite !mulf_eq0 inE /= => /negbTE -> /=.
      by rewrite (negbTE nz_a2) /= -rootE root_x_ci2.

    pose u := c~0; pose v := c~1.

    pose A' :=
      \matrix_(i < 4, j < 2)
        let: (a1, a2) := a 0%:I 1%:I (2 + i./2)%:I in
          [:: a1; (-1)^+(odd i) * a2]`_j.
    pose b' := [col u; v].

    have uniqD_r (k : 'I_2):
      uniq ([:: 0%:I; 1%:I; (2 + k)%:I] : seq 'I_4).
      by case: k => k lt_k2; rewrite -(map_inj_uniq val_inj) /= !inordK.

    apply: (IH A' b' u _ v _); last 2 first.
    + have H (k : 'I_2) (sg : bool):
        let: a := a 0%:I 1%:I (2 + k)%:I in
          exists r : {poly K}, a.1 *: u + ((-1)^+sg * a.2) *: v == r ^+ 2.
        case aE: (a _ _ _) => [a1 a2]; move: (fact6  _ _ _ (uniqD_r k)).
        rewrite aE /= subr_sqr mulrC => eq_c2; case: (cf_copsqr _ _ eq_c2).
        + by rewrite fact4.
        + by move: (fact8 _ _ _ (uniqD_r k)); rewrite aE.
        have := eq_c2; rewrite mulrC; case/(cf_copsqr _ _).
        + by rewrite fact4.
        + by move: (fact8 _ _ _ (uniqD_r k)); rewrite coprimep_sym aE.
        move=> r2 /esym r2E r1 /esym r1E; case: sg.
        + by exists r2; rewrite expr1 mulN1r scaleNr r2E.
        + by exists r1; rewrite expr0 mul1r r1E.
        pose c' := \col_(i < 4) xchoose (H (i./2)%:I (odd i)); exists c'.
        apply/matrixP=> i j; rewrite !mxE big_ord_to_nat unlock /= addr0.
        rewrite ![b' _ _]mxE ord1 !(tnth_nth [tuple 0]) 2?inordK /tnth //=.
        rewrite ![A'%:MP _ _]mxE ![A' _ _]mxE; case aE: (a _ _ _) => [a1 a2].
        rewrite ![_ _%:I]inordK //=; move: (xchooseP (H (i./2)%:I (odd i))).
        move/eqP=> <-; rewrite !inordK ?aE //=; last first.
          by rewrite ltnS (half_leq (n := 3)) // -ltnS.
        by rewrite !mul_polyC.
    + by apply: fact1; rewrite eqE /= !inordK.
    + by rewrite !mxE !(tnth_nth [tuple 0]) !inordK.
    + by rewrite !mxE !(tnth_nth [tuple 0]) !inordK.
    + have szc i: (size (c i 0%R) < (maxn (size p) (size q)))%N.
        rewrite maxnC /maxn [(size q < _)%N]ltnNge le_sz_pq /=.
        rewrite -ltn_double -[X in (X < _)%N]prednK; last first.
          by rewrite double_gt0 lt0n size_poly_eq0 fact4.
        rewrite -addnn -size_mul ?fact4 // -expr2.
        move/matrixP/(_ i 0)/(congr1 sizep)/esym: eq_Ab_c2.
        rewrite mxE=> ->; rewrite !mxE big_ord_to_nat unlock /=.
        rewrite addr0 -/p -/q; case sz_q: (size q) => [|szq].
          move: le_sz_pq Nc_pq; rewrite sz_q leqn0 => /eqP ->.
          by rewrite maxnn.
        rewrite doubleS /= !ltnS; apply: (leq_trans (size_add _ _)).
        apply: (@leq_trans (maxn (size p) (size q))).
          rewrite geq_max !leq_max ![_%:MP _ _]mxE !mul_polyC.
          by rewrite !size_scale_leq !simpm.
        rewrite maxnC /maxn [(size q < _)%N]ltnNge le_sz_pq /= sz_q.
        rewrite -addnn -{1}[szq]add0n ltn_add2r lt0n.
        apply/negP=> /eqP z_szq; move: le_sz_pq Nc_pq.
        by rewrite sz_q z_szq maxnC /maxn [(1 < size p)%N]ltnNge => ->.
      by rewrite geq_max -![(_ <= sz)%N]ltnS !(leq_trans (szc _)).
    + rewrite ltnNge geq_max; apply/negP=> /andP [Cu Cv].
      by move/eqP: (fact2 _ _ Cu Cv); rewrite eqE /= !inordK.
    + move=> i j ne_ij; rewrite row_free_unit unitmxE unitfE.
      rewrite det2 !mxE; set cf := a _ _; rewrite [cf]lock.
      rewrite !(tnth_nth 0) !inordK //= -lock /cf => {cf}.
      case: (i./2 =P j./2)=> [eq_div2_ij|/eqP ne_div2_ij].
      * rewrite -eq_div2_ij; case aE: (a _ _ _) => [a1 a2].
        have ->: (-1) ^+ (odd j) = -(-1) ^+ (odd i) :> K.
          case: (odd i =P odd j) => [eq_odd_ij|/eqP ne_odd_ij].
            move: (odd_double_half (val j)); rewrite -eq_odd_ij -eq_div2_ij.
            by move/eqP; rewrite odd_double_half (inj_eq val_inj) (negbTE ne_ij).
          move: ne_odd_ij; rewrite negb_add => /eqP <-.
          by rewrite signrN.
        rewrite mulrCA -mulrA [a2 * a1]mulrC -mulrBl !mulf_eq0.
        move: (fact7 _ _ _ (uniqD_r (i./2)%:I)).
          rewrite inordK; last first.
            by rewrite ltnS (half_leq (n := 3)) // -ltnS.
          rewrite aE /= mulf_eq0 => /norP [/negbTE-> /negbTE->].
          rewrite !simpm -opprB oppr_eq0 opprK -mulr2n -mulr_natl.
          have := chiN2; rewrite mulf_eq0 inE /= => /negbTE -> /=.
          by rewrite expf_eq0 oppr_eq0 oner_eq0 andbF.
      * case aE: (a _ _ _) => [a1 a2]; case a'E: (a _ _ _) => [a'1 a'2].
        rewrite subr_eq0; apply/negP=> /eqP /(congr1 (fun x => x^+2)).
        rewrite !exprMn !sqrr_sign !mul1r => eqa.
        have id2_ord2: (i./2 < 2)%N by rewrite ltnS (half_leq (n := 3)) // -ltnS.
        have jd2_ord2: (j./2 < 2)%N by rewrite ltnS (half_leq (n := 3)) // -ltnS.
        have := fact7 _ _ _ (uniqD_r (Ordinal id2_ord2)).
        have := fact7 _ _ _ (uniqD_r (Ordinal jd2_ord2)).
        rewrite aE a'E /= !mulf_eq0=> /norP [_ nz_a2] /norP [_ nz_a'2].
        have: (c (2 + i./2)%:I 0) ^+ 2 %= (c (2 + j./2)%:I 0) ^+ 2.
          apply/eqpP; exists (a'2 ^+ 2, a2 ^+ 2).
            by rewrite !expf_eq0 /= nz_a2 nz_a'2.
          move: (fact6 _ _ _ (uniqD_r (Ordinal id2_ord2))).
          move: (fact6 _ _ _ (uniqD_r (Ordinal jd2_ord2))).
          rewrite aE a'E /= => -> ->; rewrite !exprZn.
          by rewrite !scalerBr !scalerA ![a'2 ^+ 2 * _]mulrC eqa.
        move=> cij_prop; have: c (2 + i./2)%:I 0 %= c (2 + j./2)%:I 0.
          case/eqpP: cij_prop=> [[z1 z2] /= nz_z].
          rewrite -[z1]sqr_sqrt -[z2]sqr_sqrt -!exprZn.
          case/sqr_eqr_sign=> s; rewrite -polyC_opp -polyC_exp.
          rewrite mul_polyC scalerA => eqc; apply/eqpP.
          exists (sqrt z1, (-1) ^+ s * (sqrt z2))=> //=.
          by rewrite mulf_eq0 expf_eq0 oppr_eq0 oner_eq0 !sqrt_eq0 andbF.
        by apply/negP; rewrite fact3 // eqE /= !inordK ?(leq_add2l 2).
  Qed.
End ECRR_2_39.

(* -------------------------------------------------------------------- *)
Module DetFree.
Section ModuleSec.
  Variable K : fieldType.
  Variable p : nat.

  Variable cs : p.-tuple K.
  Variable c  : K.

  Hypothesis uniq_cs: uniq cs.
  Hypothesis nz_c : c != 0.

  Local Notation "n %:I" := (inord n) (at level 2, format "n %:I").

  Definition A :=
    let t := [tuple [tuple 1; tnth cs i] | i < p] in
      mxdefE [tuple of rcons t [tuple 0; c]].

  Lemma detfree:
    forall (i j : 'I_p.+1), i != j -> row_free (rows [tuple i; j] A).
  Proof.
    pose B :=
      \matrix_(i < p.+1, j < 2)
        (if (i < p)%N then [:: 1; cs`_i] else [:: 0; c])`_j.
    have eq_AB: A = B.
      apply/matrixP; case=> i lt_iSp j; rewrite !mxE.
      rewrite !(tnth_nth [tuple 0; 0]) !(tnth_nth 0) /=.
      rewrite nth_rcons size_map size_enum_ord.
      move: lt_iSp; rewrite ltnS leq_eqVlt; case/orP.
        by move/eqP=> ->; rewrite ltnn eqxx.
      move=> lt_ip; rewrite lt_ip (nth_map (Ordinal lt_ip)); last first.
        by rewrite size_enum_ord.
      by rewrite (tnth_nth 0) nth_enum_ord.
    move=> i j; wlog: i j / (i < j)%N.
      move=> wlog; case cmp_ij: (i < j)%N; first by apply: wlog.
      move=> ne_ij; have: (j < i)%N; last move=> lt_ji.
        by rewrite ltn_neqAle eq_sym ne_ij leqNgt cmp_ij.
      have: (row_free (rows [tuple j; i] A)).
        by apply: wlog; rewrite ?[j == i]eq_sym.
      set s : 'S_2 := tperm 0%:I 1%:I; rewrite /row_free.
      rewrite -(mxrank_row_perm s) row_perm_rows.
      move/eqP=> rkpermA; rewrite -[X in _ == X]rkpermA => {rkpermA}.
      apply/eqP; congr (\rank (rows _ A)); apply: eq_from_tnth.
      move=> k; have: ((k == 0%:I) || (k == 1%:I)).
        by case: k=> [[|[|k //]] /= lt_k2]; rewrite eqE /= !inordK.
      case/orP=> /eqP -> {k}; rewrite tnth_mktuple !(tnth_nth 0);
        by rewrite /s ?(tpermL, tpermR) !inordK.
    move=> lt_ij ne_ij; rewrite row_free_unit unitmxE unitfE det2 !rowsE.
    rewrite !(tnth_nth 0) !inordK //= eq_AB !mxE !inordK //.
    have lt_ip: (i < p)%N.
      by rewrite (leq_trans lt_ij) // -ltnS.
    case: (ltnP j p) => [lt_jp|].
      rewrite lt_ip /= mul1r mulr1 subr_eq0.
      by rewrite eq_sym nth_uniq ?size_tuple.
    by move=> _; rewrite lt_ip /= mulr0 mul1r subr0.
  Qed.
End ModuleSec.
End DetFree.

Lemma MA_E (K : fieldType) (a b c k : K):
  let A := [matrix [:: 1; a]; [:: 1; b]; [:: 1; c]; [:: 0; k]] in
  let p := [tuple a; b; c] in
    DetFree.A p k = A.
Proof.
  move=> A p; apply/matrixP=> k1 k2.
  rewrite /DetFree.A /A /mxdefE !mxE ; congr (tnth (tnth _ _) _) => {k1 k2}.
  apply/eqP; rewrite eqE /=; pose f (i : nat) := [tuple 1; p`_i].
  rewrite (iffLR (eq_in_map _ (f \o val) _)); last first.
    by move=> m _ /=; rewrite (tnth_nth 0).
  by rewrite /f map_comp val_enum_ord.
Qed.

Lemma row_freeA:
  forall (K : fieldType) (a b c k : K), uniq [:: a; b; c] -> k != 0 ->
    let A := [matrix [:: 1; a]; [:: 1; b]; [:: 1; c]; [:: 0; k]] in
      forall (i j : 'I_4), i != j -> row_free (rows [tuple i; j] A).
Proof.
  move=> K a b c k uq nz_k A i j ne_ij; set p := [tuple a; b; c].
  have uq_p: uniq p by apply: uq. move: (DetFree.detfree uq_p nz_k ne_ij).
  by have ->: DetFree.A p k = A by apply MA_E.
Qed.

(* -------------------------------------------------------------------- *)
Section ECRR_2_38.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ECPoly E (0, p)).

  Local Notation "n %:I" := (inord n) (at level 2, format "n %:I").

  Implicit Types f : ecpoly.

  Hypothesis closedK : GRing.ClosedField.axiom K.

  Local Notation clK := (ClosedFieldType K closedK).

  Import PreClosedField.

  Local Notation PEF := (@tofrac _ \o ((ecX E) \o polyC)).
  Local Notation "x %:PEF" := (PEF x) (at level 2).

  Local Notation "x %:F"  := (tofrac x).
  Local Notation "x // y" := (x%:F / y%:F) (at level 50, no associativity).

  Local Notation sizep := (size : {poly _} -> _).

  Local Notation "p ^:F" := (map_poly (@tofrac _ \o polyC) p)
    (at level 2, format "p ^:F") : ring_scope.

  Import fraction.

  Lemma L_2_38 (p q u v: {poly K}):
    (size p > 1)%N || (size q > 1)%N ->
    (size u > 1)%N || (size v > 1)%N ->
    coprimep p q -> coprimep u v ->
    q \is monic -> v \is monic ->
      u^+2 * q^+3 != v^+2 * (p^+3 + (E #a)*:p * q^+2 + (E #b)*: q^+3).
  Proof.
    move=> sz_p sz_u cop_pq cop_uv q_monic v_monic.
    set J := (_ + _); apply/negP=> /eqP eq; have: v^+2 %= q^+3.
      rewrite /eqp -(Gauss_dvdpr _ (q := u ^+ 2)); last first.
        by rewrite !(coprimep_expr, coprimep_expl) 1?coprimep_sym.
      rewrite eq dvdp_mulIl /= -(Gauss_dvdpl _ (q := J)).
        by rewrite -eq dvdp_mulIr.
      rewrite coprimep_expl // /J; apply/(@Pdiv.ClosedField.coprimepP clK)=> x.
        rewrite rootE !(horner_exp, hornerE) => /eqP root_q_x /=.
        rewrite root_q_x !simpm expf_eq0 /=; apply/negP=> root_p_x.
        move/(@Pdiv.ClosedField.coprimepP clK)/(_ _ root_p_x): cop_pq.
        by rewrite root_q_x eqxx.
    move=> v2E; have/eqpfP := v2E; rewrite !lead_coef_exp (eqP q_monic) (eqP v_monic).
    rewrite !expr1n !scale1r => /esym q3E.
    have h: forall x, \mu_x (q^+3) = \mu_x (v^+2).
      by move=> x; move/(congr1 (fun r => \mu_x r)): q3E.
    have {h} h: forall x, ~~ (odd (\mu_x q)).
      move=> x; apply/negP => odd_muqx; have: odd (3 * \mu_x q)%N.
        by rewrite odd_mul odd_muqx.
      by rewrite -mulnC -mu_exp h mu_exp muln2 odd_double.
    have: q = (\prod_(c <- undup (roots q)) ('X - c%:P)^+(\mu_c q)./2)^+2.
      rewrite {1}[q]PolyClosed.roots_factor_theorem_mu_f //.
      rewrite (eqP q_monic) scale1r expr2 -big_split /=.
      apply: eq_bigr => c _; rewrite -exprD addnn.
      move: (odd_double_half (\mu_c q)); rewrite (negbTE (h _)) add0n.
      by move=> {1}<-.
    move: (\prod_(_ <- _) _) => qsrt qE.
    case/eqpf_eq: v2E=> c nz_c v2E; move: eq; rewrite v2E => /eqP {v2E}.
    rewrite -mul_polyC [X in _ == X]mulrAC (inj_eq (mulIf _)); last first.
      by rewrite expf_eq0 /= monic_neq0.
    rewrite /J; wlog: u c nz_c sz_u cop_uv / (c == 1).
      move=> wlog /eqP /(congr1 ( *%R (c^-1)%:P)).
      rewrite [X in _ = X]mulrA -polyC_mul mulVf //.
      rewrite -[c^-1](@sqr_sqrt clK) polyC_exp -exprMn.
      move/eqP/wlog; apply; rewrite ?oner_eq0 // mul_polyC.
        by rewrite size_scale // (@sqrt_eq0 clK) invr_eq0.
      by rewrite coprimep_scalel // (@sqrt_eq0 clK) invr_eq0.
      move/eqP=> ->; rewrite mul1r -/J.
      move: (Xpoly_factor E closedK); case=> cs uq_cs.
    pose csn i := tnth cs i; rewrite (big_nth 0) size_tuple => eq_Xpoly {c nz_c}.
    have (i j : 'I_3): i != j -> coprimep (p - (csn i) *: q) (p - (csn j) *: q).
      move=> ne_ij; apply/(@Pdiv.ClosedField.coprimepP clK)=> k; move=> root_i.
      apply/negP; rewrite -rootE => root_j.
      have := root_j; have := root_i; rewrite !rootE !hornerE.
      rewrite subr_eq0 => /eqP ->; rewrite -mulrBl mulf_eq0.
      rewrite subr_eq0 /csn !(tnth_nth 0) nth_uniq ?size_tuple //.
      rewrite (inj_eq val_inj) (negbTE ne_ij) /= => root_q.
      have := root_i; rewrite rootE !hornerE (eqP root_q) mulr0 subr0.
      move=> root_p; move/(@Pdiv.ClosedField.coprimepP clK): cop_pq => /(_ k).
      by rewrite rootE root_p root_q /= => /(_ (erefl true)).
    move=> cop_p_sub_iq eq; have (i : 'I_3): exists r, (p - (csn i) *: q) == r^+2.
      pose P1 := \prod_(c <- cs | c != csn i) (p - c *: q).
      case: (@cf_copsqr clK u (p - (csn i) *: q) P1).
      + apply/eqP=> z_u; move: (cop_uv); rewrite z_u coprime0p.
        rewrite -size_poly_eq1 => /eqP sz_v; move: sz_u.
        by rewrite sz_v ltnn orbF z_u size_poly0.
      + rewrite /P1 -big_filter -(big_map (fun i => (p - i *: q)) xpredT id).
        rewrite coprimep_prod; apply/allP=> r /mapP [c].
        rewrite mem_filter => /andP [ne_ci c_in_cs] -> {r} /=.
        case/(nthP 0): c_in_cs=> j j_lt_sz cE; move: (cop_p_sub_iq i (inord j)).
        rewrite /csn !(tnth_nth 0) inordK -?(size_tuple cs) // -cE.
        apply; rewrite eqE /= inordK -?(size_tuple cs) //.
        rewrite -(@nth_uniq _ 0 _ i j _ _ uq_cs) // ?size_tuple //.
        by move: ne_ci; rewrite cE eq_sym /csn !(tnth_nth 0).
      + rewrite /P1 -(bigD1_seq (csn i)) //=; last by rewrite /csn mem_tnth.
        rewrite (eqP eq) /J; move/(congr1 (fun p => p^:F)): eq_Xpoly.
        pose C  := GRing.comp_rmorphism (tofrac_rmorphism _) (polyC_rmorphism _).
        pose E' := ec_of_ecmorph E (C K).
        have ->: Xpoly^:F = ec.Xpoly E' by rewrite map_XpolyE /= XpolyE.
        move/(congr1 (fun r => r.[p // q])); rewrite horner_Xpoly.
        move/(congr1 (fun x => x * q%:F^+3)); rewrite !mulrDl.
        rewrite expr_div_n [_*_^+3]mulrAC -[_*_/_]mulrA divff; last first.
          by rewrite expf_neq0 // tofrac_eq0 monic_neq0.
        rewrite mulr1 -[_*_^+3]mulrA -[_*_^+3]mulrA -exprN1.
        rewrite !exprnP -expfzDr ?(tofrac_eq0, monic_neq0) //.
        have ->: (-1 + 3%:Z) = 2 by []; rewrite -!exprnP.
        rewrite -!(tofracX, tofracM, tofracD) /= [_%:P * _]mulrA !mul_polyC.
        rewrite rmorph_prod /= horner_prod.
        rewrite (eq_bigr (fun i => (p - (cs`_i) *: q) // q)); last first.
          move=> j _; rewrite rmorphB /= !(map_polyX, map_polyC) !hornerE /=.
          rewrite tofracB exprN1 mulrDl mulNr -mul_polyC.
          by rewrite tofracM -mulrA divff ?(tofrac_eq0, monic_neq0) // mulr1.
        rewrite big_split /= big_const_seq /= mulr1 -!invfM -expr2 -exprS.
        rewrite tofracX [_*_^+3]mulrAC -[_*_^-1]mulrA divff; last first.
          by rewrite expf_neq0 // tofrac_eq0 monic_neq0.
        move/eqP; rewrite mulr1 -rmorph_prod /= tofrac_eq => /eqP->.
        by rewrite (big_nth 0) size_tuple.
      by move=> r /eqP Er2; exists r.
    move=> cE; set opprcs := [tuple of (map -%R cs)].
    set c := \col_(i < 4) (if i < 3 then xchoose (cE (inord i)) else qsrt)%N.
    have xchP: forall (j : 'I_3), p - (csn j)%:P * q = xchoose (cE j) ^+ 2.
      by move=> j; move: (xchooseP (cE j)) => /eqP; rewrite mul_polyC.
    have chi2: 2 \notin [char K].
      by rewrite inE /= ecu_chi2.
    move: (@L_2_39 clK chi2 (DetFree.A opprcs 1) [col p; q] c).
    rewrite ![[col p; q] _ _]mxE !(tnth_nth [tuple 0]) !inordK //=.
    rewrite !(tnth_nth 0) /= ![(size _ <= _)%N]leqNgt -negb_or sz_p /=.
    move=> H; absurd false=> //; apply H => {H} //.
    + by apply: DetFree.detfree; rewrite ?oner_eq0 // uniq_map //; exact: oppr_inj.
    apply/matrixP=> i j; rewrite ord1 => {j}.
    have ->: opprcs = [tuple -(csn 0%:I); -(csn 1%:I); -(csn 2%:I)].
      rewrite /csn /opprcs; case: {uq_cs cop_p_sub_iq csn eq_Xpoly cE opprcs c xchP} cs.
      case=> [|c1 [|c2 [|c3 [|]]]] //= er; rewrite !(tnth_nth 0) !inordK //=.
      by apply/eqP; rewrite eqE /=.
    rewrite MA_E !mxE big_ord_to_nat unlock /= addr0.
    rewrite ![[col p; q] _ _]mxE !(tnth_nth [tuple 0]) !inordK //=.
    rewrite !(tnth_nth 0) /= !mxE !(tnth_nth [tuple 0; 0]) /= !(tnth_nth 0).
    rewrite !inordK //; case: i; case=> [|[|[|[|i]]]] /=;
      try solve [by [] | by move=> _; rewrite mul1r polyC_opp mulNr xchP].
    by move=> _; rewrite mul0r add0r mul1r qE.
  Qed.

  Require Import fraction.
  Import FracInterp.

  Lemma L_2_38_fec (r s : {fraction {poly K}}):
       ~~ (isfcnt r)
    -> ~~ (isfcnt s)
    -> r ^+ 2 != s ^+ 3 + ((E #a)%:P)%:F * s + ((E #b)%:P)%:F.
  Proof.
    elim/fracredW: r => n1 d1 cop_1 d1_monic Ncct1.
    elim/fracredW: s => n2 d2 cop_2 d2_monic Ncct2.
    have [size_1 size_2] := (isfnctN_size Ncct1, isfnctN_size Ncct2).
    move: (L_2_38 size_2 size_1 cop_2 cop_1 d2_monic d1_monic) => h.
    rewrite !expr_div_n -!tofracX; apply/eqP => /(congr1 (fun x => x * (d1^+2)%:F)).
    rewrite -mulrA [_^-1*_]mulrC divff ?mulr1; last first.
      by rewrite tofrac_eq0 expf_neq0 // monic_neq0.
    rewrite [X in _ = X]mulrC => /(congr1 (fun x => x * (d2^+3)%:F)).
    rewrite -tofracM -[X in _ = X]mulrA !mulrDl -[_ * (d2^+3)%:F]mulrA.
    rewrite [_^-1*_]mulrC divff ?mulr1; last first.
      by rewrite tofrac_eq0 expf_neq0 // monic_neq0.
    rewrite -[(_ * (n2//d2)) * _]mulrA [(n2//d2)*_]mulrAC.
    rewrite {1}[(d2^+3)%:F]tofracX -exprN1 [_%:F^+3]exprnP -[_*_^(-1)]mulrA.
    rewrite -expfzDr ?(tofrac_eq0, monic_neq0) //= -exprnP.
    rewrite -!(tofracX, tofracM, tofracD) mulrA !mul_polyC.
    by move/eqP; rewrite tofrac_eq => /eqP eq; move: h; rewrite eq eqxx.
  Qed.
End ECRR_2_38.

(* -------------------------------------------------------------------- *)
Section L_2_40_base.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).
  Notation "f .[ x , y ]" := (eceval f x y).
  Notation "p %:E" := (ecX E p).

  Implicit Types f : {fraction ecpoly}.
  Hypothesis closedK : GRing.ClosedField.axiom K.
  Import PreClosedField.

  Local Notation clK := (ClosedFieldType K closedK).
  Local Notation PEF := (@tofrac _ \o ((ecX E) \o polyC)).
  Local Notation "x %:PEF" := (PEF x) (at level 2).
  Local Notation "x %:F"  := (tofrac x).
  Local Notation "x // y" := (x%:F / y%:F) (at level 50, no associativity).

  Local Notation "\- x"   := (FracInterp.opp x).
  Local Notation "x \+ y" := (FracInterp.add x y).
  Local Notation "x \* y" := (FracInterp.mul x y) (at level 30).
  Local Notation "x \^-1" := (FracInterp.gginv x) (at level 20).

  Local Notation neq0 := (mulf_neq0, invr_eq0, ecX_eq0, tofrac_eq0, conjp_eq0).

  Local Hint Extern 0 (is_true (ec.Xpoly _ != 0)) => exact: XpolyN0.

  Notation "f \Fo g"  := (comp_frac_fec f g).
  Notation "f \PFo g" := (comp_poly_fec g f).

  Local Notation "'Y" := [ecp 1 *Y + 0].

  Variable h : {fraction ecpoly}.
  Variable P : point K.
  Variable Q : point K.

  Hypothesis divhE : ecdiv h = << P >> - << Q >>.

  Lemma L_2_40_base: P = Q.
  Proof.
    have [->|ne_PQ] := eqVneq P Q; first by [].
    (* Some properties about h:
     * - order h R =  1 if R = P
     *             = -1 if R = Q
     *             =  0 otherwise
     * - h is not constant (as a fraction)
     * - P/Q are on the curve *)
    have ordhE: forall R, order h R = (R == P)%:Z - (R == Q)%:Z.
      move=> R; rewrite -ecdiv_coeffE divhE coeffB !coeffU.
      by rewrite !mul1r ![_ == R]eq_sym !natz.
    have ordhP: order h P = 1.
      by move: (ordhE P); rewrite (negbTE ne_PQ) eqxx subr0.
    have ordhQ: order h Q = -1.
      by move: (ordhE Q); rewrite eq_sym (negbTE ne_PQ) eqxx sub0r.
    have ordhNPQ R: R != P -> R != Q -> order h R = 0.
      move=> ne_PR ne_QR; move: (ordhE R);
        by rewrite (negbTE ne_PR) (negbTE ne_QR) subrr.
    have Ncct_h: ~~ (constant_fraction h).
      by apply: (constant_fraction_order0 (P := P)); rewrite ordhP.
    have oncveQ: oncurve Q.
      rewrite -[_ _ _]negbK; apply/negP;
        by move/(order_outcve h); rewrite ordhQ.
    have oncveP: oncurve P.
      rewrite -[_ _ _]negbK; apply/negP;
        by move/(order_outcve h); rewrite ordhP.
    have nz_h: h != 0.
      by apply/negP=> /eqP z_h; rewrite z_h order0 in ordhP.

    (* hR is the function associating h - h.(R) to R.
     * For a fixed S, (hR S) has the following properties
     * - it is not constant (as a fraction)
     * - its divisor is <<S>> - <<Q>> if S is on the curve and not equal to Q *)
    pose hR R := h - (evalK R h)%:PEF.
    have nz_hR R: hR R != 0.
      rewrite /hR subr_eq0; move: (evalK _ _) => c.
      apply/negP => /eqP  /(congr1 ((@order _ _)^~ P)).
      by rewrite orderC ordhP.
    have ecdivhRE R: oncurve R -> R != Q -> ecdiv (hR R) = << R >> - << Q >>.
      have hRdmp: ecdiv (hR R) = fgpos (ecdiv (hR R)) - fgneg (ecdiv h).
        rewrite -(Necdiv_transE _ (- (evalK R h))) /PEF /=.
        by rewrite polyC_opp ecXN tofracN -fg_decomp.
      move=> oncveR ne_RQ; rewrite hRdmp; have NhE: fgneg (ecdiv h) = <<Q>>.
        apply/eqP/freeg_eqP => S; rewrite coeff_fgnegE.
        rewrite divhE coeffB !coeffU !mul1r; do! case: eqP => //=.
        by move=> eq_QS eq_PS; rewrite eq_QS eq_PS eqxx in ne_PQ.
      have/(congr1 (@deg _))/eqP := hRdmp.
      rewrite degB {1}NhE degU deg_ecdiv_eq0 // eq_sym subr_eq0 => /eqP degPhR.
      rewrite NhE; congr (_ - _); move: degPhR; rewrite -[fgpos _]freeg_sumE.
      have ehR: eval (hR R) R = 0%:PP.
        rewrite /hR evalDr ?(evalN, evalC) // /evalK.
        case ehR: (eval h R) => [x|] /=; first by rewrite subrr.
        by move/eqP: ehR; rewrite -eval_lt0_order ordhE (negbTE ne_RQ) subr0.
      move/eqP: ehR; rewrite -eval_gt0_order // => gt0_ordhR.
      rewrite (bigD1_seq R) ?uniq_dom //=; last by rewrite mem_posdiv.
      rewrite degD [X in _ + X]raddf_sum /= degU coeff_fgposE ecdiv_coeffE.
      move: gt0_ordhR; rewrite gtz0_ge1 ler_eqVlt; case/orP; last first.
        move=> lt1_ordhR; rewrite maxr_r //; last first.
          by apply: (@ler_trans _ 1) => //; rewrite ltrW.
        move/(congr1 (+%R (-1))); rewrite [X in _ = X]addrC subrr.
        move/eqP; rewrite addrA [-1+_]addrC paddr_eq0; first last.
        + by apply: sumr_ge0=> S _; rewrite degU coeff_fgposE ler_maxr.
        + by rewrite subr_ge0 ltrW.
        case/andP; rewrite subr_eq0 => /eqP ordhR _.
        by rewrite ordhR ltrr in lt1_ordhR.
      move/eqP=> <-; rewrite maxr_r // -{2}[1]addr0 => /addrI /eqP.
      rewrite psumr_eq0 => [|S _]; last by rewrite degU coeff_fgposE ler_maxr.
      move=> all0; set S := \sum_(_ <- _ | _) _; have ->: S = 0; first last.
        by rewrite addr0.
      apply/eqP; rewrite {}/S big_seq_cond big1 // => S /andP [S_indom ne_SR].
      move/allP/(_ S S_indom)/implyP/(_ ne_SR): all0.
      by rewrite degU => /eqP->; rewrite freegU0.

    (* Any rational function s.t. Q is not in the domain of its divisor
     * can be expressed as a rational fraction in h *)
    have H f: order f Q = 0 -> exists r, f = r \Fo h; first move=> ordfQ.
      have [->|nz_f] := eqVneq f 0; first by exists 0; rewrite comp_fracC_fec.
      pose F := \prod_(R <- dom (ecdiv f)) (('X - (evalK R h)%:P)%:F)^(order f R).
      have FohE: F \Fo h = \prod_(R <- dom (ecdiv f)) (hR R)^(order f R).
        rewrite /F /hR comp_frac_prod_fec //; apply: eq_bigr => S _.
        rewrite -comp_fracX_exp ?comp_fracF_fec //; congr (_ ^ _).
        rewrite /comp_poly_fec rmorphB /= map_polyX map_polyC /=.
        by rewrite !hornerE.
      have nz_FohE: F \Fo h != 0.
        rewrite FohE prodf_seq_neq0; apply/allP.
        by move=> S _; apply/implyP=> _; rewrite expfz_neq0.
      have: ecdiv f = ecdiv (F \Fo h).
        rewrite FohE ecdiv_prod -?FohE // big_seq.
        rewrite (eq_bigr (fun S => (<<S>> - <<Q>>) *~ (order f S))); last first.
          move=> S S_in_domf; rewrite ecdivXz ecdivhRE //.
          + have [//|outcveS] := (boolP (oncurve S)); move: S_in_domf.
            by rewrite mem_dom inE ecdiv_coeffE order_outcve.
          + apply/eqP=> eq_SQ; move: ordfQ; rewrite -eq_SQ => ordfS.
            by move: S_in_domf; rewrite mem_dom inE ecdiv_coeffE ordfS.
        rewrite (eq_bigr (fun S => (<<order f S *g S>> - (<<Q>> *~ order f S)))); last first.
          by move=> S _; rewrite mulrzBl freegU_mulz intz.
        rewrite -big_seq sumrB -mulrz_sumr -ecdiv_degE.
        by rewrite deg_ecdiv_eq0 // subr0 -ecdiv_sumE.
      case/eq_ecdiv_proportional_func=> // c nz_c; exists ((c%:P%:F) * F).
      by rewrite comp_fracM_fec // mulrC comp_fracC_fec.

    (* Any rational function can be expressed as a rational fraction in h
     * (Generalization of previous property) *)
    have {H} H f: exists r, f = r \Fo h.
      have [->|nz_f] := eqVneq f 0; first by exists 0; rewrite comp_fracC_fec.
      move: (uniok_decomp (decomp_correct nz_h oncveQ)).
      move: (uniok_decomp (decomp_correct nz_f oncveQ)).
      rewrite ordhQ; set u := (unifun _ _); set r := (_ // _); set s := (_ // _).
      have nz_dc1_h: (decomp h Q).1 != 0 by rewrite decomp_nz_num.
      have nz_dc2_h: (decomp h Q).2 != 0 by rewrite decomp_nz_den.
      have nz_dc1_f: (decomp f Q).1 != 0 by rewrite decomp_nz_num.
      have nz_dc2_f: (decomp f Q).2 != 0 by rewrite decomp_nz_den.
      have nz_u: u != 0 by rewrite unifun_neq0.
      have nz_s: s != 0 by rewrite /s mulf_neq0 // ?invr_eq0 tofrac_eq0.
      move=> fE hE; have: u = h^-1 * s.
        rewrite hE invfM exprN1 invrK -mulrA mulVf ?mulr1 //.
        move=> uE; move: {hE} fE; rewrite uE expfzMl exprz_inv -mulrA.
        set g := (s^_ * r); have: order g Q = 0.
          rewrite /g order_mul ?(neq0, expfz_neq0) // order_expz.
          rewrite (uniok_order_decomp (decomp_correct nz_h oncveQ)).
          rewrite (uniok_order_decomp (decomp_correct nz_f oncveQ)).
          by rewrite addr0 mul0rz.
        case/H => t gE fE; exists (('X%:F)^(-order f Q) * t).
        rewrite comp_fracM_fec // -gE -comp_fracX_exp // comp_fracF_fec //.
        by rewrite /comp_poly_fec map_polyX hornerX {1}fE.

    (* Using previous result, we can express 'X and 'Y as rational
     * fractions in h. These functions are non constant. Moreover, they
     * are on the lifted base curve. *)
    case: (H ('X%:E)%:F) => f1 Ef1; case: (H 'Y%:F) => f2 Ef2.
    have oncve_f: f2 ^+ 2 = f1 ^+ 3 + ((E #a)%:P)%:F * f1 + ((E #b)%:P)%:F.
      apply (injective_comp_frac_fec closedK Ncct_h).
      rewrite !(comp_fracX_fec, comp_fracM_fec, comp_fracD_fec) //.
      rewrite -!Ef1 -!Ef2 !comp_fracC_fec -!(tofracX, tofracM, tofracD).
      by rewrite ecY_sqr expr1n mul1r XpolyE -!(ecXX, ecXM, ecXD) mul_polyC.
    have Ncct_f1: ~~ isfcnt f1.
      apply/negP => /isfcntfP [c Ef1c]; move/eqP: Ef1.
      rewrite Ef1c comp_fracC_fec tofrac_eq => /eqP /ecX_inj /eqP.
      by rewrite -subr_eq0 polyXsubC_eq0.
    have Ncct_f2: ~~ isfcnt f2.
      apply/negP => /isfcntfP [c Ef2c]; move/eqP: Ef2.
      rewrite Ef2c comp_fracC_fec tofrac_eq eqE /= => /eqP [].
      by move/eqP; rewrite oner_eq0.

    (* Last result conflicts with technical lemma L_2_38. QED. *)
    move: (L_2_38_fec E closedK) => /(_ f2 f1 Ncct_f2 Ncct_f1).
    by rewrite oncve_f eqxx.
  Qed.
End L_2_40_base.

(* -------------------------------------------------------------------- *)
Section L_2_40.
  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

  Notation Xpoly   := (@Xpoly K E).
  Notation ecpoly  := (@ecpoly K E).
  Notation oncurve := (@oncurve K E).

  Implicit Types f : {fraction ecpoly}.

  Hypothesis closedK : GRing.ClosedField.axiom K.

  Import PreClosedField.

  Hint Resolve closedK.

  Local Notation "D1 :~: D2" := (@ecdeqv _ E D1 D2).

  Lemma L_2_40 p q: << p >> :~: << q >> -> p = q.
  Proof. by case=> h /L_2_40_base ->. Qed.
End L_2_40.
