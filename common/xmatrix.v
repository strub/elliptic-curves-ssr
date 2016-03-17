(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun bigop.
From mathcomp Require Import seq fintype tuple choice perm ssralg zmodp.
From mathcomp Require Export matrix mxalgebra.

(* -------------------------------------------------------------------- *)
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Local Notation "n %:I" := (inord n) (at level 2, format "n %:I").

(* -------------------------------------------------------------------- *)
Section MxSubRows.
  Variables T : Type.
  Variables p m n : nat.

  Implicit Type M : 'M[T]_(m, n).

  Definition rows (rs : p.-tuple 'I_m) M : 'M_(p, n) :=
    \matrix_(i, j) (row (tnth rs i) M 0 j).
End MxSubRows.

Section MxSubRowsFacts.
  Variables R : ringType.
  Variables p m n r : nat.

  Implicit Type M  : 'M[R]_(m, n).
  Implicit Type rs : p.-tuple 'I_m.

  Definition subrs_mx (rs : p.-tuple 'I_m) : 'M[R]_(p, m) :=
    \sum_i delta_mx i (tnth rs i).

  Lemma rows_subrsE rs M: rows rs M = (subrs_mx rs) *m M.
  Proof.
    apply/matrixP=> i j; rewrite !mxE (bigD1 (tnth rs i)) //=.
    rewrite big1 ?addr0; last first.
      move=> k ne_k_ti; rewrite /subrs_mx (bigD1 i) //= !mxE.
      rewrite eqxx (negbTE ne_k_ti) add0r summxE.
      rewrite big1 ?mul0r // => i' ne_i'i; rewrite !mxE.
      by rewrite [i == i']eq_sym (negbTE ne_i'i).
    rewrite /subrs_mx summxE (bigD1 i) //= big1; last first.
      by move=> i' ne_i'i; rewrite mxE [i == i']eq_sym (negbTE ne_i'i).
    by rewrite mxE !eqxx addr0 mul1r.
  Qed.

  Lemma rowsE rs M i j: (rows rs M) i j = row (tnth rs i) M 0 j.
  Proof. by rewrite !mxE. Qed.

  Lemma row_perm_rows rs M s:
    row_perm s (rows rs M) = rows [tuple tnth rs (s i) | i < p] M.
  Proof.
    by apply/matrixP=> i j; rewrite !mxE tnth_map tnth_ord_tuple.
  Qed.
End MxSubRowsFacts.

Section MxSubRowsMoreFacts.
  Variables R S : ringType.
  Variables f : R -> S.
  Variables p m n r : nat.

  Implicit Type M  : 'M[R]_(m, n).
  Implicit Type rs : p.-tuple 'I_m.

  Lemma rows_mul rs M (B : 'M[R]_(n, r)):
    rows rs (M *m B) = (rows rs M) *m B.
  Proof. by rewrite !rows_subrsE -mulmxA. Qed.

  Lemma map_rows rs M:
    map_mx f (rows rs M) = rows rs (map_mx f M).
  Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.
End MxSubRowsMoreFacts.

(* -------------------------------------------------------------------- *)
Lemma mxrank_row_perm (F : fieldType) n m s (M : 'M[F]_(n, m)):
  \rank (row_perm s M) = \rank M.
Proof.
  rewrite row_permE -[_ *m _]trmxK mxrank_tr trmx_mul.
  rewrite mxrankMfree ?mxrank_tr // tr_perm_mx.
  by rewrite row_free_unit unitmx_perm.
Qed.

(* -------------------------------------------------------------------- *)
Definition mxdefE (T : Type) (n m : nat) (M : n.-tuple (m.-tuple T)) :=
  \matrix_(i, j) tnth (tnth M i) j.

Notation "[ 'matrix' r1 ; .. ; rn ]" :=
  (mxdefE [tuple of (tuple (@Tuple _ _ r1)) :: .. [:: tuple (@Tuple _ _ rn)] .. ])
  (at level 0, format "[ 'matrix' '['  x1 ; '/'  .. ; '/'  xn ']' ]").

Notation "[ 'col' x1 ; .. ; xn ]" :=
  (mxdefE [tuple of (tuple (@Tuple _ _ [:: x1])) :: .. [:: tuple (@Tuple _ _ [:: xn])] .. ])
  (at level 0, format "[ 'col' '['  x1 ; '/'  .. ; '/'  xn ']' ]").

Ltac cdet :=
  do ?[rewrite (expand_det_row _ ord0) //=;
    rewrite ?(big_ord_recl, big_ord0) //= ?mxE //=;
      rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
        rewrite ?(mul1r, mulr1, mulN1r, mul0r, mul1r, addr0) /=;
          do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].

(* -------------------------------------------------------------------- *)
Section MxConcrete.
  Variable K : idomainType.

  Hypothesis nz_2: 2%:R != 0 :> K.

  Lemma det2 (M : 'M[K]_2):
    \det M = (M 0%:I 0%:I) * (M 1%:I 1%:I) - (M 0%:I 1%:I) * (M 1%:I 0%:I).
  Proof.
    cdet; rewrite mulrN; congr (_ * _ - _ * _); congr (M _ _);
      by apply/eqP; rewrite eqE /= !inordK.
  Qed.

  Lemma det2_eq0 (a1 a2 : K):
    (\det [matrix [:: a1; a2]; [:: a1; -a2]] == 0) = (a1 * a2 == 0).
  Proof.
    rewrite det2 !mxE /tnth !inordK //=.
    rewrite !mulrN ![a2 * _]mulrC -mulr2n mulNrn oppr_eq0.
    by rewrite -mulr_natl [X in X = _]mulf_eq0 (negbTE nz_2).
  Qed.
End MxConcrete.
