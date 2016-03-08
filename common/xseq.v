(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp
Require Import ssreflect ssrnat ssrbool eqtype ssrfun fintype bigop.
From mathcomp
Require Export seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma subset_nil (T : eqType) (xs : seq T): {subset xs <= [::]} -> xs = [::].
Proof.
  case: xs => [|x xs] // H; absurd false=> //.
  by rewrite -(in_nil x) (H x) // in_cons eqxx.
Qed.

Lemma undup_cat (T : eqType) (s1 s2 : seq T):
  undup (s1 ++ s2) = undup (filter (predC (mem s2)) s1) ++ (undup s2).
Proof.
  elim: s1 => [|x s1 IH] //=.
  rewrite mem_cat; case x_in_s1: (x \in s1) => /=.
  + rewrite IH; congr (_ ++ _); case x_in_s2: (x \in s2) => //=.
    by rewrite mem_filter /= x_in_s2 x_in_s1.
  + case x_in_s2: (x \in s2) => //=.
    by rewrite mem_filter /= x_in_s1 andbF IH.
Qed.

Lemma undup_double (T : eqType) (s : seq T):
  undup (s ++ s) = undup s.
Proof.
  rewrite undup_cat (eq_in_filter (a2 := pred0)).
  + by rewrite filter_pred0.
  + by move=> x /= ->.
Qed.

Lemma perm_eq_map (T U : eqType) (f : T -> U) (xs ys : seq T):
  perm_eq xs ys -> (perm_eq (map f xs) (map f ys)).
Proof.
  by move/perm_eqP => H; apply/perm_eqP=> p; rewrite !count_map.
Qed.

Lemma perm_eq_undup (T : eqType) (xs ys : seq T):
  perm_eq xs ys -> perm_eq (undup xs) (undup ys).
Proof.
  move=> H; apply: uniq_perm_eq; rewrite ?undup_uniq //.
  by move=> x; rewrite !mem_undup; apply: perm_eq_mem.
Qed.

Lemma uniq_map (T U : eqType) (f : T -> U) (xs : seq T):
  injective f -> uniq (map f xs) = uniq xs.
Proof.
  move=> injf; apply: map_inj_in_uniq => x y _ _.
  by apply: injf.
Qed.

Lemma perm_cat (T : eqType) (xs1 xs2 ys1 ys2 : seq T):
  perm_eq xs1 ys1 -> perm_eq xs2 ys2 -> perm_eq (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  move=> /perm_eqP H1 /perm_eqP H2; apply/perm_eqP => p.
  by rewrite !count_cat H1 H2.
Qed.

Lemma mem_flattenP (T : eqType) (xss : seq (seq T)) (x : T):
  reflect
    (exists2 xs : seq T, xs \in xss & x \in xs)
    (x \in flatten xss).
Proof.
  apply: (iffP idP); elim: xss => [|xs xss IH] //=; try by case.
  + rewrite mem_cat; case/orP.
    * by move=> x_in_xs; exists xs => //; rewrite inE eqxx.
    * case/IH=> ys ys_in_xss x_in_ys; exists ys => //.
      by rewrite inE ys_in_xss orbT.
  + case=> ys; rewrite inE; case/orP.
    * by case/eqP=> -> {ys}; rewrite mem_cat=> ->.
    * move=> ys_in_xss x_in_ys; rewrite mem_cat IH ?orbT //.
      by exists ys.
Qed.

Lemma count_pred1 (T : eqType) (xs : seq T) (x : T):
  (count (pred1 x) xs != 0%N) = (x \in xs).
Proof.
  elim: xs => [|y ys IH] //=; rewrite inE [y == _]eq_sym.
  by rewrite addn_eq0 negb_and IH; case: (x == y).
Qed.

Lemma nth_assoc_index (T U : eqType) (f : T -> U) (D : seq T) (xU : U) (x : T):
  let ass := [seq (f x, x) | x <- D] in
    x \in D ->
      nth xU [seq m.1 | m <- ass] (index x [seq m.2 | m <- ass]) = f x.
Proof.
  move=> /= x_in_D; rewrite -!map_comp map_id (eq_map (f2 := f)) //.
  by rewrite (nth_map x) ?index_mem // nth_index.
Qed.

Lemma mem_ord n (k : 'I_n.+1): k \in [seq (inord i) | i <- iota 0 n.+1].
Proof.
  move: (mem_ord_enum k)=> /(map_f val).
  rewrite val_ord_enum -(mem_map val_inj) -map_comp.
  rewrite map_id_in // => m lt_m_Sn /=; rewrite inordK //.
  by move: lt_m_Sn; rewrite mem_iota add0n; case/andP.
Qed.

Lemma filter_pred1 (T : eqType) (i : T) s:
  filter (pred1 i) s = nseq (count (pred1 i) s) i.
Proof.
  by elim: s => [|x xs IH] //=; case: (x =P i) => [->|//=]; rewrite IH.
Qed.

Lemma count_nseq (T : eqType) (p : pred T) i n:
  count p (nseq n i) = (n * (p i))%N.
Proof. by elim: n => [|n IH] //=; rewrite IH mulSn. Qed.

Lemma mem_nseq (T : eqType) (c : T) i n: c \in nseq n i -> c = i.
Proof.
  by elim: n => [|n IH] //=; rewrite in_cons; case/orP; first move/eqP.
Qed.

Lemma undup_nseq (T : eqType) (i : T) n: n != 0%N -> undup (nseq n i) = [:: i].
  case: n => [//|n] _; have ->: nseq n.+1 i = rcons (nseq n i) i.
    apply: (@eq_from_nth _ i); first by rewrite size_rcons !size_nseq.
    move=> j _ /=; have ->: nth i (nseq n.+1 i) j = i.
      by case: j => [|j] //=; rewrite nth_nseq; case: ltnP.
    rewrite nth_rcons; case: ltnP => _; last by case: eqP.
    by rewrite nth_nseq; case: ltnP.
  rewrite -cats1 undup_cat (@eq_in_filter _ _ pred0); last first.
    by move=> c /= /mem_nseq/eqP h; apply: negbF; rewrite mem_seq1.
  by rewrite filter_pred0 cat0s.
Qed.

Lemma perm_eq_filter (T : eqType) (p : pred T) (xs ys : seq T):
  perm_eq xs ys -> perm_eq (filter p xs) (filter p ys).
Proof.
  move=> /perm_eqP peq; apply/perm_eqP=> pc.
  by rewrite !count_filter peq.
Qed.
