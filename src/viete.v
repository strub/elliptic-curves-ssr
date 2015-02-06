(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
Require Import seq tuple fintype bigop ssralg poly polydiv.
Require Import binomial perm finset path zmodp.

Import GRing.Theory.

Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* -------------------------------------------------------------------- *)
Section PolyMisc.
  (* All lemmas of this section should be moved *)

  Variable R : idomainType.

  Lemma coef_XsubCM (c : R) (p : {poly R}) (i : nat):
    (('X - c%:P) * p)`_i = (i != 0%N)%:R * p`_i.-1 - c * p`_i.
  Proof.
    case: i => [|i].
      by rewrite -!horner_coef0 !hornerE mulNr.
    rewrite mul1r -pred_Sn coefM big_ord_recl addrC.
    rewrite -horner_coef0 subn0 !hornerE mulNr; congr (_ + _).
    rewrite big_ord_recl lift0 subSS subn0 big1.
      by rewrite coefB coefX coefC subr0 mul1r addr0.
    by move=> j _; rewrite !lift0 coefB coefX coefC subr0 mul0r.
  Qed.

  Lemma coefS_XsubCM (c : R) (p : {poly R}) (i : nat):
    (('X - c%:P) * p)`_i.+1 = p`_i - c * p`_i.+1.
  Proof. by rewrite coef_XsubCM mul1r. Qed.

  Lemma lead_coef_prod (I : finType) (F : I -> {poly R}) :
    lead_coef (\prod_i F i) = \prod_i (lead_coef (F i)).
  Proof.
    elim/big_rec2: _ => [|i c p _ IH]; first by rewrite lead_coef1.
    by rewrite lead_coefM IH.
  Qed.
End PolyMisc.

(* -------------------------------------------------------------------- *)
Section Viete.
  Variable R : idomainType.

  Local Notation "n %:I" := (inord n) (at level 2, format "n %:I").

  Definition tmono (n : nat) (s : seq 'I_n) :=
    sorted ltn (map val s).

  Definition tlift1 n k (t : k.-tuple 'I_n) : k.-tuple 'I_n.+1 :=
    [tuple of map (lift 0) t].

  Lemma tlift1_sorted n k (t : k.-tuple 'I_n):
    tmono (tlift1 t) = tmono t.
  Proof.
    rewrite /tmono; case: t=> /= t _; case: t => [//|c t].
    rewrite -map_comp (eq_map (f2 := succn \o val)) //= map_comp.
    by rewrite (map_path (e' := ltn) (b := xpred0)) //; apply/hasPn.
  Qed.

  Definition Sfun (n : nat) (k : nat) : {set k.-tuple 'I_n}:=
    [set x : k.-tuple 'I_n | tmono x].

  Lemma Sfun_card n k: #|Sfun n k| = 'C(n, k).
  Proof. exact: card_ltn_sorted_tuples. Qed.

  Definition polysym (n k : nat) (cs : seq R) : R :=
    \sum_(s in Sfun n k) \prod_(i <- s) cs`_i.

  Definition Sfun_sub1 (n k : nat) := [set [tuple of      tlift1 x] | x in Sfun n k.+1].
  Definition Sfun_sub2 (n k : nat) := [set [tuple of 0 :: tlift1 x] | x in Sfun n k   ].

  Lemma Sfunsub_disjoint n k: [disjoint (Sfun_sub1 n k) & (Sfun_sub2 n k)].
  Proof.
    apply/pred0P=> x /=; apply/negP; case/andP.
    case/imsetP=> t1 _ -> /imsetP [t2 _] /eqP.
    rewrite eqE /=; case: t1 t2 => [t1 /= szt1] [t2 /= _].
    by case: t1 szt1.
  Qed.

  Lemma SfunS (n k : nat):
    Sfun n.+1 k.+1 = (Sfun_sub1 n k) :|: (Sfun_sub2 n k).
  Proof.
    have Ss1: forall x, x \in Sfun_sub1 n k -> tmono x.
    + move=> x /imsetP [t]; rewrite inE => St -> /=.
      by rewrite tlift1_sorted.
    have Ss2: forall x, x \in Sfun_sub2 n k -> tmono x.
    + move=> x /imsetP [t]; rewrite inE => St -> /=.
      rewrite /tmono /=; case: t St; case=> [|ht t] /= _ // St.
      rewrite -map_comp (eq_map (f2 := (fun x : 'I__ => x.+1))) //.
      move: St; rewrite /tmono /= /map_path.
      rewrite -(map_path (e := ltn) (b := pred0) (h := succn)) //.
      * by rewrite /bump leq0n add1n -map_comp.
      * by apply/hasPn.
    have s12_sb_D: (Sfun_sub1 n k) :|: (Sfun_sub2 n k) \subset Sfun n.+1 k.+1.
    + apply/subsetP=> t; rewrite in_setU; case/orP.
      * by move=> /Ss1 t_in_s1; rewrite /Sfun inE.
      * by move=> /Ss2 t_in_s2; rewrite /Sfun inE.
    apply/esym/eqP; rewrite eqEcard s12_sb_D /=.
    rewrite cardsU disjoint_setI0 ?Sfunsub_disjoint // cards0 subn0.
    rewrite !card_imset ?Sfun_card ?binS //.
    + move=> t1 t2 /= /eqP; rewrite eqE /= eqseq_cons eqxx /=.
      move/eqP/inj_map => -/(_ (@lift_inj n.+1 ord0)).
      by move=> eq_t; apply/eqP; rewrite eqE /= eq_t.
    + move=> t1 t2 /= /eqP; rewrite eqE /=.
      move/eqP/inj_map => -/(_ (@lift_inj n.+1 ord0)).
      by move=> eq_t; apply/eqP; rewrite eqE /= eq_t.
  Qed.

  Lemma Sfunn (n : nat): Sfun n.+1 n.+1 = [set [tuple i | i < n.+1]].
  Proof.
    pose F n := [tuple i | i < n.+1].
    have Fkmb: F n \in Sfun n.+1 n.+1.
      by rewrite inE /= /tmono -map_comp val_enum_ord iota_ltn_sorted.
    have/setD1K := Fkmb => <-; have: #|Sfun n.+1 n.+1| == 1%N.
      by rewrite Sfun_card binn.
    rewrite (cardsD1 (F n)) Fkmb add1n => /eqP [].
    by move/eqP; rewrite cards_eq0 => /eqP->; rewrite setU0.
  Qed.

  Lemma Sfun11: Sfun 1 1 = [set [tuple 0 : 'I_1]].
  Proof.
    apply/esym/eqP; rewrite eqEcard cards1 Sfun_card andbT.
    by apply/subsetP=> t; rewrite inE => /eqP->; rewrite inE.
  Qed.

  Lemma viete n (k : 'I_n.+1) (cs : n.+1.-tuple R):
    polysym n.+1 k.+1 cs = (-1)^+k.+1 * (\prod_(c <- cs) ('X - c%:P))`_(n - k).
  Proof.
    elim: n k cs => [|n IH] k cs.
      case: cs; case=> [|c [|c' cs]] // sz_c.
      rewrite ord1 expr1 subn0 big_seq1 -horner_coef0.
      by rewrite !hornerE mulrNN mul1r /polysym Sfun11 big_set1 big_seq1.
    case: (k =P n.+1%:I)=> [->|/eqP].
      rewrite inordK // subnn -horner_coef0 horner_prod.
      rewrite (eq_bigr (fun c => -c)) /=; last first.
        by move=> c _; rewrite !hornerE.
      rewrite big_tnth prodrN card_ord {1}size_tuple mulrA.
      rewrite -exprMn mulrNN mulr1 expr1n mul1r.
      rewrite /polysym Sfunn big_set1 /= map_id.
      rewrite -(big_tnth _ _ cs xpredT (fun x => x)).
      rewrite (eq_bigr (fun i:'I__ => cs`_i)) //.
      rewrite [X in _ = X](big_nth 0) big_mkord size_tuple.
      by rewrite /index_enum -enumT.
    rewrite neq_ltn; case/orP; last first.
      by rewrite inordK // ltnNge -ltnS ltn_ord.
    rewrite inordK // => lt_k_Sn; case: cs => /=.
    case=> [|c cs] //= /eqP [/eqP sz_cs]; rewrite big_cons subSn //.
    rewrite coefS_XsubCM mulrBr; pose tcs := Tuple sz_cs.
    move: (IH k%:I tcs); rewrite !inordK // mulrCA => <-.
    pose P := [predU Sfun_sub1 n.+1 k & Sfun_sub2 n.+1 k].
    rewrite {1}/polysym SfunS (eq_bigl P); last first.
      by rewrite {}/P /= => t; rewrite !inE.
    set x := - _;rewrite bigU {}/P ?Sfunsub_disjoint //=; congr (_ + _).
    + rewrite big_imset /=; last first.
        move=> t u tD uD /= [] /inj_map eq; apply/eqP.
        by rewrite eqE /= eq //; apply: lift_inj.
      by apply: eq_bigr => t tD; rewrite big_map.
    + rewrite big_imset /=; last first.
        move=> t u tD uD /= [] /inj_map eq; apply/eqP.
        by rewrite eqE /= eq //; apply: lift_inj.
      apply/esym; rewrite {}/x; case: (k =P 0) => [->|/eqP].
        rewrite expr1 mulN1r mulrN opprK subn0.
        set p := \prod_(_ <- _) _; have sz_p: size p = n.+2.
          by rewrite /p size_prod_XsubC (eqP sz_cs).
        rewrite {1}[n.+1]pred_Sn -{1}sz_p -lead_coefE.
        rewrite /p big_tnth lead_coef_prod big1; last first.
          by move=> i _; rewrite lead_coefXsubC.
        rewrite mulr1; have: #|Sfun n.+1 0| == 1%N by rewrite Sfun_card bin0.
        case/cards1P=> t ->; rewrite big_set1 big_cons /=.
        have: t == [::] :> seq _ by rewrite -size_eq0 size_tuple.
        by move/eqP=> ->; rewrite big_nil mulr1.
      move=> nz_k; rewrite -[X in (_ - X)%N]prednK ?lt0n //.
      rewrite subnSK -1?ltnS; last rewrite prednK ?lt0n //.
      rewrite -mulrN -mulN1r [X in c * X]mulrA -exprS.
      rewrite -signr_odd /= negbK signr_odd; move: (IH (k.-1)%:I tcs).
      rewrite inordK ?prednK ?lt0n // 1?ltnW // => <-.
      rewrite /polysym big_distrr /=; apply: eq_bigr => t tD.
      by rewrite big_cons big_map.
  Qed.

  Lemma Sfun1 (n : nat): Sfun n 1 = [set [tuple i] | i in 'I_n].
  Proof.
    apply/eqP; rewrite eqEcard Sfun_card bin1 imset_card.
    rewrite card_image; last by move=> i1 i2 /= [->].
    rewrite card_ord leqnn andbT /Sfun; apply/subsetP.
    move=> x _; apply/imsetP; exists (tnth x 0) => //.
    by apply/eq_from_tnth=> i; rewrite ord1.
  Qed.

  Lemma polysym1 (n : nat) (cs : n.-tuple R):
    polysym n 1 cs = \sum_(c <- cs) c.
  Proof.
    case: cs=> cs sz_cs /=; rewrite /polysym Sfun1.
    rewrite big_imset //=; last by move=> i1 i2 _ _ /= [->].
    rewrite (eq_bigr (fun i : 'I_n => cs`_i)); last first.
      by move=> i _; rewrite big_seq1.
    by rewrite [X in _ = X](big_nth 0) big_mkord (eqP sz_cs).
  Qed.

  Lemma viete0 (n : nat) (cs : n.+1.-tuple R):
    \sum_(c <- cs) c = - (\prod_(c <- cs) ('X - c%:P))`_n.
  Proof.
    move: (viete 0 cs);
      by rewrite polysym1 expr1 mulNr mul1r subn0.
  Qed.
End Viete.
