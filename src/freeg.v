(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype choice xseq.
Require Import fintype bigop ssralg ssrfun ssrint ssrnum.
Require Import generic_quotient fracfield.

Import GRing.Theory.
Import Num.Theory.

Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Defensive Implicit.

(* -------------------------------------------------------------------- *)
Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'freeg' K }" (at level 0, format "{ 'freeg'  K }").
Reserved Notation "[ 'freeg' S ]" (at level 0, format "[ 'freeg'  S ]").

(* -------------------------------------------------------------------- *)
Module FreegDefs.
  Section Defs.
    Variable K : choiceType.

    Definition reduced (D : seq (int * K)) :=
         (uniq [seq zx.2 | zx <- D])
      && (all  [pred zx | zx.1 != 0] D).

    Lemma reduced_uniq: forall D, reduced D -> uniq [seq zx.2 | zx <- D].
    Proof. by move=> D /andP []. Qed.

    Record prefreeg : Type := mkPrefreeg {
      seq_of_prefreeg : seq (int * K);
      _ : reduced seq_of_prefreeg
    }.

    Implicit Arguments mkPrefreeg [].

    Local Coercion seq_of_prefreeg : prefreeg >-> seq.

    Lemma prefreeg_reduced: forall (D : prefreeg), reduced D.
    Proof. by case. Qed.

    Lemma prefreeg_uniq: forall (D : prefreeg), uniq [seq zx.2 | zx <- D].
    Proof. by move=> D; apply reduced_uniq; apply prefreeg_reduced. Qed.

    Canonical prefreeg_subType :=
      [subType for seq_of_prefreeg by prefreeg_rect].

    Definition prefreeg_eqMixin := Eval hnf in [eqMixin of prefreeg by <:].
    Canonical  prefreeg_eqType  := Eval hnf in EqType _ prefreeg_eqMixin.

    Definition prefreeg_choiceMixin := Eval hnf in [choiceMixin of prefreeg by <:].
    Canonical  prefreeg_choiceType  := Eval hnf in ChoiceType prefreeg prefreeg_choiceMixin.
  End Defs.

  Implicit Arguments mkPrefreeg [K].

  Section Quotient.
    Variable K : choiceType.

    Local Coercion seq_of_prefreeg : prefreeg >-> seq.

    Definition equiv (D1 D2 : prefreeg K) := perm_eq D1 D2.

    Lemma equiv_refl: reflexive equiv.
    Proof. by move=> D; apply: perm_eq_refl. Qed.

    Lemma equiv_sym: symmetric equiv.
    Proof. by move=> D1 D2; apply: perm_eq_sym. Qed.

    Lemma equiv_trans: transitive equiv.
    Proof.
      by move=> D1 D2 D3 H12 H23; apply (perm_eq_trans H12 H23).
    Qed.

    Canonical prefreeg_equiv := EquivRel equiv equiv_refl equiv_sym equiv_trans.
    Canonical prefreeg_equiv_direct := defaultEncModRel equiv.

    Definition type := {eq_quot equiv}.
    Definition type_of of phant K := type.

    Notation "{ 'freeg' K }" := (type_of (Phant K)).

    Canonical freeg_quotType   := [quotType of type].
    Canonical freeg_eqType     := [eqType of type].
    Canonical freeg_choiceType := [choiceType of type].
    Canonical freeg_eqQuotType := [eqQuotType equiv of type].

    Canonical freeg_of_quotType   := [quotType of {freeg K}].
    Canonical freeg_of_eqType     := [eqType of {freeg K}].
    Canonical freeg_of_choiceType := [choiceType of {freeg K}].
    Canonical freeg_of_eqQuotType := [eqQuotType equiv of {freeg K}].
  End Quotient.

  Module Exports.
    Coercion seq_of_prefreeg : prefreeg >-> seq.

    Canonical prefreeg_equiv.
    Canonical prefreeg_equiv_direct.

    Canonical prefreeg_subType.
    Canonical prefreeg_eqType.
    Canonical prefreeg_choiceType.
    Canonical prefreeg_equiv.
    Canonical freeg_quotType.
    Canonical freeg_eqType.
    Canonical freeg_choiceType.
    Canonical freeg_eqQuotType.
    Canonical freeg_of_quotType.
    Canonical freeg_of_eqType.
    Canonical freeg_of_choiceType.
    Canonical freeg_of_eqQuotType.

    Notation prefreeg   := prefreeg.
    Notation fgequiv    := equiv.
    Notation mkPrefreeg := mkPrefreeg.

    Notation reduced := reduced.

    Notation "{ 'freeg' T }" := (type_of (Phant T)).

    Identity Coercion type_freeg_of : type_of >-> type.
  End Exports.
End FreegDefs.

Export FreegDefs.Exports.

(* -------------------------------------------------------------------- *)
Section FreegTheory.
  Variable K : choiceType.

  Lemma perm_eq_fgrepr:
    forall (D : prefreeg K), perm_eq (repr (\pi_{freeg K} D)) D.
  Proof.
    by move=> S; rewrite -/(fgequiv _ _); apply/eqmodP; rewrite reprK.
  Qed.

  Lemma reduced_uniq (D : seq (int * K)):
    reduced D -> uniq [seq zx.2 | zx <- D].
  Proof. by case/andP. Qed.

  Lemma prefreeg_reduced: forall (D : prefreeg K), reduced D.
  Proof. by case. Qed.

  Lemma prefreeg_uniq: forall (D : prefreeg K), uniq [seq zx.2 | zx <- D].
  Proof. by move=> D; apply reduced_uniq; apply prefreeg_reduced. Qed.

  Fixpoint augment (D : seq (int * K)) (z : int) x :=
    if   D is ((z', x') as d) :: D
    then if x == x' then (z + z', x) :: D else d :: (augment D z x)
    else [:: (z, x)].

  Definition reduce D :=
    filter
      [pred zx | zx.1 != 0]
      (foldr (fun zx D => augment D zx.1 zx.2) [::] D).

  Definition predom (D : seq (int * K)) : seq K := [seq x.2 | x <- D].

  Definition dom (D : {freeg K}) := [seq zx.2 | zx <- (repr D)].

  Lemma uniq_dom D: uniq (dom D).
  Proof. by rewrite /dom; case: (repr D)=> /= {D} D; case/andP. Qed.

  Lemma reduced_cons z (D : seq (int * K)):
    reduced (z :: D) = [&& z.1 != 0, z.2 \notin predom D & reduced D].
  Proof.
    rewrite /reduced map_cons cons_uniq /= !andbA; congr (_ && _).
    by rewrite andbAC; congr (_ && _); rewrite andbC.
  Qed.

  Lemma mem_augment: forall D z x y,
    x != y -> y \notin (predom D) -> y \notin (predom (augment D z x)).
  Proof.
    move=> D z x y neq_xy; elim: D => [|[z' x'] D IH] /=.
    + by move=> _; rewrite mem_seq1 eq_sym.
    + rewrite in_cons negb_or => /andP [neq_yx' HyD].
      have [->|neq_xx'] := eqVneq x x'; rewrite ?eqxx /=.
      * by rewrite in_cons negb_or neq_yx' HyD.
      * by rewrite (negbTE neq_xx') /= in_cons (negbTE neq_yx') IH.
  Qed.

  Lemma uniq_predom_augment D z x:
    uniq (predom D) -> uniq (predom (augment D z x)).
  Proof.
    elim: D => [|[z' x'] D IH] //=.
    have [->|neq_xx'] := eqVneq x x'; rewrite ?eqxx //.
    rewrite (negbTE neq_xx') /=; case/andP=> Hx'D /IH ->.
    by rewrite andbT; apply mem_augment.
  Qed.

  Lemma uniq_predom_reduce D: uniq (predom (reduce D)).
  Proof.
    rewrite /reduce; set D' := (foldr _ _ _).
    apply (subseq_uniq (s2 := predom D')).
    + by apply map_subseq; apply filter_subseq.
    rewrite /D' => {D'}; elim: D=> [|[z x] D IH] //=.
    by apply uniq_predom_augment.
  Qed.

  Lemma reduced_reduce D: reduced (reduce D).
  Proof.
    rewrite /reduced uniq_predom_reduce /=.
    by apply/allP=> zx; rewrite mem_filter=> /andP [].
  Qed.

  Lemma outdom_augmentE D k x:
    x \notin predom D -> augment D k x = rcons D (k, x).
  Proof.
    elim: D=> [//|[k' x'] D IH] /=; rewrite in_cons.
    by case/norP=> /negbTE -> /IH ->.
  Qed.

  Lemma reduce_reduced D: reduced D -> reduce D = rev D.
  Proof.
    move=> rD; rewrite /reduce; set S := foldr _ _ _.
    have ->: S = rev D; rewrite {}/S.
      elim: D rD => [//|[k x] D IH]; rewrite reduced_cons /=.
      case/and3P=> nz_k x_notin_D rD; rewrite IH //.
      rewrite rev_cons outdom_augmentE //; move: x_notin_D.
      by rewrite /predom map_rev mem_rev.
    rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
    move=> kx; rewrite mem_rev /=; case/andP: rD.
    by move=> _ /allP /(_ kx).
  Qed.

  Lemma reduceK (D : seq (int * K)): reduced D -> perm_eq (reduce D) D.
  Proof.
    move/reduce_reduced=> ->; apply/perm_eqP=> p.
    rewrite /rev -[X in _ = X]addn0; have ->: (0 = count p [::])%N by [].
    elim: D [::] => [|xk D IH] S.
      by rewrite catrevE /= add0n.
      by rewrite /= IH /= addnCA addnA.
  Qed.

  Definition Prefreeg (D : seq (int * K)) :=
    mkPrefreeg (reduce D) (reduced_reduce D).

  Lemma PrefreegK:
    forall (D : prefreeg K), Prefreeg D = D %[mod_eq (@fgequiv K)].
  Proof.
    case=> [D HD]; rewrite /Prefreeg; apply/eqmodP=> /=.
    by rewrite /fgequiv /=; apply: reduceK.
  Qed.

  Definition Freeg := lift_embed {freeg K} Prefreeg.
  Canonical to_freeg_pi_morph := PiEmbed Freeg.

  Local Notation "[ 'freeg' S ]" := (Freeg S).

  Local Notation "<< z *g p >>" := [freeg [:: (z, p)]].
  Local Notation "<< p >>"      := [freeg [:: (1%Z, p)]].

  Definition prefreeg_opp (D : seq (int * K)) :=
    [seq (-xz.1, xz.2) | xz <- D].

  Section Morphism.
    Variable G : zmodType.
    Variable f : K -> G.

    Definition prelift (D : seq (int * K)) : G :=
      \sum_(x <- D) (f x.2) *~ x.1.

    Lemma prelift_nil: prelift [::] = 0.
    Proof. by rewrite /prelift big_nil. Qed.

    Lemma prelift_cons D k x: prelift ((k, x) :: D) = (f x) *~ k + (prelift D).
    Proof. by rewrite /prelift big_cons. Qed.

    Lemma prelift_cat D1 D2: prelift (D1 ++ D2) = prelift D1 + prelift D2.
    Proof. by rewrite /prelift big_cat. Qed.

    Lemma prelift_seq1 k x: prelift [:: (k, x)] = (f x) *~ k.
    Proof. by rewrite /prelift big_seq1. Qed.

    Lemma prelift_perm_eq D1 D2: perm_eq D1 D2 -> prelift D1 = prelift D2.
    Proof. by move=> peq; apply: eq_big_perm. Qed.

    Lemma prelift_augment D k x:
      prelift (augment D k x) = ((f x) *~ k) + (prelift D).
    Proof.
      elim: D => [|[k' x'] D IH] //=.
        by rewrite prelift_seq1 prelift_nil !simpm.
      have [->|ne_xx'] := eqVneq x x'.
        by rewrite eqxx !prelift_cons mulrzDl addrA.
        by rewrite (negbTE ne_xx') !prelift_cons IH addrCA.
    Qed.

    Lemma prelift_reduce D: prelift (reduce D) = prelift D.
    Proof.
      rewrite /reduce; set S := foldr _ _ _; set rD := filter _ _.
      have ->: prelift rD = prelift S; rewrite ?/rD => {rD}.
        elim: S => [//|[k x] S IH] /=; have [->|nz_k] := eqVneq k 0.
          by rewrite eqxx /= prelift_cons mulr0z !simpm.
        by rewrite nz_k !prelift_cons IH.
      rewrite /S; elim: {S} D => [//|[k x] D IH].
      by rewrite prelift_cons /= prelift_augment IH.
    Qed.

    Lemma prelift_opp D: prelift (prefreeg_opp D) = -(prelift D).
    Proof.
      rewrite /prelift big_map big_endo ?oppr0 //=; last exact: opprD.
      by apply: eq_bigr => i _; rewrite mulrNz.
    Qed.

    Lemma prelift_repr D: prelift(repr (\pi_{freeg K} D)) = prelift D.
    Proof. by rewrite (prelift_perm_eq (perm_eq_fgrepr _)). Qed.

    Definition lift   := fun (D : prefreeg _) => prelift D.
    Definition fglift := lift_fun1 {freeg K} lift.

    Lemma pi_fglift: {mono \pi_{freeg K} : D / lift D >-> fglift D}.
    Proof.
      case=> [D redD]; unlock fglift; rewrite !piE.
      by apply/prelift_perm_eq; apply: perm_eq_fgrepr.
    Qed.

    Canonical pi_fglift_morph := PiMono1 pi_fglift.

    Lemma fglift_Freeg (D : seq (int * K)): fglift [freeg D] = prelift D.
    Proof.
      unlock Freeg; unlock fglift; rewrite !piE /lift.
      rewrite (prelift_perm_eq (perm_eq_fgrepr _)) /=.
      exact: prelift_reduce.
    Qed.

    Lemma liftU k x: fglift << k *g x >> = (f x) *~ k.
    Proof. by rewrite fglift_Freeg prelift_seq1. Qed.
  End Morphism.

  (* -------------------------------------------------------------------- *)
  Definition coeff k D : int := fglift (fun k' => (k' == k)%:Z) D.

  Lemma coeffU k x y: coeff y << k *g x >> = k * (x == y).
  Proof. by rewrite /coeff liftU -mulrzl intz. Qed.

  Definition precoeff k (D : seq (int * K)) : int :=
    \sum_(x <- D | x.2 == k) x.1.

  Lemma precoeffE k:
    precoeff k =1 prelift (fun k' => (k' == k)%:Z).
  Proof.
    move=> D; rewrite /precoeff /prelift; apply/esym.
    rewrite (bigID [pred x | x.2 == k]) /= addrC big1; last first.
      by move=> i /negbTE ->; rewrite mul0rz.
    rewrite add0r; apply: eq_bigr=> i /eqP ->.
    by rewrite eqxx /= intz.
  Qed.

  Lemma precoeff_nil k: precoeff k [::] = 0.
  Proof. by rewrite /precoeff big_nil. Qed.

  Lemma precoeff_cons z D k x:
    precoeff z ((k, x) :: D) = (x == z)%:R * k + (precoeff z D).
  Proof.
    by rewrite /precoeff big_cons /=; case: (_ == _); rewrite !simpm.
  Qed.

  Lemma precoeff_cat k D1 D2:
    precoeff k (D1 ++ D2) = (precoeff k D1) + (precoeff k D2).
  Proof. by rewrite !precoeffE prelift_cat. Qed.

  Lemma precoeff_opp k D: precoeff k (prefreeg_opp D) = -(precoeff k D).
  Proof. by rewrite !precoeffE prelift_opp. Qed.

  Lemma precoeff_perm_eq k D1 D2: perm_eq D1 D2 -> precoeff k D1 = precoeff k D2.
  Proof. by rewrite !precoeffE => /prelift_perm_eq. Qed.

  Lemma precoeff_repr k D: precoeff k (repr (\pi_{freeg K} D)) = precoeff k D.
  Proof. by rewrite !precoeffE prelift_repr. Qed.

  Lemma precoeff_reduce k D: precoeff k (reduce D) = precoeff k D.
  Proof. by rewrite !precoeffE prelift_reduce. Qed.

  Lemma precoeff_outdom x D: x \notin predom D -> precoeff x D = 0.
  Proof.
    move=> x_notin_D; rewrite /precoeff big_seq_cond big_pred0 //.
    case=> k z /=; have [->|/negbTE ->] := eqVneq z x; last first.
      by rewrite andbF.
    rewrite eqxx andbT; apply/negP=> /(map_f (@snd _ _)).
    by rewrite (negbTE x_notin_D).
  Qed.

  Lemma reduced_mem D k x: reduced D ->
    ((k, x) \in D) = (precoeff x D == k) && (k != 0).
  Proof.
    elim: D => [|[k' x'] D IH] /=.
      by rewrite in_nil precoeff_nil eq_sym andbN.
    rewrite reduced_cons => /and3P [/= nz_k' x'ND rD].
    rewrite in_cons precoeff_cons IH //.
    move: x'ND; have [->|nz_x'x] := eqVneq x' x.
      move=> xND; rewrite eqE /= eqxx andbT mul1r.
      rewrite precoeff_outdom // addr0 [0 == _]eq_sym.
      by rewrite andbN orbF [k == _]eq_sym andb_idr // => /eqP <-.
    rewrite eqE /= [x == _]eq_sym (negbTE nz_x'x) andbF.
    by rewrite mul0r add0r.
  Qed.

  Lemma coeff_Freeg k D: coeff k [freeg D] = precoeff k D.
  Proof. by rewrite /coeff fglift_Freeg precoeffE. Qed.

  Lemma freegequivP D1 D2 (HD1 : reduced D1) (HD2 : reduced D2):
    reflect
      (precoeff^~ D1 =1 precoeff^~ D2)
      (fgequiv (mkPrefreeg D1 HD1) (mkPrefreeg D2 HD2)).
  Proof.
    apply: (iffP idP); rewrite /fgequiv /=.
    + by move=> H k; apply: precoeff_perm_eq.
    move=> H; apply uniq_perm_eq.
    + by move/reduced_uniq: HD1=> /map_uniq.
    + by move/reduced_uniq: HD2=> /map_uniq.
    move=> [z k]; have [->|nz_z] := eqVneq z 0.
      by rewrite !reduced_mem // eqxx !andbF.
    by rewrite !reduced_mem // nz_z !andbT H.
  Qed.

  Lemma fgequivP (D1 D2 : prefreeg K):
    reflect
      (precoeff^~ D1 =1 precoeff^~ D2)
      (fgequiv D1 D2).
  Proof. by case: D1 D2 => [D1 HD1] [D2 HD2]; apply/freegequivP. Qed.

  Lemma freeg_eqP (D1 D2 : {freeg K}):
    reflect (coeff^~ D1 =1 coeff^~ D2) (D1 == D2).
  Proof.
    apply: (iffP idP); first by move/eqP=> ->.
    elim/quotW: D1 => D1; elim/quotW: D2 => D2.
    move=> eqc; rewrite eqmodE; apply/fgequivP=> k.
    by move: (eqc k); rewrite /coeff !piE /lift !precoeffE.
  Qed.

  Lemma perm_eq_Freeg (D1 D2 : seq (int * K)):
    perm_eq D1 D2 -> [freeg D1] = [freeg D2].
  Proof.
    move=> peq; apply/eqP/freeg_eqP=> k.
    by rewrite !coeff_Freeg; apply precoeff_perm_eq.
  Qed.

  Lemma freeg_repr (D : {freeg K}): [freeg (repr D)] = D.
  Proof.
    apply/eqP/freeg_eqP=> k.
    by rewrite coeff_Freeg precoeffE /coeff; unlock fglift.
  Qed.

  Lemma Freeg_dom:
    forall D, [freeg [seq (coeff z D, z) | z <- dom D]] = D.
  Proof.
    move=> D; apply/esym/eqP/freeg_eqP=> k.
    rewrite -{1 2}[D]freeg_repr !coeff_Freeg /dom.
    case: (repr D)=> {D} D rD /=; rewrite -map_comp map_id_in //.
    move=> [z x]; rewrite reduced_mem // => /andP [/eqP <- _].
    by rewrite /= coeff_Freeg.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma precoeff_uniqE (D : seq (int * K)) k:
      uniq (predom D) ->
        precoeff k D = [seq x.1 | x <- D]`_(index k (predom D)).
  Proof.
    elim: D => [|[z x D IH]].
      by rewrite precoeff_nil nth_nil.
    rewrite precoeff_cons /= => /andP [x_notin_D /IH ->].
    have [eq_xk|ne_xk] := altP (x =P k); last by rewrite mul0r add0r.
    rewrite mul1r /= nth_default ?addr0 //.
    move: (index_size k (predom D)); rewrite leq_eqVlt.
    rewrite index_mem -eq_xk (negbTE x_notin_D) orbF.
    by move=> /eqP ->; rewrite !size_map.
  Qed.

  Lemma precoeff_mem_uniqE (D : seq (int * K)) kz:
     uniq (predom D) -> kz \in D -> precoeff kz.2 D = kz.1.
  Proof.
    move=> uniq_domD kz_in_D; have uniq_D: (uniq D).
      by move/map_uniq: uniq_domD.
    rewrite precoeff_uniqE // (nth_map kz); last first.
      by rewrite -(size_map (@snd _ _)) index_mem map_f.
    rewrite nth_index_map // => {kz kz_in_D} kz1 kz2.
    move=> kz1_in_D kz2_in_D eq; apply/eqP; case: eqP=> //.
    move/eqP;
      rewrite -[kz1](nth_index kz1 (s := D)) //;
      rewrite -[kz2](nth_index kz1 (s := D)) //.
    rewrite nth_uniq ?index_mem //.
    set i1 := index _ _; set i2 := index _ _ => ne_i.
    have := ne_i; rewrite -(nth_uniq kz1.2 (s := predom D)) //;
      try by rewrite size_map index_mem.
    by rewrite !(nth_map kz1) ?index_mem // !nth_index // eq eqxx.
  Qed.

  Lemma mem_dom (D : {freeg K}) : dom D =i [pred k | coeff k D != 0].
  Proof.
    elim/quotW: D; case=> D rD; rewrite /dom => z; rewrite !inE.
    rewrite (perm_eq_mem (perm_eq_map _ (perm_eq_fgrepr _))) /=.
    unlock coeff; rewrite !piE /lift /= -precoeffE.
    rewrite precoeff_uniqE -/(predom _); last by case/andP: rD.
    case/andP: rD=> _ /allP rD; apply/esym.
    case z_in_D: (_ \in _); last first.
      rewrite nth_default // size_map -(size_map (@snd _ _)).
      by rewrite leqNgt index_mem z_in_D.
    rewrite (nth_map (0, z)); last first.
      by rewrite -(size_map (@snd _ _)) index_mem z_in_D.
    set x := nth _ _ _; rewrite (negbTE (rD x _)) //.
    by rewrite /x mem_nth // -(size_map (@snd _ _)) index_mem z_in_D.
  Qed.

  Lemma coeff_outdom (D : {freeg K}) k:
    k \notin dom D -> coeff k D = 0.
  Proof. by rewrite mem_dom inE negbK => /eqP ->. Qed.
End FreegTheory.

Notation "[ 'freeg' S ]" := (Freeg S).

Notation "<< z *g p >>" := [freeg [:: (z, p)]].
Notation "<< p >>"      := [freeg [:: (1%Z, p)]].

(* -------------------------------------------------------------------- *)
Module FreegZmodType.
  Section Defs.
    Variable K : choiceType.

    Local Notation zero := [freeg [::]].

    Lemma reprfg0: repr zero = Prefreeg [::] :> (prefreeg K).
    Proof.
      rewrite !piE; apply/eqP; rewrite eqE /=; apply/eqP.
      by apply: perm_eq_small => //=; apply: perm_eq_fgrepr.
    Qed.

    Definition fgadd_r (D1 D2 : prefreeg K) := Prefreeg (D1 ++ D2).

    Definition fgadd := lift_op2 {freeg K} fgadd_r.

    Lemma pi_fgadd: {morph \pi : D1 D2 / fgadd_r D1 D2 >-> fgadd D1 D2}.
    Proof.
      case=> [D1 redD1] [D2 redD2]; unlock fgadd; rewrite !piE.
      apply/eqmodP=> /=; apply/freegequivP=> k /=.
      by rewrite !precoeff_reduce !precoeff_cat !precoeff_repr.
    Qed.

    Canonical pi_fgadd_morph := PiMorph2 pi_fgadd.

    Definition fgopp_r (D : prefreeg K) := Prefreeg (prefreeg_opp D).

    Definition fgopp := lift_op1 {freeg K} fgopp_r.

    Lemma pi_fgopp: {morph \pi : D / fgopp_r D >-> fgopp D}.
    Proof.
      case=> [D redD]; unlock fgopp; rewrite !piE.
      apply/eqmodP=> /=; apply/freegequivP=> k /=.
      by rewrite !precoeff_reduce !precoeff_opp !precoeff_repr.
    Qed.

    Canonical pi_fgopp_morph := PiMorph1 pi_fgopp.

    Lemma addmA: associative fgadd.
    Proof.
      elim/quotW=> [D1]; elim/quotW=> [D2]; elim/quotW=> [D3].
      unlock fgadd; rewrite !piE /fgadd_r /=.
      apply/eqmodP; apply/freegequivP=> k /=.
      by rewrite !(precoeff_reduce, precoeff_cat, precoeff_repr) addrA.
    Qed.

    Lemma addmC: commutative fgadd.
    Proof.
      elim/quotW=> [D1]; elim/quotW=> [D2].
      unlock fgadd; rewrite !piE /fgadd_r /=.
      apply/eqmodP; apply/freegequivP=> k /=.
      by rewrite !(precoeff_reduce, precoeff_cat, precoeff_repr) addrC.
    Qed.

    Lemma addm0: left_id zero fgadd.
    Proof.
      elim/quotW=> [[D redD]]; unlock fgadd; rewrite !(reprfg0, piE).
      rewrite /fgadd_r /=; apply/eqmodP=> /=; apply/freegequivP=> /= k.
      by rewrite precoeff_reduce precoeff_repr.
    Qed.

    Lemma addmN: left_inverse zero fgopp fgadd.
    Proof.
      elim/quotW=> [[D redD]]; unlock fgadd fgopp; rewrite !(reprfg0, piE).
      rewrite /fgadd_r /fgopp_r; apply/eqmodP=> /=; apply/freegequivP=> /= k.
      set R := (precoeff_reduce, precoeff_repr,
                precoeff_cat   , precoeff_opp ,
                precoeff_repr  , precoeff_nil ).
      by rewrite !R /= addrC subrr.
    Qed.

    Definition freeg_zmodMixin := ZmodMixin addmA addmC addm0 addmN.
    Canonical  freeg_zmodType  := ZmodType {freeg K} freeg_zmodMixin.
  End Defs.

  Module Exports.
    Canonical pi_fgadd_morph.
    Canonical pi_fgopp_morph.
    Canonical  freeg_zmodType.
  End Exports.
End FreegZmodType.

Import FreegZmodType.
Export FreegZmodType.Exports.

(* -------------------------------------------------------------------- *)
Section FreegZmodTypeTheory.
  Variable K : choiceType.

  Implicit Types x y z : K.
  Implicit Types k : int.

  (* -------------------------------------------------------------------- *)
  Section Lift.
    Variable G : zmodType.
    Variable f : K -> G.

    Lemma lift_is_additive: additive (fglift f).
    Proof.
      elim/quotW=> [[D1 /= H1]]; elim/quotW=> [[D2 /= H2]].
      unlock fglift; rewrite !piE [_ + _]piE /lift /=.
      rewrite !prelift_repr /fgadd_r /fgopp_r /=.
      by rewrite !(prelift_reduce, prelift_cat, prelift_opp).
    Qed.
  End Lift.

  (* -------------------------------------------------------------------- *)
  Lemma coeff_is_additive x: additive (coeff x).
  Proof. by apply: lift_is_additive. Qed.

  Canonical coeff_additive x := Additive (coeff_is_additive x).

  Lemma coeff0   z   : coeff z 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma coeffN   z   : {morph coeff z: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma coeffD   z   : {morph coeff z: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma coeffB   z   : {morph coeff z: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma coeffMn  z n : {morph coeff z: x / x *+ n} . Proof. exact: raddfMn. Qed.
  Lemma coeffMNn z n : {morph coeff z: x / x *- n} . Proof. exact: raddfMNn. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dom0: dom 0 = [::] :> seq K.
  Proof.
    apply: perm_eq_small=> //; apply: uniq_perm_eq=> //.
      by apply: uniq_dom.
    by move=> z; rewrite mem_dom !(inE, in_nil) coeff0 eqxx.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dom_eq0 (D : {freeg K}): (dom D == [::]) = (D == 0).
  Proof.
    apply/eqP/eqP; last by move=> ->; rewrite dom0.
    move=> z_domD; apply/eqP/freeg_eqP=> z; rewrite coeff0 coeff_outdom //.
    by rewrite z_domD in_nil.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domU (c : int) (z : K): c != 0 -> dom << c *g z >> = [:: z].
  Proof.
    move=> nz_c; apply: perm_eq_small=> //; apply: uniq_perm_eq=> //.
      by apply: uniq_dom.
    move=> x; rewrite mem_dom !(inE, in_nil) coeffU [z == _]eq_sym.
    by rewrite mulf_eq0 (negbTE nz_c) /= eqz_nat eqb0 negbK.
  Qed.

  (* -------------------------------------------------------------------*)
  Lemma domU1 (z : K): dom << z >> = [:: z].
  Proof. by rewrite domU ?oner_eq0. Qed.

  (* -------------------------------------------------------------------*)
  Lemma domN (D : {freeg K}): dom (-D) =i dom D.
  Proof. by move=> z; rewrite !mem_dom !inE coeffN oppr_eq0. Qed.

  Lemma domN_perm_eq (D : {freeg K}): perm_eq (dom (-D)) (dom D).
  Proof.
    by apply: uniq_perm_eq; rewrite ?uniq_dom //; apply: domN.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domD_perm_eq (D1 D2 : {freeg K}):
       [predI (dom D1) & (dom D2)] =1 pred0
    -> perm_eq (dom (D1 + D2)) (dom D1 ++ dom D2).
  Proof.
    move=> D12_nI; have inD1E p: p \in dom D1 -> p \notin dom D2.
      move=> p_in_D1; move/(_ p): D12_nI; rewrite !inE p_in_D1.
      by rewrite andTb => /= ->.
    have inD2E p: p \in dom D2 -> p \notin dom D1.
      move=> p_in_D2; move/(_ p): D12_nI; rewrite !inE p_in_D2.
      by rewrite andbT => /= ->.
    apply: uniq_perm_eq; rewrite ?uniq_dom //.
      rewrite cat_uniq ?uniq_dom //= andbT; apply/hasP.
      case=> p p_in_D2; move/(_ p): D12_nI => /=.
      by rewrite p_in_D2 andbT=> ->.
    move=> p; rewrite mem_cat !mem_dom !inE coeffD.
    move/(_ p): D12_nI; rewrite /= !mem_dom !inE.
    case nz_D1p: (_ != 0) => /=.
      by move/negbT; rewrite negbK=> /eqP->; rewrite addr0.
    move=> _; move/negbT: nz_D1p; rewrite negbK.
    by move/eqP->; rewrite add0r.
  Qed.

  Lemma domD (D1 D2 : {freeg K}) x:
       [predI (dom D1) & (dom D2)] =1 pred0
    -> (x \in dom (D1 + D2)) = (x \in dom D1) || (x \in dom D2).
  Proof. by move/domD_perm_eq/perm_eq_mem/(_ x); rewrite mem_cat. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domD_subset (D1 D2 : {freeg K}):
    {subset dom (D1 + D2) <= (dom D1) ++ (dom D2)}.
  Proof.
    move=> z; rewrite mem_cat !mem_dom !inE coeffD.
    have nz_sum (x1 x2 : int): x1 + x2 != 0 -> (x1 != 0) || (x2 != 0).
      by have [->|->] := eqVneq x1 0; first by rewrite add0r eqxx.
    by move/nz_sum; case/orP=> ->; rewrite ?orbT.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma dom_sum_subset (I : Type) (r : seq I) (F : I -> {freeg K}) (P : pred I):
    {subset dom (\sum_(i <- r | P i) F i) <= flatten [seq dom (F i) | i <- r & P i]}.
  Proof.
    move=> p; elim: r => [|r rs IH]; first by rewrite big_nil dom0.
    rewrite big_cons; case Pr: (P r); last by move/IH=> /=; rewrite Pr.
    move/domD_subset; rewrite mem_cat; case/orP=> /=; rewrite Pr.
    + by rewrite map_cons /= mem_cat=> ->.
    + by move/IH; rewrite map_cons /= mem_cat=> ->; rewrite orbT.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma domB (D1 D2 : {freeg K}):
    {subset dom (D1 - D2) <= (dom D1) ++ (dom D2)}.
  Proof. by move=> z; move/domD_subset; rewrite !mem_cat domN. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma freegUD k1 k2 x:
    << k1 *g x >> + << k2 *g x >> = << (k1 + k2) *g x >>.
  Proof.
    by apply/eqP/freeg_eqP=> z; rewrite coeffD !coeffU -mulrDl.
  Qed.

  Lemma freegUN k x: - << k *g x >> = << -k *g x >>.
  Proof.
    by apply/eqP/freeg_eqP=> z; rewrite coeffN !coeffU mulNr.
  Qed.

  Lemma freegUB k1 k2 x:
    << k1 *g x >> - << k2 *g x >> = << (k1-k2) *g x >>.
  Proof. by rewrite freegUN freegUD. Qed.

  Lemma freegU0 x: << 0 *g x >> = 0 :> {freeg K}.
  Proof.
    by apply/eqP/freeg_eqP=> y; rewrite coeffU coeff0 mul0r.
  Qed.

  Lemma freegU_eq0 (k : int) (x : K):
    (<< k *g x >> == 0) = (k == 0).
  Proof.
    apply/eqP/eqP; last by move=> ->; rewrite freegU0.
    by move/(congr1 (coeff x)); rewrite coeff0 coeffU eqxx mulr1.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma freeg_muln k n (S : K):
    << k *g S >> *+ n = << (n%:Z * k) *g S >>.
  Proof.
    elim: n => [|n IH].
    + by rewrite mulr0n mul0r freegU0.
    + by rewrite mulrS IH freegUD intS mulrDl mul1r.
  Qed.

  Lemma freegU_muln n (S : K):
    << S >> *+ n = << n%:Z *g S >>.
  Proof. by rewrite freeg_muln mulr1. Qed.

  Lemma freeg_mulz (k m : int) (S : K):
    << k *g S >> *~ m = << (m*k) *g S >>.
  Proof.
    case: m=> [n|n].
    + by rewrite -pmulrn freeg_muln.
    + by rewrite NegzE -nmulrn freeg_muln mulNr freegUN.
  Qed.

  Lemma freegU_mulz (k : int) (S : K):
    << S >> *~ k = << k *g S >>.
  Proof. by rewrite freeg_mulz mulr1. Qed.

  (* -------------------------------------------------------------------- *)
  Definition deg (D : {freeg K}) : int := fglift (fun _ => 1%:Z) D.

  Lemma degU k z: deg << k *g z >> = k.
  Proof. by rewrite /deg liftU intz. Qed.

  Definition predeg (D : seq (int * K)) :=
    \sum_(kx <- D) kx.1.

  Lemma deg_is_additive: additive deg.
  Proof. by apply: lift_is_additive. Qed.

  Canonical deg_additive := Additive deg_is_additive.

  Lemma deg0     : deg 0 = 0               . Proof. exact: raddf0. Qed.
  Lemma degN     : {morph deg: x / - x}    . Proof. exact: raddfN. Qed.
  Lemma degD     : {morph deg: x y / x + y}. Proof. exact: raddfD. Qed.
  Lemma degB     : {morph deg: x y / x - y}. Proof. exact: raddfB. Qed.
  Lemma degMn  n : {morph deg: x / x *+ n} . Proof. exact: raddfMn. Qed.
  Lemma degMNn n : {morph deg: x / x *- n} . Proof. exact: raddfMNn. Qed.

  Lemma predegE: predeg =1 prelift (fun _ => 1%:Z).
  Proof.
    move=> D; rewrite /predeg /prelift; apply: eq_bigr.
    by move=> i _; rewrite intz.
  Qed.

  Lemma predeg_nil: predeg [::] = 0.
  Proof. by rewrite /predeg big_nil. Qed.

  Lemma predeg_cons D k x:
    predeg ((k, x) :: D) = k + (predeg D).
  Proof. by rewrite /predeg big_cons. Qed.

  Lemma predeg_cat D1 D2:
    predeg (D1 ++ D2) = (predeg D1) + (predeg D2).
  Proof. by rewrite !predegE prelift_cat. Qed.

  Lemma predeg_opp D: predeg (prefreeg_opp D) = -(predeg D).
  Proof. by rewrite !predegE prelift_opp. Qed.

  Lemma predeg_perm_eq D1 D2: perm_eq D1 D2 -> predeg D1 = predeg D2.
  Proof. by rewrite !predegE => /prelift_perm_eq. Qed.

  Lemma predeg_repr D: predeg (repr (\pi_{freeg K} D)) = predeg D.
  Proof. by rewrite !predegE prelift_repr. Qed.

  Lemma predeg_reduce D: predeg (reduce D) = predeg D.
  Proof. by rewrite !predegE prelift_reduce. Qed.

  (* -------------------------------------------------------------------- *)
  Lemma freeg_nil: [freeg [::]] = 0 :> {freeg K}.
  Proof. by apply/eqP/freeg_eqP. Qed.

  Lemma freeg_cat (D1 D2 : seq (int * K)):
    [freeg D1 ++ D2] = [freeg D1] + [freeg D2].
  Proof.
    apply/eqP/freeg_eqP => k; rewrite coeffD.
    by rewrite !coeff_Freeg precoeff_cat.
  Qed.

  (* -------------------------------------------------------------------- *)
  Definition fgenum (D : {freeg K}) : seq (int * K) := repr D.

  Lemma Freeg_enum (D : {freeg K}): Freeg (fgenum D) = D.
  Proof.
    elim/quotW: D; case=> D rD /=; unlock Freeg; rewrite /Prefreeg.
    apply/eqmodP=> /=; rewrite /fgequiv /fgenum /=.
    apply: (perm_eq_trans (reduceK _)); last by apply: perm_eq_fgrepr.
    by apply: prefreeg_reduced.
  Qed.

  Lemma perm_eq_fgenum (D : seq (int * K)) (rD : reduced D):
    perm_eq (fgenum (\pi_{freeg K} (mkPrefreeg D rD))) D.
  Proof. by rewrite /fgenum; apply: perm_eq_fgrepr. Qed.

  (* -------------------------------------------------------------------- *)
  Lemma freeg_sumE (D : {freeg K}):
    \sum_(z <- dom D) << (coeff z D) *g z >> = D.
  Proof.
    apply/eqP/freeg_eqP=> x /=; rewrite raddf_sum /=.
    case x_in_dom: (x \in dom D); last rewrite coeff_outdom ?x_in_dom //.
    + rewrite (bigD1_seq x) ?uniq_dom //= big1 ?addr0.
      * by rewrite coeffU eqxx mulr1.
      * by move=> z ne_z_x; rewrite coeffU (negbTE ne_z_x) mulr0.
    + rewrite big_seq big1 // => z z_notin_dom; rewrite coeffU.
      apply/eqP; rewrite mulf_eq0; apply/orP; right.
      rewrite eqz_nat eqb0; apply/eqP=> /(congr1 (fun x => x \in dom D)).
      by rewrite x_in_dom z_notin_dom.
  Qed.
End FreegZmodTypeTheory.

(* -------------------------------------------------------------------- *)
Reserved Notation "D1 <=g D2" (at level 50, no associativity).

Section FreegCmp.
  Variable K : choiceType.

  Definition fgle (D1 D2 : {freeg K}) :=
    all [pred z | coeff z D1 <= coeff z D2] (dom D1 ++ dom D2).

  Local Notation "D1 <=g D2" := (fgle D1 D2).

  Lemma fgleP D1 D2:
    reflect (forall z, coeff z D1 <= coeff z D2) (D1 <=g D2).
  Proof.
    apply: (iffP allP); last by move=> H z _; apply: H.
    move=> lec z; case z_in_dom: (z \in (dom D1 ++ dom D2)).
      by apply: lec.
    move: z_in_dom; rewrite mem_cat; case/norP=> zD1 zD2.
    by rewrite !coeff_outdom // lerr.
  Qed.

  Lemma fgposP D:
    reflect (forall z, 0 <= coeff z D) (0 <=g D).
  Proof.
    apply: (iffP idP).
    + by move=> posD z; move/fgleP/(_ z): posD; rewrite coeff0.
    + by move=> posD; apply/fgleP=> z; rewrite coeff0.
  Qed.

  Lemma fgledd D: D <=g D.
  Proof. by apply/fgleP=> z; rewrite lerr. Qed.

  Lemma fgle_trans: transitive fgle.
  Proof.
    move=> D2 D1 D3 le12 le23; apply/fgleP=> z.
    by rewrite (ler_trans (y := coeff z D2)) //; apply/fgleP.
  Qed.
End FreegCmp.

Local Notation "D1 <=g D2" := (fgle D1 D2).

(* -------------------------------------------------------------------- *)
Section FreegCmpDom.
  Variable K : choiceType.

  Lemma dompDl (D1 D2 : {freeg K}):
    0 <=g D1 -> 0 <=g D2 -> dom (D1 + D2) =i (dom D1) ++ (dom D2).
  Proof.
    move=> pos_D1 pos_D2 z; rewrite mem_cat !mem_dom !inE coeffD.
    by rewrite paddr_eq0; first 1 [rewrite negb_and] || apply/fgposP.
  Qed.
End FreegCmpDom.

(* -------------------------------------------------------------------- *)
Section FreegMap.
  Variable K : choiceType.
  Variable P : pred K.
  Variable f : int -> int.

  Implicit Types D : {freeg K}.

  Definition fgmap D :=
    \sum_(z <- dom D | P z) << f (coeff z D) *g z >>.

  Lemma fgmap_coeffE (D : {freeg K}) z:
    z \in dom D -> coeff z (fgmap D) = (f (coeff z D)) * (P z).
  Proof.
    move=> zD; rewrite /fgmap raddf_sum /= -big_filter; case Pz: (P z).
    + rewrite (bigD1_seq z) ?(filter_uniq, uniq_dom) //=; last first.
        by rewrite mem_filter Pz.
      rewrite coeffU eqxx mulr1 big1 ?addr0 //.
      by move=> z' ne_z'z; rewrite coeffU (negbTE ne_z'z) mulr0.
    + rewrite big_seq big1 ?mulr0 //.
      move=> z' z'PD; rewrite coeffU; have/negbTE->: z' != z.
        apply/eqP=> /(congr1 (fun x => x \in filter P (dom D))).
        by rewrite z'PD mem_filter Pz.
      by rewrite mulr0.
  Qed.

  Lemma fgmap_dom D: {subset dom (fgmap D) <= filter P (dom D)}.
  Proof.
    move=> z; rewrite mem_dom inE mem_filter andbC.
    case zD: (z \in (dom D)) => /=.
    + rewrite fgmap_coeffE // mulf_eq0 negb_or => /andP [_].
      by rewrite eqz_nat eqb0 negbK.
    + rewrite /fgmap raddf_sum /= big_seq_cond big1 //.
      move=> z' /andP [z'D _]; rewrite coeffU.
      have/negbTE->: z' != z; last by rewrite mulr0.
      apply/eqP=> /(congr1 (fun x => x \in dom D)).
      by rewrite  zD z'D.
  Qed.

  Lemma fgmap_f0_coeffE (D : {freeg K}) z:
    f 0 = 0 -> coeff z (fgmap D) = (f (coeff z D)) * (P z).
  Proof.
    move=> z_f0; case zD: (z \in dom D).
      by rewrite fgmap_coeffE.
    rewrite !coeff_outdom ?z_f0 ?zD //.
    by apply/negP=> /fgmap_dom; rewrite mem_filter zD andbF.
  Qed.
End FreegMap.

(* -------------------------------------------------------------------- *)
Section FreegNorm.
  Variable K : choiceType.

  Definition fgnorm (D : {freeg K}) := fgmap xpredT Num.norm D.

  Lemma fgnormE D: fgnorm D = \sum_(z <- dom D) << `|coeff z D| *g z >>.
  Proof. by []. Qed.

  Lemma coeff_fgnormE (D : {freeg K}) z: coeff z (fgnorm D) = `|coeff z D|.
  Proof. by rewrite fgmap_f0_coeffE ?mulr1. Qed.
End FreegNorm.

(* -------------------------------------------------------------------- *)
Section FreegPosDecomp.
  Variable K : choiceType.

  Definition fgpos (D : {freeg K}) :=
    fgmap [pred z | coeff z D >= 0] Num.norm D.

  Definition fgneg (D : {freeg K}) :=
    fgmap [pred z | coeff z D <= 0] Num.norm D.

  Lemma fgposE D:
    fgpos D = \sum_(z <- dom D | coeff z D >= 0) << `|coeff z D| *g z >>.
  Proof. by []. Qed.

  Lemma fgnegE D:
    fgneg D = \sum_(z <- dom D | coeff z D <= 0) << `|coeff z D| *g z >>.
  Proof. by []. Qed.

  Lemma fgposN D: fgpos (-D) = fgneg D.
  Proof.
    apply/eqP/freeg_eqP=> z; rewrite !fgmap_f0_coeffE // !inE /=.
    by rewrite !coeffN oppr_ge0 normrN.
  Qed.

  Lemma fgpos_le0 D: 0 <=g fgpos D.
  Proof. by apply/fgleP=> z; rewrite coeff0 fgmap_f0_coeffE. Qed.

  Lemma fgneg_le0 D: 0 <=g fgneg D.
  Proof. by rewrite -fgposN fgpos_le0. Qed.

  Lemma coeff_fgposE D k: coeff k (fgpos D) = Num.max 0 (coeff k D).
  Proof.
    rewrite fgmap_f0_coeffE // inE; rewrite /Num.max.
    rewrite lerNgt ler_eqVlt; case: eqP=> [->//|_] /=.
    case: ltrP; rewrite ?(mulr0, mulr1) // => pos_zD.
    by rewrite ger0_norm.
  Qed.

  Lemma coeff_fgnegE D k: coeff k (fgneg D) = - (Num.min 0 (coeff k D)).
  Proof.
    by rewrite -fgposN coeff_fgposE coeffN -{1}[0]oppr0 -oppr_min.
  Qed.

  Lemma fgpos_dom D: {subset dom (fgpos D) <= dom D}.
  Proof.
    by move=> x /fgmap_dom; rewrite mem_filter => /andP [_].
  Qed.

  Lemma fgneg_dom D: {subset dom (fgneg D) <= dom D}.
  Proof.
    by move=> k; rewrite -fgposN => /fgpos_dom; rewrite domN.
  Qed.

  Lemma fg_decomp (D : {freeg K}): D = (fgpos D) - (fgneg D).
  Proof.
    apply/eqP/freeg_eqP=> k; rewrite coeffB.
    by rewrite coeff_fgposE coeff_fgnegE opprK addr_max_min add0r.
  Qed.

  Lemma fgnorm_decomp (D : {freeg K}): fgnorm D = (fgpos D) + (fgneg D).
  Proof.
    apply/eqP/freeg_eqP=> k; rewrite coeffD coeff_fgnormE.
    rewrite coeff_fgposE coeff_fgnegE /Num.max /Num.min.
    rewrite lerNgt ler_eqVlt; case: (0 =P _)=> [<-//|_] /=.
    case: ltrP=> /=; rewrite ?(subr0, sub0r) => lt.
    + by rewrite gtr0_norm.
    + by rewrite ler0_norm.
  Qed.
End FreegPosDecomp.

(* -------------------------------------------------------------------- *)
Section PosFreegDeg.
  Variable K : choiceType.

  Lemma fgpos_eq0P (D : {freeg K}): 0 <=g D -> deg D = 0 -> D = 0.
  Proof.
    move=> posD; rewrite -{1}[D]freeg_sumE raddf_sum /=.
    rewrite (eq_bigr (fun z => coeff z D)); last first.
      by move=> i _; rewrite degU.
    move/eqP; rewrite psumr_eq0; last by move=> i _; apply/fgposP.
    move/allP=> zD; apply/eqP; apply/freeg_eqP=> z; rewrite coeff0.
    case z_in_D: (z \in dom D); last first.
      by rewrite coeff_outdom // z_in_D.
    by apply/eqP/zD.
  Qed.

  Lemma fgneg_eq0P (D : {freeg K}): D <=g 0 -> deg D = 0 -> D = 0.
  Proof.
    move=> negD deg_eq0; apply/eqP; rewrite -oppr_eq0; apply/eqP.
    apply/fgpos_eq0P; last by apply/eqP; rewrite degN oppr_eq0 deg_eq0.
    apply/fgposP=> z; rewrite coeffN oppr_ge0.
    by move/fgleP: negD => /(_ z); rewrite coeff0.
  Qed.

  Lemma deg1pos (D : {freeg K}):
    0 <=g D -> deg D = 1 -> exists x, D = << x >>.
  Proof.
    move=> D_ge0 degD_eq1; have: D != 0.
      by case: (D =P 0) degD_eq1 => [->|//]; rewrite deg0.
    rewrite -dom_eq0; case DE: (dom D) => [//|p ps] _.
    rewrite -[D]addr0 -(subrr <<p>>) addrA addrAC.
    have: coeff p D != 0.
      by move: (mem_dom D p); rewrite DE in_cons eqxx inE /=.
    rewrite neqr_lt ltrNge; have/fgposP/(_ p) := D_ge0 => ->/=.
    move=> coeffpD_gt0; have: 0 <=g (D - <<p>>).
      apply/fgposP=> q; rewrite coeffB coeffU mul1r.
      case: (p =P q) =>[<-/=|]; last first.
        by move=> _; rewrite subr0; apply/fgposP.
      by rewrite subr_ge0.
    move/fgpos_eq0P=> ->; first by rewrite add0r; exists p.
    by rewrite degB degU degD_eq1 subrr.
  Qed.

  Lemma deg1neg (D : {freeg K}):
    D <=g 0 -> deg D = -1 -> exists x, D = - << x >>.
  Proof.
    move=> D_le0 degD_eqN1; case: (@deg1pos (-D)).
    + apply/fgleP=> p; rewrite coeffN coeff0 oppr_ge0.
      by move/fgleP/(_ p): D_le0; rewrite coeff0.
    + by rewrite degN degD_eqN1 opprK.
    + by move=> p /eqP; rewrite eqr_oppLR => /eqP->; exists p.
  Qed.
End PosFreegDeg.

(* -------------------------------------------------------------------- *)
Section FreegIndDom.
  Variable T : choiceType.

  Variable R : pred T.
  Variable P : {freeg T} -> Prop.

  Hypothesis H0:
    forall D, [predI dom D & [predC R]] =1 pred0 -> P D.

  Hypothesis HS:
    forall k x D, x \notin dom D -> k != 0 -> ~~ (R x) ->
      P D -> P (<< k *g x >> + D).

  Lemma freeg_ind_dom D: P D.
  Proof.
    rewrite -[D]freeg_sumE (bigID R) /=; set DR := \sum_(_ <- _ | _) _.
    have: [predI dom DR & [predC R]] =1 pred0.
      move=> p /=; rewrite !inE; apply/negP=> /andP [].
      rewrite /DR => /dom_sum_subset /flattenP.
      case=> [ps /mapP [q]]; rewrite mem_filter => /andP [].
      move=> Rq q_in_D ->; rewrite domU ?mem_seq1; last first.
        by move: (mem_dom D q); rewrite inE => <-.
      by move/eqP=> ->; move: Rq; rewrite /in_mem /= => ->.
    move: DR => DR domDR; rewrite addrC -big_filter.
    set ps := [seq _ <- _ | _]; move: (perm_eq_refl ps).
    rewrite {1}/ps; move: ps (D) => {D}; elim => [|p ps IH] D.
    + by move=> _; rewrite big_nil add0r; apply: H0.
    + move=> DE; move/(_ p): (perm_eq_mem DE); rewrite !inE eqxx /=.
      have /=: uniq (p :: ps).
        by move/perm_eq_uniq: DE; rewrite filter_uniq // uniq_dom.
      case/andP=> p_notin_ps uniq_ps; rewrite mem_filter=> /andP [NRp p_in_D].
      rewrite big_cons -addrA; apply HS => //; first 1 last.
      * by move: p_in_D; rewrite mem_dom.
      * pose D' := D - << coeff p D *g p >>.
        have coeffD' q: coeff q D' = coeff q D * (p != q).
          rewrite {}/D' coeffB coeffU; case: (p =P q).
          - by move=> ->; rewrite !(mulr1, mulr0) subrr.
          - by move/eqP=> ne_pq; rewrite !(mulr1, mulr0) subr0.
        have: perm_eq (dom D) (p :: dom D').
          apply: uniq_perm_eq; rewrite /= ?uniq_dom ?andbT //.
          - by rewrite mem_dom inE coeffD' eqxx mulr0.
          move=> q; rewrite in_cons !mem_dom !inE coeffD' [q == _]eq_sym.
          case: (p =P q); rewrite !(mulr0, mulr1) //=.
          by move=> <-; move: p_in_D; rewrite mem_dom.
        move/perm_eq_filter=> /(_ [pred q | ~~ (R q)]) /=.
        rewrite NRp; rewrite perm_eq_sym; move/(perm_eq_trans)=> /(_ _ DE).
        rewrite perm_cons => domD'; rewrite big_seq.
        rewrite (eq_bigr (fun q => << coeff q D' *g q >>)); last first.
          move=> q q_in_ps; rewrite /D' coeffB coeffU; case: (p =P q).
          - by move=> eq_pq; move: p_notin_ps; rewrite eq_pq q_in_ps.
          - by move=> _; rewrite mulr0 subr0.
        by rewrite -big_seq; apply IH.
      * apply/negP=> /domD_subset; rewrite mem_cat; case/orP; last first.
          by move=> p_in_DR; move/(_ p): domDR; rewrite !inE NRp p_in_DR.
        move/dom_sum_subset; rewrite filter_predT => /flattenP [qs].
        move/mapP => [q q_in_ps ->]; rewrite domU; last first.
          move/perm_eq_mem/(_ q): DE; rewrite !inE q_in_ps orbT.
          by rewrite mem_filter => /andP [_]; rewrite mem_dom.
        rewrite mem_seq1 => /eqP pq_eq; move: p_notin_ps.
        by rewrite pq_eq q_in_ps.
  Qed.
End FreegIndDom.

Section FreegIndDom0.
  Variable T : choiceType.
  Variable P : {freeg T} -> Prop.

  Hypothesis H0: P 0.
  Hypothesis HS:
    forall k x D, x \notin dom D -> k != 0 ->
      P D -> P (<< k *g x >> + D).

  Lemma freeg_ind_dom0 D: P D.
  Proof.
    apply: (@freeg_ind_dom _ xpred0) => {D} [D|k x D].
    + move=> domD; have ->: D = 0; last exact: H0.
      case: (D =P 0) => [//|/eqP]; rewrite -dom_eq0.
      case: (dom D) domD => [//|p ps] /(_ p).
      by rewrite !inE eqxx andbT /= /in_mem.
    + by move=> ?? _ ?; apply: HS.
  Qed.
End FreegIndDom0.
