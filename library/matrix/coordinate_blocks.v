From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From GaussianAnalysis.matrix Require Import euclidean real_spectral condition_cone.
From GaussianAnalysis.convex Require Import logdet_barrier.

(**md**************************************************************************)
(* # Coordinate partitions and transport of quadratic forms                   *)
(*                                                                            *)
(* Enumerating a finite coordinate set and its complement gives a bijection  *)
(* with a head block and a tail block, including empty blocks. For the support *)
(* of a vector, the tail is zero. Bijective coordinate selection preserves   *)
(* inner products, quadratic forms, positive definiteness and condition cones.*)
(* The construction uses MathComp's enum_val/enum_rank_in; the transport is   *)
(* finite-sum reindexing. These are general linear-algebra inputs for the      *)
(* sparse-shift argument of doc/shifted-gaussian.tex, with no law assumptions. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Section coordinate_partition.
Variable d : nat.
Variable S : {set 'I_d}.

Definition coordinate_partition_index (i : 'I_(#|S| + #|~: S|)) : 'I_d :=
  match split i with
  | inl j => @enum_val _ S j
  | inr j => @enum_val _ (~: S) j
  end.

Lemma coordinate_partition_headE (i : 'I_#|S|) :
  coordinate_partition_index (lshift #|~: S| i) = @enum_val _ S i.
Proof. by rewrite /coordinate_partition_index -[lshift _ i]/(unsplit (inl _ i))
  unsplitK. Qed.

Lemma coordinate_partition_tailE (j : 'I_#|~: S|) :
  coordinate_partition_index (@rshift #|S| #|~: S| j) = @enum_val _ (~: S) j.
Proof. by rewrite /coordinate_partition_index -[rshift _ j]/(unsplit (inr _ j))
  unsplitK. Qed.

Lemma coordinate_partition_head (i : 'I_#|S|) :
  coordinate_partition_index (lshift #|~: S| i) \in S.
Proof. by rewrite /coordinate_partition_index -[lshift _ i]/(unsplit (inl _ i))
  unsplitK; apply: enum_valP. Qed.

Lemma coordinate_partition_tail (j : 'I_#|~: S|) :
  coordinate_partition_index (@rshift #|S| #|~: S| j) \notin S.
Proof.
rewrite /coordinate_partition_index -[rshift _ j]/(unsplit (inr _ j)) unsplitK.
by have := @enum_valP _ (~: S) j; rewrite inE.
Qed.

Definition coordinate_partition_inverse (i : 'I_d) : 'I_(#|S| + #|~: S|).
Proof.
case: (boolP (i \in S)) => hi.
- exact: lshift #|~: S| (enum_rank_in hi i).
- apply: (@rshift #|S| #|~: S|).
  refine (@enum_rank_in _ i (~: S) _ i).
  by rewrite inE.
Defined.

Lemma coordinate_partition_inverseK :
  cancel coordinate_partition_inverse coordinate_partition_index.
Proof.
move=> i; rewrite /coordinate_partition_inverse; case (boolP (i \in S)) => hi.
- rewrite coordinate_partition_headE; exact: enum_rankK_in.
- rewrite coordinate_partition_tailE; apply: enum_rankK_in; by rewrite inE.
Qed.

Lemma coordinate_partition_inj : injective coordinate_partition_index.
Proof.
move=> i j; rewrite /coordinate_partition_index.
case Ei: (split i) => [a|a]; case Ej: (split j) => [b|b] hab.
- have ab : a = b := enum_val_inj hab.
  by rewrite -(splitK i) -(splitK j) Ei Ej ab.
- have ha := @enum_valP _ S a; have hb := @enum_valP _ (~: S) b.
  by rewrite -hab inE ha in hb.
- have ha := @enum_valP _ (~: S) a; have hb := @enum_valP _ S b.
  by rewrite hab inE hb in ha.
- have ab : a = b := enum_val_inj hab.
  by rewrite -(splitK i) -(splitK j) Ei Ej ab.
Qed.

Lemma coordinate_partition_indexK :
  cancel coordinate_partition_index coordinate_partition_inverse.
Proof. by move=> i; apply: coordinate_partition_inj;
  rewrite coordinate_partition_inverseK. Qed.

Lemma coordinate_partition_bij : bijective coordinate_partition_index.
Proof. exact: (Bijective coordinate_partition_indexK coordinate_partition_inverseK).
Qed.

Lemma coordinate_partition_card : (#|S| + #|~: S|)%N = d.
Proof. by rewrite cardsC card_ord. Qed.

Lemma coordinate_partition_complement : #|~: S| = (d - #|S|)%N.
Proof. by rewrite {1}(cardsCs (~: S)) finset.setCK card_ord. Qed.

End coordinate_partition.

Section coordinate_support.
Variable R : realType.
Variable d : nat.

Definition coordinate_support (m : 'cV[R]_d) : {set 'I_d} :=
  [set i | m i 0 != 0].

Lemma coordinate_support_tail (m : 'cV[R]_d)
    (j : 'I_#|~: coordinate_support m|) :
  m (@coordinate_partition_index d (coordinate_support m)
      (@rshift #|coordinate_support m| #|~: coordinate_support m| j)) 0 = 0.
Proof.
have := @coordinate_partition_tail d (coordinate_support m) j.
by rewrite /coordinate_support inE negbK => /eqP.
Qed.

Lemma coordinate_support_zero : coordinate_support (0 : 'cV[R]_d) = finset.set0.
Proof. by apply/setP => i; rewrite /coordinate_support !inE mxE eqxx. Qed.

Lemma coordinate_support_full (m : 'cV[R]_d) :
  (forall i, m i 0 != 0) -> coordinate_support m = finset.setT.
Proof. by move=> hm; apply/setP => i; rewrite /coordinate_support !inE hm. Qed.

Lemma coordinate_support_head (m : 'cV[R]_d)
    (i : 'I_#|coordinate_support m|) :
  m (@coordinate_partition_index d (coordinate_support m)
      (lshift #|~: coordinate_support m| i)) 0 != 0.
Proof.
have := @coordinate_partition_head d (coordinate_support m) i.
by rewrite /coordinate_support inE.
Qed.

(* A coordinate vector has exactly one head coordinate, wherever its
   nonzero entry lies in the original order. *)
Example coordinate_support_delta (i : 'I_d) :
  coordinate_support (delta_mx i 0 : 'cV[R]_d) = [set i].
Proof.
apply/setP => j; rewrite /coordinate_support !inE mxE eqxx andbT.
by case: (j == i); rewrite /= ?eqxx ?oner_eq0.
Qed.

End coordinate_support.


Section coordinate_transport.
Variable R : realType.

Lemma mxdot_rowsub_bij m e n (f : 'I_e -> 'I_m)
    (A B : 'M[R]_(m, n)) : bijective f ->
  mxdot (rowsub f A) (rowsub f B) = mxdot A B.
Proof.
move=> hf; rewrite /mxdot [RHS](reindex f (onW_bij _ hf)).
apply: eq_bigr => i _; apply: eq_bigr => j _; by rewrite !mxE.
Qed.

Lemma mxdot_colsub_bij m n e (f : 'I_e -> 'I_n)
    (A B : 'M[R]_(m, n)) : bijective f ->
  mxdot (colsub f A) (colsub f B) = mxdot A B.
Proof.
move=> hf; rewrite -[LHS]mxdot_trmx !trmx_mxsub.
by rewrite mxdot_rowsub_bij // mxdot_trmx.
Qed.

Lemma mxdot_mxsub_bij m n e k (f : 'I_e -> 'I_m) (g : 'I_k -> 'I_n)
    (A B : 'M[R]_(m, n)) : bijective f -> bijective g ->
  mxdot (mxsub f g A) (mxsub f g B) = mxdot A B.
Proof.
by move=> hf hg; rewrite [mxsub f g A]mxsubrc [mxsub f g B]mxsubrc
  mxdot_rowsub_bij // mxdot_colsub_bij.
Qed.

Lemma frobenius_mxsub_bij m n e k (f : 'I_e -> 'I_m) (g : 'I_k -> 'I_n)
    (A : 'M[R]_(m, n)) : bijective f -> bijective g ->
  frobenius (mxsub f g A) = frobenius A.
Proof. by move=> hf hg; rewrite /frobenius mxdot_mxsub_bij. Qed.

Lemma mulmx_coordinate_bij m n e p (f : 'I_e -> 'I_n)
    (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) : bijective f ->
  colsub f A *m rowsub f B = A *m B.
Proof.
move=> hf; apply/matrixP => i j.
rewrite !mxE [RHS](reindex f (onW_bij _ hf)).
by apply: eq_bigr => k _; rewrite !mxE.
Qed.

Lemma coordinate_selection_isometry d e (f : 'I_e -> 'I_d) :
  bijective f ->
  let U := rowsub f (1%:M : 'M[R]_d) in
  U *m U^T = 1%:M /\ U^T *m U = 1%:M.
Proof.
move=> hf /=; have [g hfg hgf] := hf.
have finj : injective f := can_inj hfg.
rewrite trmx_mxsub trmx1; split.
- rewrite -mxsub_mul mulmx1; apply/matrixP => i j.
  by rewrite !mxE (inj_eq finj).
- by rewrite mulmx_coordinate_bij // mulmx1.
Qed.

Lemma mxsub_coordinate_mul m n e p k (f : 'I_e -> 'I_n)
    (g : 'I_k -> 'I_m) (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  bijective f -> mxsub g f A *m rowsub f B = rowsub g (A *m B).
Proof.
by move=> hf; rewrite mxsubrc mul_rowsub_mx mulmx_coordinate_bij.
Qed.

Lemma coordinate_quadratic_form d e (f : 'I_e -> 'I_d)
    (A : 'M[R]_d) (x : 'cV[R]_d) : bijective f ->
  mxdot (rowsub f x) (mxsub f f A *m rowsub f x) = mxdot x (A *m x).
Proof.
by move=> hf; rewrite mxsub_coordinate_mul // mxdot_rowsub_bij.
Qed.

Lemma coordinate_row_quadratic_form d e (f : 'I_e -> 'I_d)
    (A : 'M[R]_d) (x : 'rV[R]_d) : bijective f ->
  mxdot (colsub f x) (colsub f x *m mxsub f f A) = mxdot x (x *m A).
Proof.
move=> hf; rewrite [mxsub f f A]mxsubcr mulmx_colsub mulmx_coordinate_bij //.
exact: mxdot_colsub_bij.
Qed.

Lemma coordinate_mxsubK d e (f : 'I_e -> 'I_d) (g : 'I_d -> 'I_e)
    (A : 'M[R]_d) : cancel g f -> mxsub g g (mxsub f f A) = A.
Proof. by move=> hgf; apply/matrixP => i j; rewrite !mxE !hgf. Qed.

Lemma coordinate_rowsubK d e n (f : 'I_e -> 'I_d) (g : 'I_d -> 'I_e)
    (A : 'M[R]_(d, n)) : cancel g f -> rowsub g (rowsub f A) = A.
Proof. by move=> hgf; apply/matrixP => i j; rewrite !mxE hgf. Qed.

Lemma coordinate_colsubK d e n (f : 'I_e -> 'I_d) (g : 'I_d -> 'I_e)
    (A : 'M[R]_(n, d)) : cancel g f -> colsub g (colsub f A) = A.
Proof. by move=> hgf; apply/matrixP => i j; rewrite !mxE hgf. Qed.

Lemma coordinate_symmetric d e (f : 'I_e -> 'I_d) (A : 'M[R]_d) :
  bijective f -> (mxsub f f A \is symmetricmx) = (A \is symmetricmx).
Proof.
move=> [g hfg hgf]; apply/symmetricmxP/symmetricmxP => hA.
- have h := congr1 (mxsub g g) hA.
  by rewrite trmx_mxsub !coordinate_mxsubK in h.
- by rewrite trmx_mxsub hA.
Qed.


Lemma coordinate_rowsub_eq0 d e n (f : 'I_e -> 'I_d)
    (A : 'M[R]_(d, n)) : bijective f ->
  (rowsub f A == 0) = (A == 0).
Proof. by move=> hf; rewrite -!mxdot_eq0 mxdot_rowsub_bij. Qed.

Lemma coordinate_colsub_eq0 d e n (f : 'I_e -> 'I_d)
    (A : 'M[R]_(n, d)) : bijective f ->
  (colsub f A == 0) = (A == 0).
Proof. by move=> hf; rewrite -!mxdot_eq0 mxdot_colsub_bij. Qed.

Lemma coordinate_posdef_forward d e (f : 'I_e -> 'I_d) (A : 'M[R]_d) :
  bijective f -> posdefmx A -> posdefmx (mxsub f f A).
Proof.
move=> hf [As Ap]; have [g hfg hgf] := hf.
have hg : bijective g := Bijective hgf hfg.
split; first by rewrite coordinate_symmetric.
move=> y y0.
have x0 : colsub g y != 0 by rewrite coordinate_colsub_eq0.
have h := Ap _ x0.
have hq := coordinate_row_quadratic_form A (colsub g y) hf.
by rewrite coordinate_colsubK // in hq; rewrite hq.
Qed.

Lemma coordinate_posdef d e (f : 'I_e -> 'I_d) (A : 'M[R]_d) :
  bijective f -> (posdefmx (mxsub f f A) <-> posdefmx A).
Proof.
move=> hf; split; last exact: coordinate_posdef_forward.
move=> hA; have [g hfg hgf] := hf.
have hg : bijective g := Bijective hgf hfg.
have := coordinate_posdef_forward hg hA.
by rewrite coordinate_mxsubK.
Qed.

Lemma coordinate_cond_cone_forward d e (f : 'I_e -> 'I_d)
    (C : R) (A : 'M[R]_d) :
  bijective f -> cond_cone C A -> cond_cone C (mxsub f f A).
Proof.
move=> hf [As [t t0 ht]]; have [g hfg hgf] := hf.
have hg : bijective g := Bijective hgf hfg.
split; first by rewrite coordinate_symmetric.
exists t => // y.
have h := ht (rowsub g y).
have hq := coordinate_quadratic_form A (rowsub g y) hf.
rewrite coordinate_rowsubK // in hq.
by rewrite mxdot_rowsub_bij // -hq in h.
Qed.

Lemma coordinate_cond_cone d e (f : 'I_e -> 'I_d)
    (C : R) (A : 'M[R]_d) :
  bijective f -> (cond_cone C (mxsub f f A) <-> cond_cone C A).
Proof.
move=> hf; split; last exact: coordinate_cond_cone_forward.
move=> hA; have [g hfg hgf] := hf.
have hg : bijective g := Bijective hgf hfg.
have := coordinate_cond_cone_forward hg hA.
by rewrite coordinate_mxsubK.
Qed.

Lemma coordinate_pullback_quadratic d e (f : 'I_e -> 'I_d)
    (g : 'I_d -> 'I_e) (Q : 'M[R]_e) (x : 'cV[R]_d) :
  cancel f g -> cancel g f ->
  mxdot x (mxsub g g Q *m x) =
    mxdot (rowsub f x) (Q *m rowsub f x).
Proof.
move=> hfg hgf; have hg : bijective g := Bijective hgf hfg.
have := coordinate_quadratic_form Q (rowsub f x) hg.
by rewrite coordinate_rowsubK.
Qed.

Lemma coordinate_pd_fit_pullback d e n (f : 'I_e -> 'I_d)
    (g : 'I_d -> 'I_e) (Q : 'M[R]_e) (x : 'I_n -> 'cV[R]_d) (a : R) :
  cancel f g -> cancel g f -> posdefmx Q ->
  (forall i, mxdot (rowsub f (x i)) (Q *m rowsub f (x i)) = a) ->
  posdefmx (mxsub g g Q) /\
    forall i, mxdot (x i) (mxsub g g Q *m x i) = a.
Proof.
move=> hfg hgf Qpd hfit; split.
- exact: coordinate_posdef_forward (Bijective hgf hfg) Qpd.
- by move=> i; rewrite (coordinate_pullback_quadratic Q (x i) hfg hgf).
Qed.

End coordinate_transport.
