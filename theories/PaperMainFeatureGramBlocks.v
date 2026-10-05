(* Exact Gram blocks of the quadratic feature map (G14, checkpoint A;
   manuscript lines 504-517, eq:Q-def and eq:DV-def).
   For a sample x of N points of R^d, with the raw features
   x_i x_i^T - I:
   - the full Gram (Q Q^* )_ij = <x_i x_i^T - I, x_j x_j^T - I>
     = (x_i^T x_j)^2 - |x_i|^2 - |x_j|^2 + d (paper_main_feature_gram_entry);
   - the diagonal block D_ia = x_ia^2 - 1, an N x d matrix;
   - the square-free block V, an N x (d * d) matrix: row i is mxvec of the
     d x d matrix with entry sqrt 2 x_ia x_ib for a < b and 0 otherwise.
     The ordered-pair guard a < b replaces a new pair-index type.
   Then Q Q^* = D D^T + V V^T, so V V^T <= Q Q^* in Loewner order.
   Q Q^* = d times the Gram of the normalized head features (d > 0), and
   (V V^T)_ii = |x_i|^4 - sum_a x_ia^4. N = 0 and d = 0 are allowed. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadFeature PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadCoefficients PaperMainGeometrySeparation PaperMainSymmetricBilinear.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Pairings through mxvec. *)
Lemma pmfg_mxvec_dot d (A B : 'M[R]_d) :
  \sum_(k < d * d) mxvec A 0 k * mxvec B 0 k = paper_main_pairing A B.
Proof.
rewrite (reindex _ (curry_mxvec_bij _ _)) /= /paper_main_pairing pair_bigA /=.
by apply: eq_bigr => [[a b]] _ /=; rewrite !mxvecE.
Qed.

(* 2. A symmetric double sum is its diagonal plus twice its upper part. *)
Lemma pmfg_sum_sym d (F : 'I_d -> 'I_d -> R) :
  (forall a b, F a b = F b a) ->
  \sum_(a < d) \sum_(b < d) F a b =
  \sum_(a < d) F a a + 2 * \sum_(a < d) \sum_(b < d) (if (a < b)%N then F a b else 0).
Proof.
move=> HF.
have E : forall a b, F a b = (if (a < b)%N then F a b else 0) +
    ((if a == b then F a b else 0) + (if (b < a)%N then F a b else 0)).
  move=> a b; case: (ltngtP a b) => [Hab|Hab|Hab].
  - have Hne : (a == b) = false by apply/negbTE; rewrite -val_eqE /= neq_ltn Hab.
    by rewrite Hne !addr0.
  - have Hne : (a == b) = false by apply/negbTE; rewrite -val_eqE /= neq_ltn Hab orbT.
    by rewrite Hne !add0r.
  - have Heq : a = b by exact: val_inj.
    by rewrite Heq eqxx add0r addr0.
have Hsplit : \sum_(a < d) \sum_(b < d) F a b =
    \sum_(a < d) \sum_(b < d) (if (a < b)%N then F a b else 0) +
    (\sum_(a < d) \sum_(b < d) (if a == b then F a b else 0) +
     \sum_(a < d) \sum_(b < d) (if (b < a)%N then F a b else 0)).
  rewrite -!big_split /=; apply: eq_bigr => a _.
  rewrite -!big_split /=; apply: eq_bigr => b _.
  exact: E.
have Hdiag : \sum_(a < d) \sum_(b < d) (if a == b then F a b else 0) = \sum_(a < d) F a a.
  apply: eq_bigr => a _; rewrite (bigD1 a) //= eqxx big1 ?addr0 //.
  by move=> b /negbTE Hb; rewrite eq_sym Hb.
have Hlow : \sum_(a < d) \sum_(b < d) (if (b < a)%N then F a b else 0) =
    \sum_(a < d) \sum_(b < d) (if (a < b)%N then F a b else 0).
  rewrite exchange_big; apply: eq_bigr => a _; apply: eq_bigr => b _.
  by rewrite HF.
rewrite Hsplit Hdiag Hlow; ring.
Qed.

(* 3. The full Gram and its two blocks. *)
Section Blocks.
Variables (N d : nat) (x : paper_main_sample N d).

Definition paper_main_raw_feature (i : nat) : 'M[R]_d :=
  paper_main_point x i *m (paper_main_point x i)^T - 1%:M.

Definition paper_main_feature_gram : 'M[R]_N :=
  \matrix_(i, j) paper_main_pairing (paper_main_raw_feature i) (paper_main_raw_feature j).

Definition paper_main_diag_block : 'M[R]_(N, d) :=
  \matrix_(i, a) (paper_main_point x i a 0 ^+ 2 - 1).

Definition paper_main_squarefree_row (i : nat) : 'M[R]_d :=
  \matrix_(a, b) (if (a < b)%N then
    Num.sqrt 2 * (paper_main_point x i a 0 * paper_main_point x i b 0) else 0).

Definition paper_main_squarefree_block : 'M[R]_(N, d * d) :=
  \matrix_(i, k) mxvec (paper_main_squarefree_row i) 0 k.

Lemma pmfg_raw_entry i (a b : 'I_d) :
  paper_main_raw_feature i a b =
  paper_main_point x i a 0 * paper_main_point x i b 0 - (a == b)%:R.
Proof. by rewrite /paper_main_raw_feature !mxE big_ord1 !mxE. Qed.

Lemma paper_main_squarefree_gram_pairing (i j : 'I_N) :
  (paper_main_squarefree_block *m paper_main_squarefree_block^T) i j =
  paper_main_pairing (paper_main_squarefree_row i) (paper_main_squarefree_row j).
Proof.
rewrite mxE -pmfg_mxvec_dot; apply: eq_bigr => k _.
by rewrite !mxE.
Qed.

Lemma paper_main_squarefree_gram_entry (i j : 'I_N) :
  (paper_main_squarefree_block *m paper_main_squarefree_block^T) i j =
  2 * \sum_(a < d) \sum_(b < d) (if (a < b)%N then
    paper_main_point x i a 0 * paper_main_point x i b 0 *
    (paper_main_point x j a 0 * paper_main_point x j b 0) else 0).
Proof.
rewrite paper_main_squarefree_gram_pairing /paper_main_pairing mulr_sumr.
apply: eq_bigr => a _; rewrite mulr_sumr; apply: eq_bigr => b _.
rewrite !mxE; case: ifP => _; last by rewrite mul0r mulr0.
have H2 : Num.sqrt 2 * Num.sqrt 2 = 2 :> R by rewrite -expr2 sqr_sqrtr // ler0n.
by rewrite mulrACA H2.
Qed.

Lemma paper_main_diag_gram_entry (i j : 'I_N) :
  (paper_main_diag_block *m paper_main_diag_block^T) i j =
  \sum_(a < d) (paper_main_point x i a 0 ^+ 2 - 1) * (paper_main_point x j a 0 ^+ 2 - 1).
Proof. by rewrite mxE; apply: eq_bigr => a _; rewrite !mxE. Qed.

Theorem paper_main_feature_gram_blocks :
  paper_main_feature_gram =
  paper_main_diag_block *m paper_main_diag_block^T +
  paper_main_squarefree_block *m paper_main_squarefree_block^T.
Proof.
apply/matrixP => i j.
rewrite [LHS]mxE [RHS]mxE paper_main_diag_gram_entry paper_main_squarefree_gram_entry.
rewrite /paper_main_pairing (pmfg_sum_sym _ (fun a b => paper_main_raw_feature i a b *
  paper_main_raw_feature j a b)); last first.
  congr (_ + 2 * _).
    by apply: eq_bigr => a _; rewrite !pmfg_raw_entry eqxx -!expr2.
  apply: eq_bigr => a _; apply: eq_bigr => b _.
  case: ifP => Hab //.
  have Hne : (a == b) = false by apply/negbTE; rewrite -val_eqE /= neq_ltn Hab.
  by rewrite !pmfg_raw_entry Hne subr0 subr0.
by move=> a b; rewrite !pmfg_raw_entry [b == a]eq_sym; ring.
Qed.

(* 4. The square-free Gram is below the full Gram. *)
Lemma pmfg_psd_gram m k (A : 'M[R]_(m, k)) : paper_main_psd (A *m A^T).
Proof.
split.
  by move=> i j; rewrite !mxE; apply: eq_bigr => a _; rewrite !mxE mulrC.
move=> v; rewrite paper_main_quadratic_formE.
have -> : v^T *m (A *m A^T) *m v = (A^T *m v)^T *m (A^T *m v).
  by rewrite trmx_mul trmxK !mulmxA.
exact: pmh_vec_sqr_ge0.
Qed.

Theorem paper_main_squarefree_gram_le :
  paper_main_loewner_le (paper_main_squarefree_block *m paper_main_squarefree_block^T)
    paper_main_feature_gram.
Proof.
rewrite /paper_main_loewner_le paper_main_feature_gram_blocks addrK.
exact: pmfg_psd_gram.
Qed.

Theorem paper_main_feature_gram_head :
  (0 < d)%N ->
  paper_main_feature_gram = d%:R *:
    \matrix_(i, j) paper_main_pairing (paper_main_head_feature x i) (paper_main_head_feature x j).
Proof.
move=> Hd; apply/matrixP => i j; rewrite !mxE /paper_main_head_feature.
rewrite pmh_pairingZl paper_main_pairing_scale -/(paper_main_raw_feature i)
  -/(paper_main_raw_feature j).
have Hs : (Num.sqrt (d%:R))^-1 * (Num.sqrt (d%:R))^-1 = (d%:R)^-1 :> R.
  by rewrite -invfM -expr2 sqr_sqrtr // ler0n.
rewrite [_^-1 * (_^-1 * _)]mulrA Hs mulrA mulfV ?mul1r //.
by rewrite pnatr_eq0 -lt0n.
Qed.

(* 6. The diagonal of the square-free Gram. *)
Theorem paper_main_squarefree_gram_diag (i : 'I_N) :
  (paper_main_squarefree_block *m paper_main_squarefree_block^T) i i =
  ((paper_main_point x i)^T *m paper_main_point x i) 0 0 ^+ 2 -
  \sum_(a < d) paper_main_point x i a 0 ^+ 4.
Proof.
rewrite paper_main_squarefree_gram_entry pmh_vec_dot.
set f := fun a : 'I_d => paper_main_point x i a 0.
have Hsq : (\sum_(a < d) paper_main_point x i a 0 * paper_main_point x i a 0) ^+ 2 =
    \sum_(a < d) \sum_(b < d) (f a ^+ 2 * f b ^+ 2).
  rewrite expr2 mulr_suml; apply: eq_bigr => a _; rewrite mulr_sumr; apply: eq_bigr => b _.
  by rewrite /f !expr2.
rewrite Hsq (pmfg_sum_sym _ (fun a b => f a ^+ 2 * f b ^+ 2) (fun a b => mulrC _ _)).
have H4 : \sum_(a < d) f a ^+ 2 * f a ^+ 2 = \sum_(a < d) paper_main_point x i a 0 ^+ 4.
  by apply: eq_bigr => a _; rewrite -exprD.
have Hup : \sum_(a < d) \sum_(b < d) (if (a < b)%N then
      paper_main_point x i a 0 * paper_main_point x i b 0 *
      (paper_main_point x i a 0 * paper_main_point x i b 0) else 0) =
    \sum_(a < d) \sum_(b < d) (if (a < b)%N then f a ^+ 2 * f b ^+ 2 else 0).
  apply: eq_bigr => a _; apply: eq_bigr => b _; case: ifP => // _.
  by rewrite /f mulrACA -!expr2.
rewrite H4 Hup; ring.
Qed.

End Blocks.
