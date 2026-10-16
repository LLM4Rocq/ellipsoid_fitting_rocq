(* Coordinate-block identities in the frozen sample layout. These are
   deterministic and use no independence of the two coordinate blocks. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral measurable_realfun.
From mathcomp Require Import ring_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import symmetrization.
From GaussianAnalysis.matrix Require Import euclidean.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality.Shifted Require Import Translations SparseRows GaussianRows GaussianTargets
  SparseTargets SparseInterpolation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).

Lemma sparse_sample_head_point n h p (x : paper_main_sample n (h+p)) (i : 'I_n) :
  paper_main_point (sparse_sample_head x) i = usubmx (paper_main_point x i).
Proof.
apply/matrixP=>j k; rewrite (ord1 k).
by rewrite /sparse_sample_head sparse_sample_pick_point /usubmx mxE.
Qed.

Definition sparse_sample_target n h p (m : 'rV[RR]_h)
    (x : paper_main_sample n (h+p)) (i : 'I_n) :=
  sparse_head_normalized_target p m (paper_main_point (sparse_sample_head x) i)^T.

Definition sparse_sample_target_size n h p (L : R) (m : 'rV[RR]_h)
    (x : paper_main_sample n (h+p)) :=
  shifted_interpolation_size p L (sparse_sample_target m x).

Lemma sparse_sample_targetE n h p (m : 'rV[RR]_h)
    (x : paper_main_sample n (h+p)) (i : 'I_n) :
  sparse_sample_target m x i = sparse_head_scale m *
    (mxdot (paper_main_point (sparse_sample_head x) i+m^T)
      (paper_main_point (sparse_sample_head x) i+m^T) -
      (h%:R+frobenius m^+2)) / Num.sqrt p%:R.
Proof.
rewrite /sparse_sample_target /sparse_head_normalized_target
  sparse_head_target_expansion frobenius_sqr.
have -> : (paper_main_point (sparse_sample_head x) i)^T+m =
    (paper_main_point (sparse_sample_head x) i+m^T)^T.
  by rewrite linearD /= trmxK.
by rewrite mxdot_trmx; ring.
Qed.

Lemma sparse_sample_tail_point n h p (x : paper_main_sample n (h+p)) (i : 'I_n) :
  paper_main_point (sparse_sample_tail x) i = dsubmx (paper_main_point x i).
Proof.
apply/matrixP=>j k; rewrite (ord1 k).
by rewrite /sparse_sample_tail sparse_sample_pick_point /dsubmx mxE.
Qed.

Lemma sparse_sample_block_point n h p (x : paper_main_sample n (h+p)) (i : 'I_n) :
  paper_main_point x i = col_mx
    (paper_main_point (sparse_sample_head x) i)
    (paper_main_point (sparse_sample_tail x) i).
Proof. by rewrite sparse_sample_head_point sparse_sample_tail_point vsubmxK. Qed.

Definition sparse_block_shift h p (m : 'rV[RR]_h) : 'cV[RR]_(h+p) := col_mx m^T 0.

Lemma sparse_translated_block_point n h p (m : 'rV[RR]_h)
    (x : paper_main_sample n (h+p)) (i : 'I_n) :
  paper_main_point (sample_translate (sparse_block_shift p m) x) i =
    col_mx (paper_main_point (sparse_sample_head x) i+m^T)
      (paper_main_point (sparse_sample_tail x) i).
Proof.
by rewrite sample_translate_point /sparse_block_shift
  [paper_main_point x i]sparse_sample_block_point add_col_mx addr0.
Qed.

Lemma shifted_interpolation_sizeN n p (L : R) (y : 'I_n -> R) :
  shifted_interpolation_size p L (fun i=>-y i) = shifted_interpolation_size p L y.
Proof.
have hs : \sum_(i<n) (-y i)^+2 = \sum_(i<n) (y i)^+2.
  by apply: eq_bigr=>i _; rewrite sqrrN.
have hm : \big[Num.max/0]_(i<n) `|-y i| = \big[Num.max/0]_(i<n) `|y i|.
  by apply: eq_bigr=>i _; rewrite normrN.
by rewrite /shifted_interpolation_size hs hm.
Qed.

Theorem sparse_block_sample_pd_fit n h p (m : 'rV[RR]_h)
    (x : paper_main_sample n (h+p)) (D L : R) :
  (0 < n)%N -> (0 < p)%N -> 1 <= D -> 0 <= L ->
  universality_conditioned_fit_event n p D (sparse_sample_tail x) ->
  mixture_interpolation n p L (sparse_sample_tail x) ->
  sparse_sample_target_size L m x <= (2*D)^-1 ->
  universality_pd_fit_event n (h+p)
    (sample_translate (sparse_block_shift p m) x).
Proof.
move=> n0 p0 D1 L0 hf hI hs.
have [s0 s1 _] := sparse_head_scale_bounds m.
apply: (@sparse_block_pd_fit n h p (sparse_sample_tail x)
  (sample_translate (sparse_block_shift p m) x)
  (fun i => paper_main_point (sparse_sample_head x) i+m^T)
  D (sparse_head_scale m) L (h%:R+frobenius m^+2)
  n0 p0 D1 s0 s1 L0 hf hI).
  exact: sparse_translated_block_point.
have he : (fun i : 'I_n => -sparse_head_scale m *
    (mxdot (paper_main_point (sparse_sample_head x) i+m^T)
      (paper_main_point (sparse_sample_head x) i+m^T) -
      (h%:R+frobenius m^+2)) / Num.sqrt p%:R) =
    (fun i => -sparse_sample_target m x i).
  by apply/funext=>i; rewrite sparse_sample_targetE mulNr mulNr.
by rewrite he shifted_interpolation_sizeN.
Qed.

Lemma measurable_sparse_head_point_row n h p (i : 'I_n) :
  measurable_fun [set: paper_main_sample n (h+p)]
    (fun x => (paper_main_point (sparse_sample_head x) i)^T : 'rV[RR]_h).
Proof.
apply: (eq_measurable_fun
  (fun x => tnth (sample_row_tuple (sparse_sample_head x)) i)).
  by move=>x _; rewrite /sample_row_tuple tnth_mktuple.
apply: measurableT_comp (measurable_tnth i) _.
exact: measurableT_comp (@measurable_sample_row_tuple n h)
  (@measurable_sparse_sample_pick n (h+p) h (lshift p)).
Qed.

Lemma measurable_sparse_sample_target n h p (m : 'rV[RR]_h) (i : 'I_n) :
  measurable_fun [set: paper_main_sample n (h+p)]
    (fun x => sparse_sample_target m x i : RR).
Proof.
exact: measurableT_comp (measurable_sparse_head_normalized_target p m)
  (measurable_sparse_head_point_row i).
Qed.

Lemma measurable_sparse_sample_target_size n h p (L : R) (m : 'rV[RR]_h) :
  measurable_fun [set: paper_main_sample n (h+p)]
    (fun x => sparse_sample_target_size L m x : RR).
Proof.
rewrite /sparse_sample_target_size /shifted_interpolation_size.
apply: measurable_funM => //; apply: measurable_funD.
- apply: measurable_funM => //.
  have msum : measurable_fun [set: paper_main_sample n (h+p)]
      (fun x => (\sum_(i<n) sparse_sample_target m x i ^+2 : RR)).
    apply: measurable_sum=>i; apply: measurable_funX.
    exact: measurable_sparse_sample_target.
  exact: measurableT_comp (continuous_measurable_fun (@sqrt_continuous RR)) msum.
- apply: measurable_funM => //.
  apply: measurable_bigmax0=>i.
  exact: measurableT_comp (@normr_measurable RR setT)
    (measurable_sparse_sample_target m i).
Qed.
