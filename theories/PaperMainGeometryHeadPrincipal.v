(* The lower Gram edge passes to principal submatrices: the deterministic
   step "the lower edge in eq:feature-sat passes to principal submatrices,
   so Q_J >= c d I" in the proof of lem:head-correction-bounds (manuscript
   line 1001).

   A head J of size m inside the n features is an injective index map
   s : 'I_m -> 'I_n. The selection matrix S, with S_ki = [s i = k], satisfies
   S^T S = I and S^T G S = (G_(s i, s j))_ij. Hence if G is coercive with
   constant mu (u^T G u >= mu |u|^2), so is every principal submatrix, with
   the same mu; in particular the Gram matrix of the subfamily W o s. With
   PaperMainGeometryHeadCoefficients this gives the exact correction, its
   bounds and the normalized support transfer for every head at once. The
   lower edge of the full Gram matrix and the residual bounds are
   hypotheses here. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* The selection matrix of an index map: S_ki = [s i = k]. *)
Definition paper_main_head_select {n m : nat} (s : 'I_m -> 'I_n) : 'M[R]_(n, m) :=
  \matrix_(k, i) (s i == k)%:R.

(* The principal submatrix (G_(s i, s j))_ij. *)
Definition paper_main_head_principal {n m : nat} (G : 'M[R]_n) (s : 'I_m -> 'I_n) :
    'M[R]_m :=
  \matrix_(i, j) G (s i) (s j).

Lemma pmh_sum_delta n (a : 'I_n) (F : 'I_n -> R) :
  \sum_(k < n) (a == k)%:R * F k = F a.
Proof.
rewrite (bigD1 a) //= eqxx mul1r.
have -> : \sum_(k < n | k != a) (a == k)%:R * F k = 0.
  by apply: big1 => k Hk; rewrite eq_sym (negbTE Hk) mul0r.
by rewrite addr0.
Qed.

Section Principal.
Variables (n m : nat).
Implicit Types (G : 'M[R]_n) (s : 'I_m -> 'I_n) (u : 'cV[R]_m).

Lemma paper_main_head_select_orthonormal s :
  injective s -> (paper_main_head_select s)^T *m paper_main_head_select s = 1%:M.
Proof.
move=> Hs; apply/matrixP => i j; rewrite /paper_main_head_select !mxE.
under eq_bigr do rewrite !mxE.
by rewrite pmh_sum_delta (inj_eq Hs) eq_sym.
Qed.

Lemma paper_main_head_select_principal G s :
  (paper_main_head_select s)^T *m G *m paper_main_head_select s =
  paper_main_head_principal G s.
Proof.
apply/matrixP => i j; rewrite /paper_main_head_principal [LHS]mxE.
have Hrow : forall l, ((paper_main_head_select s)^T *m G) i l = G (s i) l.
  move=> l; rewrite /paper_main_head_select !mxE.
  under eq_bigr do rewrite !mxE.
  exact: pmh_sum_delta.
under eq_bigr do rewrite Hrow /paper_main_head_select mxE mulrC.
by rewrite pmh_sum_delta mxE.
Qed.

Theorem paper_main_head_principal_coercive G s (mu : R) :
  injective s -> paper_main_head_coercive G mu ->
  paper_main_head_coercive (paper_main_head_principal G s) mu.
Proof.
move=> Hs HG u.
have H := HG (paper_main_head_select s *m u).
rewrite trmx_mul -!mulmxA (mulmxA (paper_main_head_select s)^T)
  paper_main_head_select_orthonormal // mul1mx in H.
rewrite -paper_main_head_select_principal.
by rewrite !mulmxA in H *.
Qed.

End Principal.

Lemma paper_main_head_gram_sub d n m (W : 'I_n -> 'M[R]_d) (s : 'I_m -> 'I_n) :
  paper_main_head_gram (fun i => W (s i)) =
  paper_main_head_principal (paper_main_head_gram W) s.
Proof. by apply/matrixP => i j; rewrite /paper_main_head_principal !mxE. Qed.

(* Every head of a family whose full Gram matrix is coercive has a coercive,
   hence invertible, Gram matrix with the same constant. *)
Corollary paper_main_head_sub_coercive d n m (W : 'I_n -> 'M[R]_d)
    (s : 'I_m -> 'I_n) (mu : R) :
  injective s -> paper_main_head_coercive (paper_main_head_gram W) mu ->
  paper_main_head_coercive (paper_main_head_gram (fun i => W (s i))) mu.
Proof.
move=> Hs HG; rewrite paper_main_head_gram_sub.
exact: paper_main_head_principal_coercive.
Qed.
