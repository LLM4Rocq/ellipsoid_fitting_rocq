(* The rescaled positive semidefinite cones of Koehler and Sohn (arXiv
   2608.27372, section 5, lines 4848-4950 of arxiv_v1.tex), and the
   covariance of the quadratic features.

   For kappa > 1, c_kappa = (kappa - 3)/2, the map T_kappa multiplies the
   diagonal of a matrix by sqrt ((kappa - 1)/2) and keeps the rest, and the
   cone S^d_kappa = T_kappa(S^d_+) is the image of the positive semidefinite
   cone. The feature covariance is
   C_kappa(A, B) = (1/d) (2 <A, B> + (kappa - 3) <A_diag, B_diag>)
   = (2/d) <T_kappa A, T_kappa B> (eq:gaussian-section-covariance): the
   covariance E <W, A> <W, B> of the quadratic feature W = (x x^T - I)/sqrt d
   of a point with independent coordinates of mean 0, variance 1 and fourth
   moment kappa, and of the Gaussian feature G = sqrt (2/d) T_kappa
   ((A + A^T)/2) of a square matrix A with independent standard normal
   entries ((A + A^T)/2 is the paper's GOE matrix: diagonal entries N(0, 1),
   entries above the diagonal N(0, 1/2), all independent).

   Proved, for kappa > 1:
   - cone_shiftE, cone_shiftD1, kappa_dualE: c_kappa = (kappa - 3)/2,
     1 + c_kappa = (kappa - 1)/2 and kappa^vee = 1 + 4/(kappa - 1), with
     MathComp's operations (the definitions, at Stdlib's R, unfold to
     Stdlib's); cone_shift_gtN1: c_kappa > -1; cone_shift3: c_3 = 0.
   - kappa_dual_gt1, kappa_dualK, kappa_dual3, kappa_dual_lt3,
     kappa_dual_gt3: kappa^vee is an involution of ]1, +oo[ with fixed point
     3, exchanging ]1, 3[ and ]3, +oo[; cone_shift_dual:
     c_{kappa^vee} = -c_kappa/(1 + c_kappa).
   - The map T_kappa (cone_mapE: it multiplies the diagonal by
     sqrt ((kappa - 1)/2)): linear (cone_mapD, cone_mapZ, cone_mapN);
     cone_mapK and cone_mapVK, T_{kappa^vee} = T_kappa^{-1}
     (cone_factor_dual); cone_map3, T_3 is the identity; cone_map_sym,
     T_kappa preserves symmetry; cone_map_pairing, T_kappa is self-adjoint
     for the Frobenius pairing.
   - The covariance: pairing_cone_map, <T_kappa A, T_kappa B> = <A, B> +
     c_kappa sum_i A_ii B_ii; feature_covE, C_kappa(A, B) = (2/d)
     <T_kappa A, T_kappa B>; feature_cov_coercive, for every A,
     min(2, kappa - 1)/d ||A||_F^2 <= C_kappa(A, A) <= max(2, kappa - 1)/d
     ||A||_F^2 (eq:feature-covariance-coercivity); feature_cov1,
     C_kappa(I, I) = kappa - 1.
   - The positive semidefinite cone: psd_outer, v v^T >= 0;
     psd_pairing_ge0, <Y, S> >= 0 for Y, S >= 0 (spectral theorem of
     library/matrix/real_spectral.v); psd_self_dual, a symmetric Y is >= 0
     if and only if <Y, S> >= 0 for every S >= 0.
   - The cones: kappa_coneP, Y is in S^d_kappa if and only if
     T_{kappa^vee} Y >= 0; kappa_cone3, S^d_3 is the positive semidefinite
     cone; kappa_cone_sym, its elements are symmetric; kappa_coneD and
     kappa_coneZ, it is a convex cone; kappa_cone_closed, it is closed
     (an intersection of the closed half-spaces 0 <= <Y, W>,
     continuous_pairing).
   - Lemma 5.2: kappa_cone_dual, within the symmetric matrices the dual
     cone of S^d_kappa is S^d_{kappa^vee}; kappa_cone_polar, its polar cone
     is -S^d_{kappa^vee}.
   - The Gaussian feature: gaussian_feature_pairing, <G, B> = <A, sqrt (2/d)
     T_kappa B> for B symmetric (pairing_goe_part, <(A + A^T)/2, M> =
     <A, M> for M symmetric); gaussian_feature_pairing_law, for A with law
     gauss (d * d), read as a d x d matrix by vec_mx, and B symmetric and
     nonzero, <G, B> has law normal_prob 0 (sqrt C_kappa(B, B))
     (gauss_mxdot of library/comparison/gauss_linear.v); mxdot_vec_mx,
     vec_mx is an isometry for the Frobenius products.

   Definitions, at Stdlib's R read through MathComp's ring_scope as in
   UniversalityDefinitions:
     cone_shift kappa      == c_kappa = (kappa - 3)/2
     kappa_dual kappa      == kappa^vee = 1 + 4/(kappa - 1)
     diag_part S           == the diagonal part S_diag of S
     cone_map kappa S      == T_kappa S = S - S_diag
                              + sqrt ((kappa - 1)/2) S_diag
     kappa_cone kappa d    == S^d_kappa, the image of the positive semidefinite
                              d x d matrices under T_kappa
     feature_cov kappa A B == C_kappa(A, B)
     sym_dual_cone K       == the symmetric Y with <Y, S> >= 0 for S in K
     sym_polar_cone K      == the symmetric Y with <Y, S> <= 0 for S in K
     goe_part A            == (A + A^T)/2
     gaussian_feature kappa A == sqrt (2/d) T_kappa ((A + A^T)/2) *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import measure lebesgue_measure probability.
From mathcomp Require Import normal_distribution.
From GaussianAnalysis Require Import euclidean real_spectral.
From GaussianAnalysis.gaussian Require Import gauss.
From GaussianAnalysis.comparison Require Import gauss_linear.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition cone_shift (kappa : R) : R := (kappa - 3%:R) / 2%:R.

Definition kappa_dual (kappa : R) : R := 1 + 4%:R / (kappa - 1).

Definition diag_part {d : nat} (S : 'M[R]_d) : 'M[R]_d :=
  \matrix_(i, j) (if i == j then S i j else 0).

Definition cone_map {d : nat} (kappa : R) (S : 'M[R]_d) : 'M[R]_d :=
  S - diag_part S + Num.sqrt ((kappa - 1) / 2%:R) *: diag_part S.

Definition kappa_cone (kappa : R) (d : nat) : set 'M[R]_d :=
  [set cone_map kappa S | S in [set S : 'M[R]_d | paper_main_psd S]].

Definition feature_cov (kappa : R) {d : nat} (A B : 'M[R]_d) : R :=
  (2%:R * paper_main_pairing A B + (kappa - 3%:R) * \sum_(i < d) A i i * B i i)
  / d%:R.

Definition sym_dual_cone {d : nat} (K : set 'M[R]_d) : set 'M[R]_d :=
  [set Y | paper_main_symmetric Y /\
    forall S, K S -> 0 <= paper_main_pairing Y S].

Definition sym_polar_cone {d : nat} (K : set 'M[R]_d) : set 'M[R]_d :=
  [set Y | paper_main_symmetric Y /\
    forall S, K S -> paper_main_pairing Y S <= 0].

Definition goe_part {d : nat} (A : 'M[R]_d) : 'M[R]_d := (2%:R)^-1 *: (A + A^T).

Definition gaussian_feature (kappa : R) {d : nat} (A : 'M[R]_d) : 'M[R]_d :=
  Num.sqrt (2%:R / d%:R) *: cone_map kappa (goe_part A).

Section kappa_dual.

Lemma cone_shiftE (kappa : R) : cone_shift kappa = (kappa - 3%:R) / 2%:R.
Proof. by rewrite /cone_shift RdivE RminusE. Qed.

Lemma cone_shiftD1 (kappa : R) : 1 + cone_shift kappa = (kappa - 1) / 2%:R.
Proof. by rewrite cone_shiftE; field. Qed.

Lemma cone_shift_gtN1 (kappa : R) : 1 < kappa -> -1 < cone_shift kappa.
Proof. by move=> k1; rewrite cone_shiftE; lra. Qed.

Lemma cone_shift3 : cone_shift 3%:R = 0.
Proof. by rewrite cone_shiftE subrr mul0r. Qed.

Lemma kappa_dualE (kappa : R) : kappa_dual kappa = 1 + 4%:R / (kappa - 1).
Proof. by rewrite /kappa_dual RplusE RdivE RminusE !R1E. Qed.

Lemma kappa_dual_gt1 (kappa : R) : 1 < kappa -> 1 < kappa_dual kappa.
Proof. by move=> k1; rewrite kappa_dualE ltrDl divr_gt0// subr_gt0. Qed.

Lemma kappa_dualK (kappa : R) : 1 < kappa ->
  kappa_dual (kappa_dual kappa) = kappa.
Proof.
move=> k1; have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
rewrite !kappa_dualE addrAC subrr add0r.
by field.
Qed.

Lemma kappa_dual3 : kappa_dual 3%:R = 3%:R.
Proof. by rewrite kappa_dualE; field. Qed.

Lemma kappa_dual_lt3 (kappa : R) : 3%:R < kappa -> kappa_dual kappa < 3%:R.
Proof.
move=> k3; rewrite kappa_dualE -ltrBrDl ltr_pdivrMr; last by lra.
by lra.
Qed.

Lemma kappa_dual_gt3 (kappa : R) : 1 < kappa -> kappa < 3%:R ->
  3%:R < kappa_dual kappa.
Proof.
move=> k1 k3; rewrite kappa_dualE -ltrBlDl ltr_pdivlMr; last by lra.
by lra.
Qed.

Lemma cone_shift_dual (kappa : R) : 1 < kappa ->
  cone_shift (kappa_dual kappa) = - cone_shift kappa / (1 + cone_shift kappa).
Proof.
move=> k1; have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
rewrite cone_shiftD1 !cone_shiftE kappa_dualE.
by field.
Qed.

(* The diagonal factors of T_kappa and T_{kappa^vee} are inverse. *)
Lemma cone_factor_dual (kappa : R) : 1 < kappa ->
  Num.sqrt ((kappa_dual kappa - 1) / 2%:R) * Num.sqrt ((kappa - 1) / 2%:R) = 1.
Proof.
move=> k1; have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have h0 : 0 <= (kappa_dual kappa - 1) / 2%:R.
  rewrite kappa_dualE addrAC subrr add0r.
  by apply: divr_ge0 => //; apply: divr_ge0 => //; exact: ltW.
rewrite -(sqrtrM _ h0).
have kne : kappa - 1 != 0 by rewrite gt_eqF.
rewrite kappa_dualE addrAC subrr add0r.
have -> : 4%:R / (kappa - 1) / 2%:R * ((kappa - 1) / 2%:R) = 1 :> R by field.
exact: sqrtr1.
Qed.

End kappa_dual.
Section cone_map.
Variable d : nat.
Implicit Types (A B S Y : 'M[R]_d).

(* sqrt ((kappa - 1) / 2), the factor of the diagonal in T_kappa. *)
Lemma cone_mapE (kappa : R) S i j : cone_map kappa S i j =
  if i == j then Num.sqrt ((kappa - 1) / 2%:R) * S i i else S i j.
Proof.
rewrite !mxE; have [->|ij] := eqVneq i j; first by rewrite subrr add0r.
by rewrite subr0 mulr0 addr0.
Qed.

Lemma cone_mapD (kappa : R) A B :
  cone_map kappa (A + B) = cone_map kappa A + cone_map kappa B.
Proof.
apply/matrixP => i j; rewrite [LHS]cone_mapE [in RHS]mxE !cone_mapE.
by case: (i == j); rewrite ?mxE ?mulrDr.
Qed.

Lemma cone_mapZ (kappa : R) (a : R) A :
  cone_map kappa (a *: A) = a *: cone_map kappa A.
Proof.
apply/matrixP => i j; rewrite [LHS]cone_mapE [in RHS]mxE !cone_mapE.
by case: (i == j); rewrite ?mxE // mulrCA.
Qed.

Lemma cone_mapN (kappa : R) A : cone_map kappa (- A) = - cone_map kappa A.
Proof. by rewrite -scaleN1r cone_mapZ scaleN1r. Qed.

(* T_{kappa^vee} = T_kappa^{-1}. *)
Lemma cone_mapK (kappa : R) : 1 < kappa ->
  cancel (cone_map kappa) (@cone_map d (kappa_dual kappa)).
Proof.
move=> k1 S; apply/matrixP => i j; rewrite !cone_mapE.
by case: eqP => [->|_]; rewrite ?eqxx // mulrA cone_factor_dual// mul1r.
Qed.

Lemma cone_mapVK (kappa : R) : 1 < kappa ->
  cancel (@cone_map d (kappa_dual kappa)) (cone_map kappa).
Proof.
move=> k1 S; apply/matrixP => i j; rewrite !cone_mapE.
case: eqP => [->|_]; rewrite ?eqxx //.
by rewrite mulrA [_ * Num.sqrt _]mulrC cone_factor_dual// mul1r.
Qed.

(* T_3 is the identity. *)
Lemma cone_map3 S : cone_map 3%:R S = S.
Proof.
apply/matrixP => i j; rewrite cone_mapE.
have -> : (3%:R - 1) / 2%:R = 1 :> R by field.
by rewrite sqrtr1 mul1r; case: eqP => [->|].
Qed.

Lemma cone_map_sym (kappa : R) S :
  paper_main_symmetric S -> paper_main_symmetric (cone_map kappa S).
Proof. by move=> Ss i j; rewrite !cone_mapE eq_sym; case: eqP => [->|_]. Qed.

(* T_kappa is self-adjoint for the Frobenius pairing. *)
Lemma cone_map_pairing (kappa : R) A B :
  paper_main_pairing (cone_map kappa A) B =
  paper_main_pairing A (cone_map kappa B).
Proof.
rewrite /paper_main_pairing; apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite !cone_mapE; case: eqP => [->|_] //; rewrite mulrCA mulrA.
Qed.

Lemma pairing_cone_map (kappa : R) A B : 1 <= kappa ->
  paper_main_pairing (cone_map kappa A) (cone_map kappa B) =
  paper_main_pairing A B + cone_shift kappa * \sum_(i < d) A i i * B i i.
Proof.
move=> k1.
have c2 : Num.sqrt ((kappa - 1) / 2%:R) ^+ 2 = (kappa - 1) / 2%:R.
  by rewrite sqr_sqrtr// divr_ge0// subr_ge0.
rewrite /paper_main_pairing mulr_sumr -big_split /=; apply: eq_bigr => i _.
have off j : j != i ->
    cone_map kappa A i j * cone_map kappa B i j = A i j * B i j.
  by move=> ji; rewrite !cone_mapE eq_sym (negPf ji).
rewrite (bigD1 i)//= [in RHS](bigD1 i)//= (eq_bigr _ off) !cone_mapE eqxx.
set c := Num.sqrt ((kappa - 1) / 2%:R).
have e : c * A i i * (c * B i i) = c ^+ 2 * (A i i * B i i) by ring.
by rewrite e c2 cone_shiftE; field.
Qed.

(* C_kappa(A, B) = (2/d) <T_kappa A, T_kappa B>. *)
Lemma feature_covE (kappa : R) A B : 1 <= kappa ->
  feature_cov kappa A B =
  2%:R / d%:R * paper_main_pairing (cone_map kappa A) (cone_map kappa B).
Proof.
move=> k1; rewrite pairing_cone_map// cone_shiftE.
have -> : feature_cov kappa A B = (2%:R * paper_main_pairing A B +
    (kappa - 3%:R) * \sum_(i < d) A i i * B i i) / d%:R by [].
by rewrite mulrAC; congr (_ * _); field.
Qed.

(* eq:feature-covariance-coercivity, for every A. *)
Lemma feature_cov_coercive (kappa : R) A : 1 < kappa ->
  Num.min 2%:R (kappa - 1) / d%:R * paper_main_pairing A A <=
    feature_cov kappa A A <=
  Num.max 2%:R (kappa - 1) / d%:R * paper_main_pairing A A.
Proof.
move=> k1.
have -> : feature_cov kappa A A = (2%:R * paper_main_pairing A A +
    (kappa - 3%:R) * \sum_(i < d) A i i * A i i) / d%:R by [].
set P := paper_main_pairing A A.
set s := \sum_(i < d) A i i * A i i.
have sP : s <= P.
  rewrite /s /P /paper_main_pairing; apply: ler_sum => i _.
  rewrite (bigD1 i) //= lerDl; apply: sumr_ge0 => j _.
  by rewrite -expr2 sqr_ge0.
have s0 : 0 <= s by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
set m := Num.min 2%:R (kappa - 1).
set M := Num.max 2%:R (kappa - 1).
have m2 : m <= 2%:R by rewrite /m ge_min lexx.
have mk : m <= kappa - 1 by rewrite /m ge_min lexx orbT.
have M2 : 2%:R <= M by rewrite /M le_max lexx.
have Mk : kappa - 1 <= M by rewrite /M le_max lexx orbT.
(* 2 P + (kappa - 3) s = 2 (P - s) + (kappa - 1) s *)
have h1 : 0 <= (2%:R - m) * (P - s) by rewrite mulr_ge0// subr_ge0.
have h2 : 0 <= (kappa - 1 - m) * s by rewrite mulr_ge0// subr_ge0.
have h3 : 0 <= (M - 2%:R) * (P - s) by rewrite mulr_ge0// subr_ge0.
have h4 : 0 <= (M - (kappa - 1)) * s by rewrite mulr_ge0// subr_ge0.
have di : 0 <= d%:R^-1 :> R by rewrite invr_ge0 ler0n.
by rewrite !(mulrAC _ d%:R^-1) !ler_wpM2r//; [lra | lra].
Qed.

(* C_kappa(I, I) = kappa - 1. *)
Lemma feature_cov1 (kappa : R) : (0 < d)%N ->
  feature_cov kappa (1%:M : 'M[R]_d) 1%:M = kappa - 1.
Proof.
move=> d0.
have -> : feature_cov kappa (1%:M : 'M[R]_d) 1%:M =
    (2%:R * paper_main_pairing (1%:M : 'M[R]_d) 1%:M + (kappa - 3%:R) *
     \sum_(i < d) (1%:M : 'M[R]_d) i i * (1%:M : 'M[R]_d) i i) / d%:R by [].
have eS : \sum_(i < d) (1%:M : 'M[R]_d) i i * (1%:M : 'M[R]_d) i i = d%:R.
  rewrite (eq_bigr (fun=> 1)); first by move=> i _; rewrite mxE eqxx mulr1.
  by rewrite sumr_const card_ord.
have eP : paper_main_pairing (1%:M : 'M[R]_d) 1%:M = d%:R.
  rewrite /paper_main_pairing -eS; apply: eq_bigr => i _.
  rewrite (bigD1 i)//= big1 ?addr0// => j ji.
  by rewrite !mxE eq_sym (negPf ji) mulr0.
rewrite eS eP; have dne : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

End cone_map.

Section psd_cone.
Variable d : nat.
Implicit Types (S Y : 'M[R]_d).

Lemma psd_outer (v : 'cV[R]_d) : paper_main_psd (v *m v^T).
Proof.
split; first by move=> i j; rewrite !mxE !big_ord1 !mxE mulrC.
move=> x; rewrite /paper_main_quadratic_form.
have -> : \sum_(i < d) \sum_(j < d) x i 0 * (v *m v^T) i j * x j 0 =
    (\sum_(i < d) x i 0 * v i 0) ^+ 2.
  rewrite expr2 mulr_suml; apply: eq_bigr => i _; rewrite mulr_sumr.
  by apply: eq_bigr => j _; rewrite mxE big_ord1 !mxE; ring.
exact: sqr_ge0.
Qed.

(* <Y, S> >= 0 for Y, S >= 0. *)
Lemma psd_pairing_ge0 Y S :
  paper_main_psd Y -> paper_main_psd S -> 0 <= paper_main_pairing Y S.
Proof.
move=> [_ Ypsd] [Ss Spsd].
have Ssym : S \is symmetricmx by apply/symmetricmxP; exact/paper_main_symmetricP.
have qfE (M : 'M[R]_d) (x : 'cV[R]_d) :
    mxdot x (M *m x) = paper_main_quadratic_form M x.
  by rewrite paper_main_quadratic_formE mxdot_colE mulmxA.
(* S = P^T diag(dv) P with dv >= 0, so <Y, S> = sum_i (P Y P^T)_ii dv_i *)
have [P Po [dv SE]] := symmetric_spectral Ssym.
have d0 i : 0 <= dv 0 i.
  by apply: (spectral_psd Po SE).1 => x; rewrite qfE.
have -> : paper_main_pairing Y S = mxdot Y S by [].
have E : mxdot Y S = \sum_i (P *m Y *m P^T) i i * dv 0 i.
  rewrite mxdot_trace; have /symmetricmxP -> := Ssym.
  rewrite SE mulmxA mulmxA mxtrace_mulC !mulmxA.
  by apply: eq_bigr => i _; rewrite mul_mx_diag mxE.
rewrite E; apply: sumr_ge0 => i _; apply: mulr_ge0 => //.
have -> : (P *m Y *m P^T) i i = paper_main_quadratic_form Y (row i P)^T.
  rewrite paper_main_quadratic_formE trmxK -row_mul !mxE.
  by apply: eq_bigr => j _; rewrite !mxE.
exact: Ypsd.
Qed.

(* The positive semidefinite cone is self-dual within the symmetric
   matrices. *)
Lemma psd_self_dual Y : paper_main_symmetric Y ->
  paper_main_psd Y <-> forall S, paper_main_psd S -> 0 <= paper_main_pairing Y S.
Proof.
move=> Ys; split=> [Yp S Sp|H]; first exact: psd_pairing_ge0.
split=> // v; rewrite -paper_main_pairing_outer; exact: H (psd_outer v).
Qed.

End psd_cone.

Section kappa_cone.
Variable d : nat.
Implicit Types (S Y : 'M[R]_d).

(* Y is in S^d_kappa if and only if T_{kappa^vee} Y >= 0. *)
Lemma kappa_coneP (kappa : R) Y : 1 < kappa ->
  kappa_cone kappa d Y <-> paper_main_psd (cone_map (kappa_dual kappa) Y).
Proof.
move=> k1; split; first by case=> S Sp <-; rewrite cone_mapK.
by move=> Yp; exists (cone_map (kappa_dual kappa) Y) => //; rewrite cone_mapVK.
Qed.

Lemma kappa_cone3 : kappa_cone 3%:R d = [set S | paper_main_psd S].
Proof.
apply/seteqP; split => Y /=; first by case=> S Sp <-; rewrite cone_map3.
by move=> Yp; exists Y => //; rewrite cone_map3.
Qed.

Lemma kappa_cone_sym (kappa : R) Y :
  kappa_cone kappa d Y -> paper_main_symmetric Y.
Proof. by case=> S [Ss _] <-; exact: cone_map_sym. Qed.

(* Lemma 5.2: the dual cone of S^d_kappa is S^d_{kappa^vee}. *)
Theorem kappa_cone_dual (kappa : R) : 1 < kappa ->
  sym_dual_cone (kappa_cone kappa d) = kappa_cone (kappa_dual kappa) d.
Proof.
move=> k1; have kd1 := kappa_dual_gt1 _ k1.
apply/seteqP; split => Y.
  (* <Y, T_kappa S> = <T_kappa Y, S>, and the cone S^d_+ is self-dual *)
  move=> [Ys HY]; apply/(kappa_coneP _ _ kd1); rewrite kappa_dualK//.
  apply/(psd_self_dual _ _ (cone_map_sym _ _ _ Ys)) => S Sp.
  by rewrite cone_map_pairing; apply: HY; exists S.
move=> /(kappa_coneP _ _ kd1); rewrite kappa_dualK// => TYp.
split; first by rewrite -(cone_mapK _ _ k1 Y); apply: cone_map_sym; case: TYp.
by move=> _ [S Sp <-]; rewrite -cone_map_pairing; exact: psd_pairing_ge0.
Qed.

(* Lemma 5.2: its polar cone is -S^d_{kappa^vee}. *)
Theorem kappa_cone_polar (kappa : R) : 1 < kappa ->
  sym_polar_cone (kappa_cone kappa d) =
  [set - Y | Y in kappa_cone (kappa_dual kappa) d].
Proof.
move=> k1; rewrite -(kappa_cone_dual _ k1).
have pN (Y S : 'M[R]_d) : paper_main_pairing (- Y) S = - paper_main_pairing Y S.
  rewrite /paper_main_pairing -sumrN; apply: eq_bigr => i _.
  by rewrite -sumrN; apply: eq_bigr => j _; rewrite mxE mulNr.
apply/seteqP; split => Y.
  move=> [Ys HY]; exists (- Y); last exact: opprK.
  split; first by move=> i j; rewrite !mxE Ys.
  by move=> S KS; rewrite pN oppr_ge0; exact: HY.
case=> Z [Zs HZ] <-; split; first by move=> i j; rewrite !mxE Zs.
by move=> S KS; rewrite pN oppr_le0; exact: HZ.
Qed.

Lemma kappa_coneD (kappa : R) S Y :
  kappa_cone kappa d S -> kappa_cone kappa d Y -> kappa_cone kappa d (S + Y).
Proof.
case=> A [As Ap] <- [B [Bs Bp] <-].
exists (A + B); last exact: cone_mapD.
split; first by move=> i j; rewrite !mxE As Bs.
move=> v; have := addr_ge0 (Ap v) (Bp v).
rewrite /paper_main_quadratic_form -big_split; congr (_ <= _).
apply: eq_bigr => i _; rewrite -big_split; apply: eq_bigr => j _.
by rewrite mxE mulrDr mulrDl.
Qed.

Lemma kappa_coneZ (kappa : R) (a : R) S :
  0 <= a -> kappa_cone kappa d S -> kappa_cone kappa d (a *: S).
Proof.
move=> a0 [A [As Ap] <-].
exists (a *: A); last exact: cone_mapZ.
split; first by move=> i j; rewrite !mxE As.
move=> v; have := mulr_ge0 a0 (Ap v).
rewrite /paper_main_quadratic_form mulr_sumr; congr (_ <= _).
apply: eq_bigr => i _; rewrite mulr_sumr; apply: eq_bigr => j _.
by rewrite mxE; ring.
Qed.

End kappa_cone.

Section kappa_cone_closed.
Variable d : nat.

Lemma pairing_delta (Y : 'M[R]_d) i j : paper_main_pairing Y (delta_mx i j) = Y i j.
Proof.
rewrite /paper_main_pairing (bigD1 i)//= (bigD1 j)//= !mxE !eqxx mulr1.
rewrite [X in _ + X + _]big1 ?addr0.
  by move=> l lj; rewrite mxE eqxx (negPf lj) mulr0.
rewrite big1 ?addr0//.
by move=> k ki; rewrite big1// => l _; rewrite mxE (negPf ki) mulr0.
Qed.

Lemma continuous_pairing (W : 'M[R]_d) :
  continuous (fun Y : 'M[R]_d => paper_main_pairing Y W).
Proof.
rewrite /paper_main_pairing.
apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
  (fun i (Y : 'M[R]_d) => \sum_j Y i j * W i j)) => i _.
apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
  (fun j (Y : 'M[R]_d) => Y i j * W i j)) => j _ Y.
apply: (continuousM (s := fun Y : 'M[R]_d => Y i j) (t := fun=> W i j)).
  exact: matrix_normedtype.coord_continuous.
exact: cst_continuous.
Qed.

(* S^d_kappa is closed. *)
Theorem kappa_cone_closed (kappa : R) : 1 < kappa -> closed (kappa_cone kappa d).
Proof.
move=> k1.
(* the closed half-spaces 0 <= <Y, W> *)
pose half (W : 'M[R]_d) := [set Y : 'M[R]_d | 0 <= paper_main_pairing Y W].
have ch W : closed (half W).
  exact: (continuous_closedP _).1 (continuous_pairing W) _ (@closed_ge _ 0).
pose E (ij : 'I_d * 'I_d) : 'M[R]_d := delta_mx ij.1 ij.2 - delta_mx ij.2 ij.1.
have pN Y W : paper_main_pairing Y (- W) = - paper_main_pairing Y W.
  by change (mxdot Y (- W) = - mxdot Y W); rewrite mxdotNr.
have pE Y ij : paper_main_pairing Y (E ij) = Y ij.1 ij.2 - Y ij.2 ij.1.
  rewrite -!pairing_delta.
  change (mxdot Y (E ij) =
    mxdot Y (delta_mx ij.1 ij.2) - mxdot Y (delta_mx ij.2 ij.1)).
  by rewrite mxdotBr.
(* Y is symmetric and <Y, T_{kappa^vee} (v v^T)> >= 0 for every v *)
have -> : kappa_cone kappa d =
    (\bigcap_(ij in [set: 'I_d * 'I_d]) (half (E ij) `&` half (- E ij))) `&`
    \bigcap_(v in [set: 'cV[R]_d]) half (cone_map (kappa_dual kappa) (v *m v^T)).
  apply/seteqP; split => Y.
    move=> /(kappa_coneP _ _ _ k1) [TYs TYp]; split.
      move=> ij _; rewrite /half /= pN pE.
      have Ys : paper_main_symmetric Y.
        by rewrite -(cone_mapVK _ _ k1 Y); exact: cone_map_sym.
      by rewrite Ys subrr oppr0 lexx.
    move=> v _; rewrite /half /= -cone_map_pairing paper_main_pairing_outer.
    exact: TYp.
  move=> [HE Hv]; apply/(kappa_coneP _ _ _ k1); split.
    apply: cone_map_sym => i j.
    have [h1 h2] := HE (i, j) I.
    move: h1 h2; rewrite /half /= pN pE /= oppr_ge0 => h1 h2.
    by apply/eqP; rewrite -subr_eq0 eq_le h2 h1.
  move=> v; rewrite -paper_main_pairing_outer cone_map_pairing.
  exact: Hv.
apply: closedI; apply: closed_bigI => ? _; last exact: ch.
by apply: closedI; exact: ch.
Qed.

End kappa_cone_closed.

Section gaussian_feature.
Local Notation RR := (R : realType).

(* vec_mx is an isometry for the Frobenius products. *)
Lemma mxdot_vec_mx d (x y : 'rV[R]_(d * d)) :
  mxdot (vec_mx x) (vec_mx y) = mxdot x y.
Proof.
rewrite /mxdot [in RHS]big_ord1 [in LHS]pair_bigA /=.
rewrite [in RHS](reindex (uncurry (@mxvec_index d d))) /=.
  exact: curry_mxvec_bij.
by apply: eq_bigr => -[i j] _; rewrite !mxE.
Qed.

Lemma pairing_goe_part d (A M : 'M[R]_d) : paper_main_symmetric M ->
  paper_main_pairing (goe_part A) M = paper_main_pairing A M.
Proof.
move=> /paper_main_symmetricP MT.
change (mxdot (goe_part A) M = mxdot A M).
by rewrite /goe_part mxdotZl mxdotDl -{2}MT mxdot_trmx; field.
Qed.

(* <G, B> = <A, sqrt (2/d) T_kappa B> for B symmetric. *)
Lemma gaussian_feature_pairing (kappa : R) d (A B : 'M[R]_d) :
  paper_main_symmetric B ->
  paper_main_pairing (gaussian_feature kappa A) B =
  paper_main_pairing A (Num.sqrt (2%:R / d%:R) *: cone_map kappa B).
Proof.
move=> Bs.
change (mxdot (gaussian_feature kappa A) B =
  mxdot A (Num.sqrt (2%:R / d%:R) *: cone_map kappa B)).
rewrite /gaussian_feature mxdotZl mxdotZr; congr (_ * _).
change (paper_main_pairing (cone_map kappa (goe_part A)) B =
  paper_main_pairing A (cone_map kappa B)).
by rewrite cone_map_pairing pairing_goe_part//; exact: cone_map_sym.
Qed.

(* For A with law gauss (d * d), read as a d x d matrix by vec_mx, and B
   symmetric and nonzero, <G, B> has law normal_prob 0 (sqrt C_kappa(B, B)). *)
Theorem gaussian_feature_pairing_law (kappa : R) d (B : 'M[R]_d) (U : set RR) :
  1 < kappa -> paper_main_symmetric B -> B != 0 -> measurable U ->
  gauss (d * d) [set x | U (paper_main_pairing (gaussian_feature kappa (vec_mx x)) B)] =
  normal_prob 0 (Num.sqrt (feature_cov kappa B B)) U.
Proof.
move=> k1 Bs B0 mU.
have d0 : (0 < d)%N by case: d B B0 Bs => // B; rewrite flatmx0 eqxx.
(* <G, B> = <x, a> for the vector a of sqrt (2/d) T_kappa B *)
pose M := Num.sqrt (2%:R / d%:R) *: cone_map kappa B.
pose a := mxvec M.
have ea x : paper_main_pairing (gaussian_feature kappa (vec_mx x)) B = mxdot x a.
  rewrite gaussian_feature_pairing//.
  change (mxdot (vec_mx x) M = mxdot x a).
  by rewrite -[in LHS](mxvecK M) mxdot_vec_mx.
have -> : [set x | U (paper_main_pairing (gaussian_feature kappa (vec_mx x)) B)] =
    [set x | U (mxdot x a)].
  by apply/seteqP; split => x /=; rewrite ea.
have a0 : a != 0.
  rewrite mxvec_eq0 scaler_eq0 negb_or; apply/andP; split.
    by rewrite sqrtr_eq0 -ltNge divr_gt0// ltr0n.
  apply/negP => /eqP TB0; move/negP: B0; apply; apply/eqP.
  rewrite -(cone_mapK _ _ k1 B) TB0.
  by apply/matrixP => i j; rewrite cone_mapE !mxE; case: eqP; rewrite ?mulr0.
(* |a|^2 = (2/d) <T_kappa B, T_kappa B> = C_kappa(B, B) *)
have fa : frobenius a = Num.sqrt (feature_cov kappa B B).
  rewrite /frobenius /a -(mxdot_vec_mx _ (mxvec M) (mxvec M)) !mxvecK.
  congr Num.sqrt.
  rewrite (feature_covE _ _ _ _ (ltW k1)).
  change (mxdot M M =
    2%:R / d%:R * mxdot (cone_map kappa B) (cone_map kappa B)).
  by rewrite /M mxdotZl mxdotZr mulrA -expr2 sqr_sqrtr// divr_ge0// ler0n.
by rewrite (gauss_mxdot a0 mU) fa.
Qed.

End gaussian_feature.
