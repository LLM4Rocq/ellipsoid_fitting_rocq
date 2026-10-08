(* The Gaussian lower bound at fourth moment 3, from the formal proof of the
   Gaussian ellipsoid fitting theorem in theories/: for alpha > 1/4, the
   least squares value Phi_G(R_d^o) (unsat_value of Unsat/LeastSquares) of
   n independent Gaussian features of law gaussian_feature_law 3 d is at
   least a constant e > 0 with probability tending to one when
   n/d^2 -> alpha. This is the lower bound of Proposition 1.4 (ii) of
   Koehler and Sohn (arXiv 2608.27372, line 323 of arxiv_v1.tex) at
   kappa = 3, without the limit of the error, at Stdlib's R.

   Results:
   - goe_public_parseval, goe_public_cov: for the orthonormal basis E_k of
     the symmetric matrices of theories/ (goe_basis), the sum over k of
     <S, E_k> <S', E_k> is <S, S'> for S and S' symmetric, and
     (<U, V> + <U, V^T>) / 2 for all U and V.
   - goe_feature_mx, goe_feature_mx_cov: the GOE matrix of theories/ of a
     row y of D coordinates (goe_matrix, of scale sqrt (2/d)) is, read by
     mxvec, y G for the D x (d * d) matrix G whose row k is
     mxvec (sqrt (2/d) E_k); and G^T G = unsat_cov 3 d.
   - goe_features, goe_featuresE, goe_features_law: the GOE features of the
     N rows of a bulk array of theories/ (the public Gaussian rows of
     theories/Hybrid/Residual.v). Under the frozen gaussian_product_law they
     are N independent features of law gaussian_feature_law 3 d (Model/Rows
     for the rows, gauss_mulmx_law of comparison/gauss_law.v for each row:
     both laws are images of standard Gaussian vectors under matrices with
     the same G^T G).
   - goe_gap_unsat_value: outside the event of paper_main_hybrid_gap_event
     (theories/Hybrid/Assembly.v) at head dimension 0, unsat_value of the
     GOE features is at least 2 e. For S > 0 of trace d and b real,
     S / (2 sqrt d) is positive semidefinite with squared Frobenius norm at
     least 1/4 (unsat_domain_frobenius), the residual of theories/ at
     (0, b / 2, S / (2 sqrt d)) is half the least squares residual
     (goe_residualE), and the loss 1 - exp (- t^2) of theories/ is at most
     t^2 (paper_main_loss_le_sqr).
   - goe_unsat_value_lower: for alpha > 1/4 there is e > 0 such that, when
     n d / d^2 -> alpha, the probability that unsat_value (n d) d Z < e for
     Z of law tuple_prod (fun=> gaussian_feature_law 3 d) (n d) tends
     to 0. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.convex Require Import least_squares logdet_barrier.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.comparison Require Import gauss_law.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions Tensor.Definitions
  Goe.Definitions Goe.MatrixBasis Spectral.Transport
  Gaussian.Symmetric.Coordinates Gaussian.Symmetric.PublicFeature
  Gordon.ProcessCovariance Geometry.Psd Geometry.Homogeneous
  Analysis.RealsBridge Analysis.ContinuousTupleMeasurability
  Gaussian.Law.LibraryBridge Loss.Translated Head.SmallBallNet.
From EllipsoidFitting Require Import Hybrid.Residual Hybrid.Loss Hybrid.Assembly.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows Measurability.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure, which carries the
   measurable structure of MathComp-Analysis on matrices. *)
Local Notation RR := (R : realType).

(* The Frobenius pairing of theories/ is mxdot. *)
Lemma mxdot_pairing n (A B : 'M[RR]_n) : mxdot A B = paper_main_pairing A B.
Proof. by []. Qed.

Section goe_rows.
Variable mi : nat.
Local Notation d := mi.+1.
Local Notation D := (paper_main_symmetric_dimension mi).

(* The basis matrix E_k of theories/, as a matrix of MathComp. *)
Definition goe_public_basis (k : nat) : 'M[RR]_d :=
  paper_main_matrix_to_public mi (goe_basis mi k).

Lemma goe_public_basis_sym k : (goe_public_basis k)^T = goe_public_basis k.
Proof.
apply/matrixP => a b; rewrite mxE /goe_public_basis.
rewrite !paper_main_matrix_to_public_entry.
by apply: goe_basis_symmetric; apply/ssrnat.leP; rewrite -ltnS.
Qed.

(* The symmetric matrices of theories/ and of MathComp. *)
Lemma paper_main_symmetricP (S : 'M[RR]_d) :
  S^T = S -> paper_main_symmetric S.
Proof. by move=> St i j; rewrite -[in LHS]St mxE. Qed.

(* <S, E_k> is the coordinate k of S in the basis of theories/. *)
Lemma mxdot_goe_public_basis (S : 'M[RR]_d) k : S^T = S ->
  mxdot S (goe_public_basis k) =
  paper_main_symmetric_coordinates mi (paper_main_matrix_from_public mi S) k.
Proof.
move=> St; rewrite mxdotC -{1}(paper_main_matrix_public_roundtrip mi S).
rewrite /goe_public_basis mxdot_pairing -paper_main_matrix_public_pairing //.
apply: paper_main_matrix_internal_symmetric.
exact: paper_main_symmetricP.
Qed.

(* Parseval's identity in the orthonormal basis of the symmetric matrices
   of theories/. *)
Lemma goe_public_parseval (S S' : 'M[RR]_d) : S^T = S -> S'^T = S' ->
  \sum_(k < D) mxdot S (goe_public_basis k) * mxdot S' (goe_public_basis k) =
  mxdot S S'.
Proof.
move=> St S't; under eq_bigr do rewrite !mxdot_goe_public_basis //.
set T := paper_main_matrix_from_public mi S.
set T' := paper_main_matrix_from_public mi S'.
rewrite -(finite_sum_seqE D (fun k => paper_main_symmetric_coordinates mi T k *
  paper_main_symmetric_coordinates mi T' k)).
have HT : symmetric_matrix mi T.
  by apply: paper_main_matrix_internal_symmetric; exact: paper_main_symmetricP.
have HT' : symmetric_matrix mi T'.
  by apply: paper_main_matrix_internal_symmetric; exact: paper_main_symmetricP.
have := paper_main_symmetric_coordinate_pairing mi T T' HT HT'.
rewrite /paper_main_gordon_dot => ->.
by rewrite paper_main_matrix_public_pairing // /T /T'
  !paper_main_matrix_public_roundtrip.
Qed.

(* For all matrices U and V, the sum over the basis of <U, E_k> <V, E_k> is
   <U, V> of their symmetric parts, (<U, V> + <U, V^T>) / 2. *)
Lemma goe_public_cov (U V : 'M[RR]_d) :
  \sum_(k < D) mxdot U (goe_public_basis k) * mxdot V (goe_public_basis k) =
  2^-1 * (mxdot U V + mxdot U V^T).
Proof.
have symE (W : 'M[RR]_d) k : mxdot W (goe_public_basis k) =
    mxdot (2^-1 *: (W + W^T)) (goe_public_basis k).
  rewrite mxdotZl mxdotDl -{3}(goe_public_basis_sym k) mxdot_trmx -mulr2n.
  by rewrite -[X in _ * X]mulr_natl mulrA mulVf ?mul1r // pnatr_eq0.
have symT (W : 'M[RR]_d) : (2^-1 *: (W + W^T))^T = 2^-1 *: (W + W^T).
  by rewrite linearZ /= linearD /= trmxK addrC.
under eq_bigr do rewrite (symE U) (symE V).
rewrite goe_public_parseval ?symT // mxdotZl mxdotZr !mxdotDl !mxdotDr.
rewrite -[in mxdot U^T V](trmxK V) !mxdot_trmx; congr (_ * _).
rewrite [X in _ + X]addrC -mulr2n -[X in _ * X]mulr_natl mulrA.
by rewrite mulVf ?mul1r // pnatr_eq0.
Qed.

(* The matrix of the map from the D Gaussian coordinates of a row of
   theories/ to its GOE feature: row k is mxvec (goe_scale mi * E_k). *)
Definition goe_feature_mx : 'M[RR]_(D, d * d) :=
  \matrix_(k, p) mxvec (goe_scale mi *: goe_public_basis k) 0 p.

(* Its rows have the covariance of the Gaussian feature at kappa = 3:
   <theta G, theta' G> = C_3 (theta, theta'). *)
Lemma goe_feature_mx_cov :
  goe_feature_mx^T *m goe_feature_mx = unsat_cov 3%:R d.
Proof.
apply/matrixP => p q; rewrite !mxE.
have AE (k : 'I_D) (r : 'I_(d * d)) : goe_feature_mx k r =
    goe_scale mi * mxdot (vec_mx (delta_mx 0 r)) (goe_public_basis k).
  rewrite mxE linearZ /= mxE; congr (_ * _).
  by rewrite -mxdot_delta -{1}(vec_mxK (delta_mx 0 r)) mxdot_mxvec mxdotC.
under eq_bigr do rewrite mxE !AE mulrACA.
rewrite -mulr_sumr goe_public_cov /unsat_cov_form.
rewrite !RmultE !RplusE RminusE subrr mul0r addr0 mulrA; congr (_ * _).
have := goe_scale_square mi; rewrite RmultE RdivE INRE => ->.
by rewrite mulrAC mulfV ?mul1r // IZRposE INRE pnatr_eq0.
Qed.

(* The GOE features of a bulk array of theories/: the GOE matrices of its N
   rows of D coordinates (theories/Hybrid/Residual.v), read by mxvec. *)
Definition goe_features N (x : (N * D).-tuple (measurableTypeR R)) :
    N.-tuple 'rV[RR]_(d * d) :=
  [tuple mxvec (paper_main_public_gaussian_row mi i (tval x)) | i < N].

(* Each is the image of the coordinates of its row under goe_feature_mx. *)
Lemma goe_featuresE N (x : (N * D).-tuple (measurableTypeR R)) :
  goe_features N x = tuple_map (fun=> fun t => row_of_tuple D t *m goe_feature_mx)
    (tuple_rows N D x).
Proof.
apply: eq_from_tnth => i; rewrite /tuple_map !tnth_mktuple.
apply/rowP => p; case/mxvec_indexP: p => a b.
rewrite mxvecE /paper_main_public_gaussian_row paper_main_matrix_to_public_entry.
rewrite /paper_main_gaussian_feature_row /goe_matrix matrix_entry_scale.
rewrite goe_module_sum_entry paper_main_matrix_coordinate_sum.
rewrite RmultE !mxE mulr_sumr; apply: eq_bigr => k _.
rewrite (matrix_entry_scale mi _ (goe_basis mi k) a b) RmultE mulrCA mulrA.
rewrite /vector_entry tuple_entry_build; first by have := ltn_ord k;
  rewrite ltnS => /ssrnat.leP.
rewrite row_of_tupleE tnth_mktuple !mxE linearZ /= mxE mxvecE.
rewrite /goe_public_basis paper_main_matrix_to_public_entry -mulrA.
by congr (_ * _); rewrite (tnth_nth 0%R) -List_nthE.
Qed.

Lemma measurable_goe_features N :
  measurable_fun [set: (N * D).-tuple (measurableTypeR R)] (goe_features N).
Proof.
apply: (eq_measurable_fun (fun x => tuple_map
    (fun=> fun t => row_of_tuple D t *m goe_feature_mx) (tuple_rows N D x))).
  by move=> x _; rewrite goe_featuresE.
apply: measurableT_comp; last exact: measurable_tuple_rows.
apply: measurable_tuple_map => i.
by apply: measurable_mulmx; [exact: measurable_row_of_tuple|
  exact: measurable_cst].
Qed.

(* The GOE features of N independent rows are N independent Gaussian
   features of law gaussian_feature_law 3 d: both are images of standard
   Gaussian vectors under matrices G with the same G^T G (gauss_mulmx_law of
   comparison/gauss_law.v). *)
Lemma goe_features_law N (A : set (N.-tuple 'rV[RR]_(d * d))) :
  measurable A ->
  gaussian_product_law (N * D) (goe_features N @^-1` A) =
  tuple_prod (fun=> gaussian_feature_law 3%:R d) N A.
Proof.
move=> mA.
pose g (t : D.-tuple (measurableTypeR R)) := row_of_tuple D t *m goe_feature_mx.
have -> : goe_features N = (fun x => tuple_map (fun=> g) (tuple_rows N D x)).
  by apply/funext => x; exact: goe_featuresE.
rewrite gaussian_sample_lawE; apply: sample_map_law => //.
  by apply: measurable_mulmx; [exact: measurable_row_of_tuple|
    exact: measurable_cst].
move=> B mB.
have mBG : measurable [set y : 'rV[RR]_D | B (y *m goe_feature_mx)].
  rewrite -[X in measurable X]setTI.
  by apply: measurable_mulmx mB => //; exact: measurable_cst.
rewrite -gaussian_product_law_tuple_prod.
rewrite (_ : g @^-1` B =
  row_of_tuple D @^-1` [set y | B (y *m goe_feature_mx)]) //.
rewrite -gauss_gaussian_product_law //.
have AB : (gaussian_feature_mx 3%:R d)^T *m gaussian_feature_mx 3%:R d =
    goe_feature_mx^T *m goe_feature_mx.
  by rewrite goe_feature_mx_cov gaussian_feature_mx_cov // ler1n.
by rewrite -(gauss_mulmx_law AB mB).
Qed.

(* The loss 1 - exp (- t^2) of theories/ is at most t^2. *)
Lemma paper_main_loss_le_sqr (t : R) : paper_main_loss t <= t ^+ 2.
Proof.
rewrite /paper_main_loss RminusE RexpE RoppE RpowE lerBlDr -lerBlDl.
exact: expR_ge1Dx.
Qed.

(* A positive definite matrix of convex/logdet_barrier.v is positive
   semidefinite in the sense of the frozen definitions. *)
Lemma posdefmx_paper_main_psd (S : 'M[RR]_d) : posdefmx S -> paper_main_psd S.
Proof.
case=> /symmetricmxP St Spos; split; first exact: paper_main_symmetricP.
move=> v; rewrite paper_main_quadratic_formE.
have [->|v0] := eqVneq v 0; first by rewrite trmx0 !mul0mx mxE.
have := Spos v^T; rewrite trmx_eq0 => /(_ v0).
by rewrite mxdot_rowE trmx_mul trmxK St mulmxA => /ltW.
Qed.

(* For S > 0 of trace d, the matrix S / (2 sqrt d) is admissible in the gap
   event of theories/: its squared Frobenius norm is at least 1/4. *)
Lemma unsat_domain_frobenius (th : 'rV[RR]_(d * d)) : unsat_domain d th ->
  1 / 4%:R <= mxdot ((2 * Num.sqrt d%:R)^-1 *: vec_mx th)
                    ((2 * Num.sqrt d%:R)^-1 *: vec_mx th).
Proof.
case=> _ tr_th.
rewrite mxdotZl mxdotZr mulrA -expr2 exprVn exprMn sqr_sqrtr ?ler0n //.
have cs := mxdot_cauchy_schwarz (vec_mx th) 1%:M.
rewrite !mxdot_trace trmx1 !mulmx1 tr_th mxtrace1 in cs.
have d0 : (0 : RR) < d%:R by rewrite ltr0n.
have hm : d%:R <= mxdot (vec_mx th) (vec_mx th).
  by rewrite -(ler_pM2r d0) -expr2 mxdot_trace.
have d4 : (0 : RR) < 2 ^+ 2 * d%:R by rewrite mulr_gt0 // exprn_gt0.
apply: le_trans (_ : (2 ^+ 2 * d%:R)^-1 * d%:R <= _).
  by rewrite invfM -mulrA mulVf ?gt_eqF // mulr1 div1r expr2 -natrM.
by rewrite ler_pM2l ?invr_gt0.
Qed.

(* The residual of theories/ at H = 0, b / 2 and S / (2 sqrt d) is half the
   residual (<G_i, S> - b)_i of the least squares problem. *)
Lemma goe_residualE N (x : (N * D).-tuple (measurableTypeR R))
    (h : paper_main_sample N 0) (H : 'M[R]_0) (th : 'rV[RR]_(d * d)) (b : R)
    (i : 'I_N) :
  paper_main_hybrid_residual N 0 mi h x H (b / 2)
    ((2 * Num.sqrt d%:R)^-1 *: vec_mx th) i 0 =
  (mxdot (tnth (goe_features N x) i) th - b) / 2.
Proof.
rewrite /paper_main_hybrid_residual !mxE /paper_main_head_small_ball_value.
rewrite /paper_main_quadratic_form /paper_main_trace !big_ord0.
rewrite !RminusE RdivE RmultE RsqrtE INRE -mxdot_pairing mxdotZr IZRposE INRE /=.
rewrite tnth_mktuple -[in RHS](vec_mxK th) mxdot_mxvec.
have s0 : Num.sqrt (d%:R : RR) != 0 by rewrite sqrtr_eq0 -ltNge ltr0n.
by set m := mxdot _ _; field.
Qed.

(* Outside the event of theories/, the least squares value of the GOE
   features is at least 2 e. *)
Lemma goe_gap_unsat_value N (x : (N * D).-tuple (measurableTypeR R))
    (h : paper_main_sample N 0) (e : R) :
  (forall (H : 'M[R]_0) (b : R) (B : 'M[R]_d),
     paper_main_symmetric H -> paper_main_psd B ->
     (1 / 4 <= paper_main_frobenius H ^ 2 + paper_main_frobenius B ^ 2)%Rcoq ->
     (e <= paper_main_hybrid_risk N
        (paper_main_hybrid_residual N 0 mi h x H b B))%Rcoq) ->
  2 * e <= unsat_value N d (goe_features N x).
Proof.
move=> gap; rewrite /unsat_value /ls_value; apply: lb_le_inf.
  exists (ls_objective (goe_features N x) 0 0 (mxvec 1%:M) 0).
  by exists (mxvec 1%:M); [exact: unsat_domain_id | exists 0].
move=> _ [th Dth [b _ <-]].
set c := (2 * Num.sqrt (d%:R : RR))^-1.
have c0 : 0 <= c by rewrite invr_ge0 mulr_ge0 ?sqrtr_ge0.
have Hsym : paper_main_symmetric (0 : 'M[R]_0) by case.
have Hpsd : paper_main_psd (c *: vec_mx th).
  by apply: paper_main_psd_scale c0 _; apply: posdefmx_paper_main_psd; case: Dth.
have Hfro : (1 / 4 <= paper_main_frobenius (0 : 'M[R]_0) ^ 2 +
    paper_main_frobenius (c *: vec_mx th) ^ 2)%Rcoq.
  apply/RleP; rewrite RplusE !RpowE RdivE R1E IZRposE INRE /=.
  rewrite /paper_main_frobenius /paper_main_pairing big_ord0 sqrtr0 expr0n add0r.
  rewrite (_ : \sum_(i < d) _ = mxdot (c *: vec_mx th) (c *: vec_mx th)) //.
  by rewrite sqr_sqrtr ?mxdot_ge0 //; exact: unsat_domain_frobenius.
have := gap 0 (b / 2) (c *: vec_mx th) Hsym Hpsd Hfro.
rewrite /paper_main_hybrid_risk RdivE INRE => /RleP he.
apply: le_trans (_ : 2 * ((\sum_(i < N) paper_main_loss
    (paper_main_hybrid_residual N 0 mi h x 0 (b / 2) (c *: vec_mx th) i 0)) /
    N%:R) <= _); first by rewrite ler_pM2l.
under eq_bigr do rewrite goe_residualE.
apply: le_trans (_ : 2 * ((\sum_(i < N)
    ((mxdot (tnth (goe_features N x) i) th - b) / 2) ^+ 2) / N%:R) <= _).
  rewrite ler_pM2l // ler_wpM2r ?invr_ge0 ?ler0n //.
  by apply: ler_sum => i _; exact: paper_main_loss_le_sqr.
rewrite /ls_objective !mul0r addr0 le_eqVlt; apply/orP; left; apply/eqP.
have sq (i : 'I_N) : ((mxdot (tnth (goe_features N x) i) th - b) / 2) ^+ 2 =
    (b - mxdot (tnth (goe_features N x) i) th) ^+ 2 / 4.
  by set m := mxdot _ _; field.
under eq_bigr do rewrite sq.
rewrite -mulr_suml -[N%:R *+ 2]mulr_natr invfM.
set S := \sum_(i < N) _; set Ni := N%:R^-1; clearbody S Ni.
by field.
Qed.

End goe_rows.

(* exp (- c d^2) tends to 0. *)
Lemma expR_sqr_lt (c eps : R) : 0 < c -> 0 < eps ->
  exists D : nat, forall d : nat, (D <= d)%N -> expR (- c * d%:R ^+ 2) < eps.
Proof.
move=> c0 e0; have [D] := INR_unbounded (eps^-1 / c).
rewrite INRE => /RltP HD; exists (maxn D 1) => d.
rewrite geq_max => /andP[Dd d1].
rewrite mulNr expRN -[X in _ < X]invrK ltf_pV2 ?posrE ?expR_gt0 ?invr_gt0 //.
apply: lt_le_trans (_ : D%:R * c <= _); first by rewrite -ltr_pdivrMr.
apply: le_trans (expR_ge1Dx _).
apply: le_trans (_ : c * d%:R ^+ 2 <= _); last by rewrite lerDr.
rewrite mulrC ler_pM2l // -natrX ler_nat (leq_trans Dd) //.
by rewrite -[X in (X <= _)%N]expn1 leq_pexp2l.
Qed.

(* The Gaussian lower bound at fourth moment 3: for alpha > 1/4 there is
   e > 0 such that n Gaussian features of law gaussian_feature_law 3 d have
   unsat_value below e with probability tending to 0 when n/d^2 -> alpha.
   It is paper_main_hybrid_gap_event of theories/ at head dimension 0, read
   through goe_features_law and goe_gap_unsat_value. *)
Theorem goe_unsat_value_lower (alpha : R) : 1 / 4%:R < alpha ->
  exists e : R, 0 < e /\ forall n : nat -> nat,
    universality_density_tends_to n alpha ->
    paper_main_tends_to (fun d => tuple_prod (fun=> gaussian_feature_law 3%:R d)
      (n d) [set Z | unsat_value (n d) d Z < e]) 0.
Proof.
move=> ha.
have ha' : (1 / 4 < alpha)%Rcoq.
  by apply/RltP; rewrite RdivE R1E IZRposE INRE.
have [eta [e [c [d0 [/RltP eta0 [/RltP e0 [/RltP c0 Hall]]]]]]] :=
  paper_main_hybrid_gap_event alpha ha'.
move: eta0 e0 c0; rewrite R0E => eta0 e0 c0.
exists (2 * e); split; first by rewrite mulr_gt0.
move=> n hn eps eps0.
have [D1 HD1] := hn eta eta0.
have [D3 HD3] := expR_sqr_lt c eps c0 eps0.
exists (maxn (maxn D1 d0) (maxn D3 1)) => d.
rewrite !geq_max => /andP[/andP[D1d d0d] /andP[D3d]].
case: d D1d d0d D3d => [//|mi] D1d d0d D3d _.
set N := n mi.+1.
(* the hypotheses of the gap event of theories/, at r = 0 and d = mi + 1 *)
have hN : (Rabs (INR N - alpha * INR mi.+1 ^ 2) <= eta * INR mi.+1 ^ 2)%Rcoq.
  apply/RleP; rewrite RabsE RminusE !RmultE !INRE RpowE.
  have := HD1 _ D1d; rewrite /paper_main_density -/N RdivE => h.
  have d2 : (0 : RR) < mi.+1%:R ^+ 2 by rewrite exprn_gt0 // ltr0n.
  have d2n : mi.+1%:R ^+ 2 != 0 :> RR by rewrite gt_eqF.
  rewrite (_ : N%:R - alpha * mi.+1%:R ^+ 2 =
    mi.+1%:R ^+ 2 * (N%:R / mi.+1%:R ^+ 2 - alpha)); first by field.
  by rewrite normrM ger0_norm ?ltW // mulrC ltr_pM2r.
have hr : (INR 0 <= sqrt (INR mi.+1) + 1)%Rcoq.
  by apply/RleP; rewrite RplusE INRE RsqrtE R1E addr_ge0 ?sqrtr_ge0.
have hm : (0 + mi + 1 <= mi.+1)%N by rewrite add0n addn1.
have [E [mE [PE HE]]] := Hall mi.+1 N 0 mi d0d hN hr hm.
set A := [set Z | _].
have mA : measurable (A : set (N.-tuple 'rV[RR]_(mi.+1 * mi.+1))).
  have -> : A = (fun Z : N.-tuple 'rV[RR]_(mi.+1 * mi.+1) =>
      unsat_value N mi.+1 Z : RR) @^-1` `]-oo, (2 * e)[%classic.
    by apply/seteqP; split => Z /=; rewrite in_itv.
  rewrite -[X in measurable X]setTI.
  by apply: measurable_unsat_value => //; exact: measurable_itv.
rewrite -(goe_features_law mi N A mA) sube0 gee0_abs ?measure_ge0 //.
(* the GOE features of x have a small value only if (h, x) is in E *)
set S := goe_features mi N @^-1` A.
have mS : measurable S.
  by rewrite /S -[X in measurable X]setTI; apply: measurable_goe_features.
have SE : setT `*` S `<=` E.
  move=> [h x] [_ /= Sx]; apply: contrapT => nE.
  have := goe_gap_unsat_value mi N x h e (HE (h, x) nE).
  by rewrite leNgt Sx.
apply: le_lt_trans (_ : _ <= (gaussian_product_law (N * 0) \x
  gaussian_product_law (N * paper_main_symmetric_dimension mi)) E)%E _.
  rewrite -[X in (X <= _)%E]mul1e.
  rewrite -(probability_setT (gaussian_product_law (N * 0))).
  rewrite -product_measure1E //.
  by apply: le_measure => //; rewrite inE //; exact: measurableX.
apply: le_lt_trans PE _.
by rewrite lte_fin RexpE RmultE RoppE INRE RpowE HD3.
Qed.
