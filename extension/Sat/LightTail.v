(* Proposition 3.4 of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 2436-2450, proof lines
   3610-3805 of arxiv_v1.tex): the light-tail quotient-norm lower bound.
   Item S9 of stage 3 of phase 5 (lane B). This file proves, over any
   realType, everything up to the union bound and its asymptotic count.
   Sat/LightTailBound assembles them with Proposition 3.1 (Sat/Apriori) and
   Corollary 3.13 (Sat/EffectiveRank) into the proposition itself, at
   Stdlib's R (light_tail_quotient).

   Statement. Let x_1, ..., x_n be the points of a sample whose coordinates
   are independent with laws universality_coordinate_law kappa K0, and let
   n / d^2 tend to alpha in (0, 1/2). There are K > 0 and gamma > 0,
   depending only on alpha and K0, such that for every C0 > 0, with
   probability tending to one: for every set I of at most C0 d ln d rows,
   every t with t_i = 0 on I and |t|_oo <= (K d)^(-1/2) |t|_2, and every h
   with h_i = 0 outside I and |h|_1 <= d^(2/3) |t|_2, the nuclear norm of
   L_X^* (h + t) = d^(-1/2) sum_i (h + t)_i (x_i x_i^T - I) is at least
   gamma d |t|_2. Sat/LightTailBound proves it for the larger set of heads
   with |h|_1 <= d |t|_2.

   Plan of the proof, as in the paper.
   - Blocks. The columns are cut into L blocks I_1, ..., I_L of sizes
     d / L + O(1). Stage l = 2, ..., L reveals the rows of I and the
     columns U_l = I_1 + ... + I_(l-1); its fresh block is I_l, and the
     U_l x I_l block of L_X^* lambda is stage_map of Sat/OneStage.v. The
     nuclear norm of a block is at most that of the whole matrix.
   - Good events. G_l asks that the first (1 - eps) p_l sorted eigenvalues
     (spec, library/matrix/von_neumann.v) of
     Sigma_(t, l) = sum_i t_i^2 u_(i, l)^T u_(i, l) be at least mu, and
     that |t_i| |u_(i, l)| <= rho. Each eigenvalue is a Lipschitz function
     of the matrix (spec_lipschitz), so G_l is closed in the revealed
     coordinates; spec_decomposition gives the matrix Q that
     stage_small_ball (Lemma 3.14) takes.
   - A fixed pair. For fixed I, t and h, the events that the block l of
     L_X^* (h + t) has nuclear norm at most 2 gamma d and that G_l holds
     occur together for every l with probability at most
     (C gamma)^((1 - eps) D_L), D_L = sum_l p_l q_l, by stage_small_ball
     at each stage and the sequential revealing of the stages
     (tuple_prod_chain_le, library/probability/conditioning.v).
   - Nets. Nets of the light unit tails of size (C / gamma)^n and of the
     heads of size exp (o(d^2)), the bounds of Proposition 3.1 (iii) (lane
     C, Sat/Apriori) and max_i |x_i|^2 <= 2 d to pass from the nets to all
     pairs, a union bound over the sets I, and the choice of L, eps, gamma
     and K with alpha < (1 - eps) (1 - 1/L) / 2.
   Inputs of lane C, used in Sat/LightTailBound: Corollary 3.13 in the form
   of the sorted eigenvalues, and Proposition 3.1.

   Proved here:
   - spec_frame: if the k largest eigenvalues of a symmetric S are at least
     mu, there is a k x p matrix Q with orthonormal rows with
     mu |y|^2 <= y Q S Q^T y^T for every y;
   - lipschitz_mx_continuous, continuous_spec_sym: Lipschitz functions of
     the matrices are continuous, and so are the sorted eigenvalues of the
     symmetric part;
   - stage_cov, stage_good, measurable_stage_good: the matrix
     Sigma_t = sum_i t_i^2 u_i^T u_i of a stage and its good event, which
     is measurable;
   - stages_small_ball, the bound for a fixed pair: if the stages l < L
     reveal the rows of I and nested sets of columns cU l, each containing
     the columns of the stage before and its fresh columns cJ l, if t
     vanishes on I and h outside I, and c0 d <= k_l, c0 d <= q_l,
     k_l <= p_l and k_l <= d, then the events of the stages (the block of
     L_X^* (h + t) in the dual ball of radius gam d, and the good event with
     the k_l largest eigenvalues) occur together with probability at most
     prod_l (C gam)^(k_l q_l), for gam >= C rho; C depends only on M, mu
     and c0;
   - blk_bnd, blk_p, blk_q, blk_cU, blk_cJ: the blocks of columns, block s
     being [floor (s d / L), floor ((s + 1) d / L)); stage s < L - 1
     reveals the blocks 0, ..., s and its fresh block is s + 1; they
     satisfy the hypotheses of stages_small_ball, and
     blk_p_ge, blk_q_ge give p_s >= (s + 1) (d / L - 1) and
     q_s >= d / L - 1;
   - l1norm, rV_net, head_net: an eta-net of a bounded set of row vectors
     with (2 e (1 + 2 r / eta))^n points, and an l1 eta-net of the heads
     on I of l1 norm at most r with
     (2 e (1 + 2 r sqrt (|I| + 1) / eta))^|I| points;
   - dual_ballP, nuclear_submx, nuclear_outer_le, nuclear_sum_le: the dual
     ball of radius r is the nuclear-norm ball, the nuclear norm of a
     submatrix is at most that of the matrix, and
     nuclear (u^T v) <= |u| |v|;
   - sample_point, sample_feature, stage_map_submx, nuclear_stage_map_le,
     nuclear_stage_map_l1: with W_i = d^(-1/2) (x_i x_i^T - I), the block
     of L_X^* lam = coef_adj W lam on rows cU and columns cJ is
     stage_map; its nuclear norm is at most that of L_X^* lam, and at most
     d^(-1/2) b |lam|_1 when |x_i|^2 <= b for every i;
   - light_tail, light_bad, light_union, the union bound: the bad event
     (some pair (h, t), t a light unit tail off a set I of at most m rows
     and h a head on I of l1 norm at most r, with every block of
     L_X^* (h + t) of nuclear norm below gam d) meets the events of the
     a priori bound (C1 d |lam|_2 for every block), of |x_i|^2 <= 2 d and
     of the good events of all light unit tails only inside a measurable
     set of probability at most
     (n + 1)^m H^m T^n prod_l (2 C gam)^(k_l q_l), with
     H = 2 e (1 + 16 r sqrt (m + 1) / (gam sqrt d)) and
     T = 2 e (1 + 8 C1 / gam);
   - light_gamma, light_count, the count: for alpha < a, there is gam with
     2 C gam <= 1 such that, for every C0 > 0 and every large d, the bound
     of light_union is at most expR (- d) when n <= ((alpha + a) / 2) d^2,
     m <= C0 d ln d, r <= d and sum_l k_l q_l >= a (d - L)^2; with
     k_l >= (1 - eps) p_l, blk_p_ge and blk_q_ge give the last condition
     for a = (1 - eps) (L - 1) / (2 L), which exceeds alpha for L large and
     eps small when alpha < 1/2. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear interval archimedean.
From mathcomp Require Import boolp classical_sets cardinality reals Rstruct.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability.
From mathcomp Require Import measurable_realfun measurable_fun_approximation.
From GaussianAnalysis Require Import measurable_matrix.
From GaussianAnalysis Require Import euclidean opnorm nets real_spectral.
From GaussianAnalysis Require Import von_neumann nuclear.
From GaussianAnalysis Require Import lindeberg tuple_rows conditioning.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Sat Require Import OneStage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section spec_frame.
Context {RT : realType}.

(* The k largest eigenvalues of a symmetric S are at least mu: there is a
   k x p matrix Q with orthonormal rows on whose rows the quadratic form of
   S is at least mu. *)
Lemma spec_frame p (S : 'M[RT]_p) k (mu : RT) :
  S \is symmetricmx -> (k <= p)%N ->
  (forall j : 'I_p, (j < k)%N -> mu <= spec S 0 j) ->
  exists Q : 'M[RT]_(k, p), Q *m Q^T = 1%:M /\
    forall y : 'rV[RT]_k, mu * mxdot y y <= mxdot (y *m Q *m S) (y *m Q).
Proof.
move=> Ss kp hspec.
have [P Po SE] := spec_decomposition Ss.
have PP : P *m P^T = 1%:M by apply/eqP; exact: Po.
(* Q is made of the first k rows of P *)
pose Q : 'M[RT]_(k, p) := \matrix_(i, j) P (widen_ord kp i) j.
have QPT : Q *m P^T = \matrix_(i, j) (widen_ord kp i == j)%:R.
  apply/matrixP => i j; rewrite !mxE.
  have := congr1 (fun M : 'M[RT]_p => M (widen_ord kp i) j) PP.
  by rewrite !mxE => <-; apply: eq_bigr => l _; rewrite !mxE.
exists Q; split.
  apply/matrixP => i i'.
  have := congr1 (fun M : 'M[RT]_(k, p) => M i (widen_ord kp i')) QPT.
  rewrite !mxE => e.
  transitivity (\sum_j Q i j * P^T j (widen_ord kp i')).
    by apply: eq_bigr => l _; rewrite !mxE.
  by rewrite e; congr (_%:R); apply/eqP/eqP => [|->].
(* y Q S Q^T y^T = z diag (spec S) z^T for z = y Q P^T, which is y
   followed by zeros *)
move=> y; rewrite SE.
pose E01 : 'M[RT]_(k, p) := \matrix_(i, j) (widen_ord kp i == j)%:R.
pose z := y *m E01.
have zE : y *m Q *m P^T = z by rewrite -mulmxA QPT.
have E01E : E01 *m E01^T = 1%:M.
  apply/matrixP => i i'; rewrite !mxE.
  rewrite (bigD1 (widen_ord kp i)) //= big1.
    by move=> j /negPf ji; rewrite /E01 !mxE eq_sym ji mul0r.
  rewrite /E01 !mxE eqxx mul1r addr0; congr (_%:R).
  by rewrite -val_eqE /= val_eqE eq_sym.
have zz : mxdot z z = mxdot y y.
  by rewrite /z mxdot_mulmxr -mulmxA E01E mulmx1.
rewrite !mulmxA zE mxdot_mulmxr zE -zz /mxdot big_ord1 big_ord1 mulr_sumr.
apply: ler_sum => j _.
have -> : (z *m diag_mx (spec S)) 0 j * z 0 j =
    spec S 0 j * (z 0 j * z 0 j).
  by rewrite mul_mx_diag mxE mulrAC mulrC.
have [jk|jk] := ltnP j k.
  by rewrite ler_wpM2r ?hspec // -expr2 sqr_ge0.
have -> : z 0 j = 0.
  rewrite /z mxE big1 // => i _; rewrite /E01 mxE.
  have -> : (widen_ord kp i == j) = false.
    by apply/negbTE; apply: contraTneq jk => <-; rewrite -ltnNge /= ltn_ord.
  by rewrite mulr0.
by rewrite !(mulr0, mul0r).
Qed.

(* A function of the matrices that is Lipschitz for the Frobenius norm is
   continuous. *)
Lemma lipschitz_mx_continuous p q (F : 'M[RT]_(p, q) -> RT) (L : RT) :
  (forall A B, `|F A - F B| <= L * frobenius (A - B)) -> continuous F.
Proof.
move=> FL x.
pose L' := `|L| + 1; have L'0 : 0 < L' by rewrite /L' ltr_wpDl.
pose c := L' * (Num.sqrt (p * q)%:R + 1).
have c0 : 0 < c by rewrite mulr_gt0 // ltr_wpDl ?sqrtr_ge0.
have FL' y : `|F x - F y| <= c * `|x - y|.
  rewrite (le_trans (FL x y)) // -mulrA.
  apply: (@le_trans _ _ (L' * frobenius (x - y))).
    by rewrite ler_wpM2r ?frobenius_ge0 // /L' (le_trans (ler_norm _)) // lerDl.
  rewrite (ler_wpM2l (ltW L'0)) //.
  apply: le_trans; first exact: frobenius_le_mx_norm.
  have -> : `|x - y| = mx_norm (x - y) by [].
  by rewrite ler_wpM2r ?lerDl // -[mx_norm _]/(`|x - y|) normr_ge0.
move=> A /nbhs_ballP [e e0 eA]; apply/nbhs_ballP.
exists (e / c); first by rewrite /= divr_gt0.
move=> y; rewrite /= -ball_normE /= => xy; apply: eA; rewrite -ball_normE /=.
by rewrite (le_lt_trans (FL' y)) // mulrC -ltr_pdivlMr.
Qed.

(* The sorted eigenvalues of the symmetric part are continuous. *)
Lemma continuous_spec_sym p (j : 'I_p) :
  continuous (fun A : 'M[RT]_p => spec (2^-1 *: (A + A^T)) 0 j).
Proof.
apply: (@lipschitz_mx_continuous _ _ _ 1) => A B; rewrite mul1r.
have sym (C : 'M[RT]_p) : 2^-1 *: (C + C^T) \is symmetricmx.
  by apply/symmetricmxP; rewrite linearZ /= linearD /= trmxK addrC.
apply: le_trans (spec_lipschitz j (sym A) (sym B)) _.
rewrite -scalerBr frobeniusZ ger0_norm ?invr_ge0 ?ler0n //.
rewrite (_ : A + A^T - (B + B^T) = (A - B) + (A - B)^T); last first.
  apply: le_trans (ler_wpM2l _ (frobeniusD _ _)) _; first by rewrite invr_ge0.
  by rewrite frobenius_trmx mulrDr mulrC -splitr.
by rewrite linearB /= opprD addrACA.
Qed.

End spec_frame.

Section good_event.
Context {RT : realType}.
Local Notation sample n d := ((n * d)%N.-tuple (measurableTypeR RT)).

(* The matrix sum_i t_i^2 u_i^T u_i of the columns c. *)
Definition stage_cov n d p (c : 'I_p -> 'I_d) (x : sample n d)
    (t : 'rV[RT]_n) : 'M[RT]_p :=
  \sum_(i < n) (t 0 i ^+ 2) *: ((stage_row c x i)^T *m stage_row c x i).

Lemma stage_cov_sym n d p (c : 'I_p -> 'I_d) (x : sample n d) t :
  stage_cov c x t \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite /stage_cov linear_sum /=; apply: eq_bigr => i _.
by rewrite linearZ /= trmx_mul trmxK.
Qed.

Lemma stage_cov_form n d p m (c : 'I_p -> 'I_d) (x : sample n d) t
    (Q : 'M[RT]_(m, p)) (y : 'rV[RT]_m) :
  mxdot (y *m Q *m stage_cov c x t) (y *m Q) =
  \sum_(i < n) (t 0 i * mxdot y (stage_row c x i *m Q^T)) ^+ 2.
Proof.
rewrite /stage_cov mulmx_sumr mxdot_suml; apply: eq_bigr => i _.
set u := stage_row c x i.
have e : y *m Q *m (t 0 i ^+ 2 *: (u^T *m u)) =
    (t 0 i ^+ 2 * mxdot y (u *m Q^T)) *: u.
  rewrite -scalemxAr mulmxA [y *m Q *m u^T]mx11_scalar mul_scalar_mx.
  by rewrite scalerA -mxdot_rowE mxdot_mulmxr.
rewrite e mxdotZl [mxdot u _]mxdotC mxdot_mulmxr.
by rewrite exprMn expr2 mulrA.
Qed.

(* The good event of a stage: the k largest eigenvalues of stage_cov are
   at least mu, and |t_i| |u_i| <= rho for every i. *)
Definition stage_good n d p (c : 'I_p -> 'I_d) (t : 'rV[RT]_n) (k : nat)
    (mu rho : RT) : set (sample n d) :=
  [set x | (forall j : 'I_p, (j < k)%N -> mu <= spec (stage_cov c x t) 0 j)
     /\ forall i, `|t 0 i| * frobenius (stage_row c x i) <= rho].

Lemma measurable_stage_good n d p (c : 'I_p -> 'I_d) (t : 'rV[RT]_n) k
    (mu rho : RT) :
  measurable (stage_good c t k mu rho).
Proof.
have mcov : measurable_fun setT (fun x : sample n d => stage_cov c x t).
  apply/measurable_fun_mxP => a b.
  rewrite (_ : (fun x => _) = (fun x : sample n d => \sum_(i < n) t 0 i ^+ 2 *
      (tnth x (row_index i (c a)) * tnth x (row_index i (c b))))).
    apply/funext => x; rewrite /stage_cov summxE; apply: eq_bigr => i _.
    by rewrite !mxE big_ord1 !mxE.
  apply: measurable_sum => i; apply: measurable_funM => //.
  by apply: measurable_funM; exact: measurable_tnth.
have mrow i : measurable_fun setT (fun x : sample n d => stage_row c x i).
  apply/measurable_fun_mxP => a b.
  rewrite (_ : (fun x => _) =
      (fun x : sample n d => tnth x (row_index i (c b)))).
    by apply/funext => x; rewrite mxE.
  exact: measurable_tnth.
have mfrob : measurable_fun setT (fun A : 'rV[RT]_p => frobenius A).
  apply: continuous_measurable_mx; apply: (lipschitz_mx_continuous (L := 1)).
  by move=> A B; rewrite mul1r ler_frobeniusB.
(* the eigenvalues of the symmetric part, equal to those of stage_cov *)
pose f (j : 'I_p) (x : sample n d) :=
  spec (2^-1 *: (stage_cov c x t + (stage_cov c x t)^T)) 0 j.
have fE j x : f j x = spec (stage_cov c x t) 0 j.
  have /symmetricmxP sE := stage_cov_sym c x t.
  have h2 : (2^-1 + 2^-1 : RT) = 1 by lra.
  by rewrite /f sE scalerDr -scalerDl h2 scale1r.
have mf j : measurable_fun setT (f j).
  have := measurableT_comp
    (continuous_measurable_mx (continuous_spec_sym (j := j))) mcov.
  by apply: eq_measurable_fun => x _.
pose g (i : 'I_n) (x : sample n d) := `|t 0 i| * frobenius (stage_row c x i).
have mg i : measurable_fun setT (g i).
  by apply: measurable_funM => //; exact: measurableT_comp mfrob (mrow i).
rewrite (_ : stage_good c t k mu rho =
  \bigcap_(j in [set j : 'I_p | (j < k)%N]) (f j @^-1` `[mu, +oo[%classic)
  `&` \bigcap_(i in [set: 'I_n]) (g i @^-1` `]-oo, rho]%classic)).
  apply/seteqP; split => x /=.
    move=> [h1 h2]; split => [j /= jk|i _] /=; rewrite in_itv /= ?andbT.
      by rewrite fE h1.
    exact: h2.
  move=> [h1 h2]; split => [j jk|i].
    by have := h1 j jk; rewrite /= in_itv /= andbT fE.
  by have := h2 i I; rewrite /= in_itv.
apply: measurableI.
  apply: fin_bigcap_measurable => [|j _].
    by apply: (sub_finite_set (subsetT _)); exact: finite_finset.
  by rewrite -[X in measurable X]setTI; apply: mf => //; exact: measurable_itv.
apply: fin_bigcap_measurable => [|i _]; first exact: finite_finset.
by rewrite -[X in measurable X]setTI; apply: mg => //; exact: measurable_itv.
Qed.

(* The rows and the matrices of a stage do not change when the
   coordinates outside a set S that contains theirs are resampled. *)
Lemma stage_row_merge n d p (c : 'I_p -> 'I_d) (S : {pred 'I_(n * d)})
    (x y : sample n d) i :
  (forall a, row_index i (c a) \in S) ->
  stage_row c (tuple_merge S x y) i = stage_row c x i.
Proof.
move=> hS; apply/rowP => a; rewrite !mxE /sample_entry tnth_merge.
by rewrite hS.
Qed.

Lemma stage_mapD n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (x : sample n d) (l1 l2 : 'rV[RT]_n) :
  stage_map cU cJ x (l1 + l2) = stage_map cU cJ x l1 + stage_map cU cJ x l2.
Proof.
rewrite /stage_map -scalerDr -big_split /=; congr (_ *: _).
by apply: eq_bigr => i _; rewrite mxE scalerDl.
Qed.

End good_event.

Section pair_bound.
Context {RT : realType}.
Local Notation sample n d := ((n * d)%N.-tuple (measurableTypeR RT)).

(* The event of a stage for the pair (h, t): the block of L_X^* (h + t) is
   in the dual ball of radius gam d, and the good event holds. *)
Definition stage_event n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (h t : 'rV[RT]_n) (k : nat) (mu rho gam : RT) : set (sample n d) :=
  [set x | dual_ball (gam * d%:R) (stage_map cU cJ x (h + t))] `&`
  stage_good cU t k mu rho.

Local Open Scope ereal_scope.

(* The bound for a fixed pair (h, t): the stages l < L reveal the rows of I
   and nested sets of columns cU l; the events of the stages occur together
   with probability at most the product of the (C gam)^(k_l q_l). *)
Theorem stages_small_ball (M mu c0 : RT) : (0 < M)%R -> (0 < mu)%R ->
  (0 < c0)%R ->
  exists2 C : RT, (0 < C)%R &
  forall n d L (p q k : nat -> nat) (cU : forall l, 'I_(p l) -> 'I_d)
    (cJ : forall l, 'I_(q l) -> 'I_d)
    (nu : nat -> probability (measurableTypeR RT) RT) (I : {pred 'I_n})
    (h t : 'rV[RT]_n) (rho gam : RT),
  (forall l, injective (cJ l)) -> (forall l a b, cU l a != cJ l b) ->
  (forall l a, exists a', cU l.+1 a' = cU l a) ->
  (forall l b, exists a', cU l.+1 a' = cJ l b) ->
  (forall j, (j < d)%N -> \int[nu j]_x x%:E = 0) ->
  (forall j, (j < d)%N -> \int[nu j]_x ((x ^+ 2)%R)%:E = 1) ->
  (forall j, (j < d)%N -> (2^-1)%:E <=
     \int[nu j]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E) ->
  (forall i, i \in I -> t 0 i = 0)%R ->
  (forall i, i \notin I -> h 0 i = 0)%R ->
  (forall l, (l < L)%N -> (c0 * d%:R <= (k l)%:R)%R /\
     (c0 * d%:R <= (q l)%:R)%R /\ (k l <= p l)%N /\ (k l <= d)%N) ->
  (0 < rho)%R -> (C * rho <= gam)%R ->
  tuple_prod (fun j => nu (j %% d)%N) (n * d)
    (\bigcap_(l < L) stage_event (cU l) (cJ l) h t (k l) mu rho gam) <=
  (\prod_(l < L) (C * gam) ^+ (k l * q l))%R%:E.
Proof.
move=> M0 mu0 c00.
have [C C0 hC] := stage_small_ball M0 mu0 c00.
exists C => // n d L p q k cU cJ nu I h t rho gam cJinj hUJ hUU hJU h0 h1 h2
  ht hh hk rho0 hgam.
have Cg0 : (0 <= C * gam)%R.
  by rewrite mulr_ge0 // ltW // (lt_le_trans _ hgam) // mulr_gt0.
pose S (l : nat) := stage_revealed (cU l) I.
pose A (l : nat) := stage_event (cU l) (cJ l) h t (k l) mu rho gam.
have mD l : measurable [set x : sample n d |
    dual_ball (gam * d%:R)%R (stage_map (cU l) (cJ l) x (h + t))].
  have mm : measurable_fun setT
      (fun x : sample n d => stage_map (cU l) (cJ l) x (h + t)).
    exact: measurable_stage_map.
  have := mm measurableT _ (@measurable_dual_ball _ (p l) (q l) (gam * d%:R)%R).
  by rewrite setTI.
have mA l : measurable (A l).
  exact: measurableI (mD l) (measurable_stage_good _ _ _ _ _).
(* the columns of stage l are revealed at stage l, those of stage l and
   its fresh columns at stage l + 1 *)
have inSU l i a : row_index i (cU l a) \in S l.
  by rewrite /S stage_revealedE; apply/orP; right; apply/existsP; exists a.
have inSUs l i a : row_index i (cU l a) \in S l.+1.
  by have [a' <-] := hUU l a; exact: inSU.
have inSJs l i b : row_index i (cJ l b) \in S l.+1.
  by have [a' <-] := hJU l b; exact: inSU.
have gS l x y (U : {pred 'I_(n * d)}) :
    (forall i a, row_index i (cU l a) \in U) ->
    stage_good (cU l) t (k l) mu rho (tuple_merge U x y) =
    stage_good (cU l) t (k l) mu rho x.
  move=> hU; have eU i := stage_row_merge x y (hU i).
  have ecov : stage_cov (cU l) (tuple_merge U x y) t = stage_cov (cU l) x t.
    by rewrite /stage_cov; apply: eq_bigr => i _; rewrite eU.
  rewrite /stage_good /= ecov; apply/propext.
  by split => -[g1 g2]; split => // i; [rewrite -eU|rewrite eU]; exact: g2.
have AS l x y : A l (tuple_merge (S l.+1) x y) = A l x.
  have eU i := stage_row_merge x y (inSUs l i).
  have eJ i := stage_row_merge x y (inSJs l i).
  have emap lam : stage_map (cU l) (cJ l) (tuple_merge (S l.+1) x y) lam =
      stage_map (cU l) (cJ l) x lam.
    by rewrite /stage_map; congr (_ *: _); apply: eq_bigr => i _; rewrite eU eJ.
  by rewrite /A /stage_event /= emap (gS l x y (S l.+1) (inSUs l)).
(* given the coordinates revealed at stage l, Lemma 3.14 *)
have hcond l x : (l < L)%N ->
    tuple_prod (fun j => nu (j %% d)%N) (n * d)
      [set y | A l (tuple_merge (S l) x y)] <= ((C * gam) ^+ (k l * q l))%:E.
  move=> lL; have [hk1 [hk2 [hk3 hk4]]] := hk l lL.
  have mX := measurable_merge_section (S l) x (mA l).
  case: (pselect (stage_good (cU l) t (k l) mu rho x)) => [gx|ngx]; last first.
    rewrite (_ : [set y | _] = set0) ?measure0 ?lee_fin ?exprn_ge0 //.
    apply/seteqP; split => // y [_ gy]; apply: ngx.
    by rewrite -(gS l x y (S l) (inSU l)).
  have [Q [QQ hQ]] := spec_frame (stage_cov_sym (cU l) x t) hk3 gx.1.
  pose B := stage_map (cU l) (cJ l) x h.
  have eh y : stage_map (cU l) (cJ l) (tuple_merge (S l) x y) h = B.
    rewrite /B /stage_map; congr (_ *: _); apply: eq_bigr => i _.
    have [iI|iI] := boolP (i \in I); last by rewrite hh // !scale0r.
    by rewrite !stage_row_merge // => a; rewrite /S stage_revealedE iI.
  pose Y := [set X : sample n d |
    dual_ball (gam * d%:R)%R (stage_map (cU l) (cJ l) X t + B)%R].
  have mY : measurable Y.
    have mm : measurable_fun setT
        (fun X : sample n d => (stage_map (cU l) (cJ l) X t + B)%R).
      apply: measurable_addmx; last exact: measurable_cst.
      exact: measurable_stage_map.
    have := mm measurableT _
      (@measurable_dual_ball _ (p l) (q l) (gam * d%:R)%R).
    by rewrite setTI.
  have sub : [set y | A l (tuple_merge (S l) x y)] `<=`
      [set y | Y (tuple_merge (S l) x y)].
    move=> y [hy _]; rewrite /Y /= -(eh y) addrC -stage_mapD.
    exact: hy.
  apply: le_trans (le_measure _ (mem_set mX)
    (mem_set (measurable_merge_section (S l) x mY)) sub) _.
  apply: (hC n d (p l) (q l) (k l) (cU l) (cJ l) nu I t Q B x rho gam) => //.
  - by move=> y; rewrite -stage_cov_form; exact: hQ.
  - exact: gx.2.
(* the stages, revealed one after the other *)
clear hC gS mD.
apply: (tuple_prod_chain_le (S := S) (A := A)
  (c := fun l => ((C * gam) ^+ (k l * q l))%R)).
- by move=> l _; exact: mA.
- move=> l j /existsP [i /existsP [j' /andP [/eqP -> hij]]].
  rewrite stage_revealedE; case/orP: hij => [-> //|/existsP [a /eqP <-]].
  have [a' <-] := hUU l a; apply/orP; right; apply/existsP; exists a'.
  by [].
- by move=> l x y _; exact: AS.
- by move=> l _; rewrite exprn_ge0.
- by move=> l x lL _; exact: hcond.
Qed.

End pair_bound.


(* The boundaries of the L blocks of columns: bnd s = (min (s, L) d) / L,
   rounded down, so that block s < L is the set of columns
   [bnd s, bnd s.+1). Stage s reveals the columns [0, blk_p s) of the
   blocks 0, ..., s and its fresh columns are those of block s.+1. *)
Definition blk_bnd (L d s : nat) : nat := (minn s L * d) %/ L.

Lemma blk_bnd_le L d s : (blk_bnd L d s <= d)%N.
Proof.
rewrite /blk_bnd; case: L => [|L]; first by rewrite divn0.
apply: leq_trans (leq_div2r _ (leq_mul (geq_minr s L.+1) (leqnn d))) _.
by rewrite mulKn.
Qed.

Lemma blk_bnd_mono L d s s' :
  (s <= s')%N -> (blk_bnd L d s <= blk_bnd L d s')%N.
Proof.
move=> ss'; apply: leq_div2r; apply: leq_mul => //.
by rewrite leq_min geq_minr (leq_trans (geq_minl _ _) ss').
Qed.

Definition blk_p (L d s : nat) : nat := blk_bnd L d s.+1.
Definition blk_q (L d s : nat) : nat := blk_bnd L d s.+2 - blk_bnd L d s.+1.

Lemma blk_pq L d s : (blk_p L d s + blk_q L d s = blk_bnd L d s.+2)%N.
Proof. by rewrite /blk_p /blk_q subnKC // blk_bnd_mono. Qed.

Definition blk_cU (L d s : nat) (a : 'I_(blk_p L d s)) : 'I_d :=
  widen_ord (blk_bnd_le L d s.+1) a.
Arguments blk_cU : clear implicits.

Lemma blk_cJ_subproof L d s (b : 'I_(blk_q L d s)) : (blk_p L d s + b < d)%N.
Proof. by rewrite (leq_trans _ (blk_bnd_le L d s.+2)) // -blk_pq ltn_add2l. Qed.

Definition blk_cJ (L d s : nat) (b : 'I_(blk_q L d s)) : 'I_d :=
  Ordinal (blk_cJ_subproof b).
Arguments blk_cJ : clear implicits.

Lemma blk_cU_inj L d s : injective (blk_cU L d s).
Proof. by move=> a a' /(congr1 val) /= e; apply: val_inj. Qed.

Lemma blk_cJ_inj L d s : injective (blk_cJ L d s).
Proof. by move=> b b' /(congr1 val) /= /addnI e; apply: val_inj. Qed.

Lemma blk_cUJ L d s a b : blk_cU L d s a != blk_cJ L d s b.
Proof.
by rewrite -val_eqE /= neq_ltn (leq_trans (ltn_ord a)) ?leq_addr.
Qed.

Lemma blk_cU_succ L d s a : exists a', blk_cU L d s.+1 a' = blk_cU L d s a.
Proof.
have h : (a < blk_p L d s.+1)%N.
  by rewrite (leq_trans (ltn_ord a)) // blk_bnd_mono.
by exists (Ordinal h); apply: val_inj.
Qed.

Lemma blk_cJ_succ L d s b : exists a', blk_cU L d s.+1 a' = blk_cJ L d s b.
Proof.
have h : (blk_p L d s + b < blk_p L d s.+1)%N.
  by rewrite [X in (_ < X)%N]/blk_p -blk_pq ltn_add2l.
by exists (Ordinal h); apply: val_inj.
Qed.



Section block_sizes.
Context {RT : realType}.

Lemma blk_bnd_ge L d s : (0 < L)%N -> (s <= L)%N ->
  (s * d)%:R / L%:R - 1 <= (blk_bnd L d s)%:R :> RT.
Proof.
move=> L0 sL; rewrite /blk_bnd (minn_idPl sL).
have L0' : (0 < L%:R :> RT) by rewrite ltr0n.
rewrite lerBlDr ler_pdivrMr // mulrDl mul1r -natrM -natrD ler_nat.
by rewrite {1}(divn_eq (s * d) L) leq_add2l ltnW // ltn_pmod.
Qed.

Lemma blk_bnd_le_div L d s : (0 < L)%N -> (s <= L)%N ->
  (blk_bnd L d s)%:R <= (s * d)%:R / L%:R :> RT.
Proof.
move=> L0 sL; rewrite /blk_bnd (minn_idPl sL).
have L0' : (0 < L%:R :> RT) by rewrite ltr0n.
by rewrite ler_pdivlMr // -natrM ler_nat leq_divM.
Qed.

Lemma blk_p_ge L d s : (0 < L)%N -> (s.+1 <= L)%N ->
  s.+1%:R * (d%:R / L%:R - 1) <= (blk_p L d s)%:R :> RT.
Proof.
move=> L0 sL; apply: le_trans (blk_bnd_ge d L0 sL).
by rewrite mulrBr mulr1 natrM mulrA lerB // ?ler1n.
Qed.

Lemma blk_q_ge L d s : (0 < L)%N -> (s.+2 <= L)%N ->
  d%:R / L%:R - 1 <= (blk_q L d s)%:R :> RT.
Proof.
move=> L0 sL; rewrite /blk_q natrB ?blk_bnd_mono //.
have h1 := blk_bnd_ge d L0 sL.
have h2 := blk_bnd_le_div d L0 (ltnW sL).
move: h1; rewrite mulSn natrD mulrDl => h1.
lra.
Qed.

Lemma sum_succ_nat (N : nat) : \sum_(s < N) (s.+1)%:R = (N * N.+1)%:R / 2 :> RT.
Proof.
elim: N => [|N IH]; first by rewrite big_ord0 mul0n mul0r.
rewrite big_ord_recr /= IH !natrM -[N.+2]addn2 -[N.+1]addn1 !natrD.
by field.
Qed.

End block_sizes.

Section light_nets.
Context {RT : realType}.

Definition l1norm n (h : 'rV[RT]_n) : RT := \sum_i `|h 0 i|.

Lemma l1norm_ge0 n (h : 'rV[RT]_n) : 0 <= l1norm h.
Proof. by apply: sumr_ge0 => i _. Qed.

Lemma l1normD n (h h' : 'rV[RT]_n) : l1norm (h + h') <= l1norm h + l1norm h'.
Proof.
rewrite /l1norm -big_split /=; apply: ler_sum => i _.
by rewrite mxE ler_normD.
Qed.

Lemma l1normN n (h : 'rV[RT]_n) : l1norm (- h) = l1norm h.
Proof. by apply: eq_bigr => i _; rewrite mxE normrN. Qed.

Lemma frobenius_le_l1norm n (h : 'rV[RT]_n) : frobenius h <= l1norm h.
Proof.
rewrite -(ger0_norm (l1norm_ge0 h)) -sqrtr_sqr; apply: ler_wsqrtr.
rewrite /mxdot big_ord1 /l1norm expr2 mulr_suml; apply: ler_sum => i _.
rewrite mulr_sumr (bigD1 i) //= -normrM ler_wpDr ?real_ler_norm ?num_real //.
by apply: sumr_ge0 => j _; rewrite -normrM normr_ge0.
Qed.

Lemma l1norm_le_frobenius n (h : 'rV[RT]_n) :
  l1norm h <= Num.sqrt n%:R * frobenius h.
Proof.
pose s : 'rV[RT]_n := \row_i (Num.sg (h 0 i)).
have e : l1norm h = mxdot h s.
  rewrite /mxdot big_ord1; apply: eq_bigr => i _.
  by rewrite mxE mulrC -normrEsg.
have s1 : frobenius s <= Num.sqrt n%:R.
  rewrite /frobenius ler_wsqrtr // /mxdot big_ord1.
  apply: (le_trans (y := \sum_(i < n) (1 : RT))); last first.
    by rewrite sumr_const card_ord.
  apply: ler_sum => i _; rewrite mxE -expr2 sqr_sg.
  by case: (h 0 i != 0); rewrite ?ler01 ?lexx.
rewrite e mulrC; apply: le_trans (ler_mxdot _ _) _.
by rewrite ler_wpM2l ?frobenius_ge0.
Qed.

(* An eta-net of a bounded set of row vectors, of its own points. *)
Lemma rV_net n (S : set 'rV[RT]_n) (r eta : RT) : 0 <= r -> 0 < eta ->
  (forall t, S t -> frobenius t <= r) ->
  exists Ns : seq 'rV[RT]_n, [/\ forall t, t \in Ns -> S t,
    forall t, S t -> exists2 t0, t0 \in Ns & frobenius (t - t0) <= eta &
    (size Ns)%:R <= (2 * expR 1 * (1 + 2 * r / eta)) ^+ n].
Proof.
move=> r0 e0 Sr.
have Sr' (c : 'cV[RT]_n) : [set c | S c^T] c -> frobenius c <= r.
  by move=> /= Sc; rewrite -frobenius_trmx Sr.
have [Nc [NcS Ncnet Ncsize]] := net_exists r0 e0 Sr'.
exists (map trmx Nc); split.
- by move=> t /mapP [c cN ->]; exact: NcS.
- move=> t St.
  have [c cN tc] : exists2 c, c \in Nc & frobenius (t^T - c) <= eta.
    by apply: Ncnet; rewrite /= trmxK.
  exists c^T; first by apply/mapP; exists c.
  by rewrite -frobenius_trmx linearB /= trmxK.
- by rewrite size_map.
Qed.

(* The heads: vectors supported on I of l1 norm at most r. *)
Definition light_head n (I : {set 'I_n}) (r : RT) : set 'rV[RT]_n :=
  [set h : 'rV[RT]_n | (forall i, i \notin I -> h 0 i = 0) /\ l1norm h <= r].

(* An l1 net of the heads, of its own points, of size exponential in |I|:
   a net of the l1 ball of 'rV_#|I| for the Euclidean distance, pushed to
   the coordinates of I. *)
Lemma head_net n (I : {set 'I_n}) (r eta : RT) : 0 <= r -> 0 < eta ->
  exists Ns : seq 'rV[RT]_n, [/\ forall h, h \in Ns -> light_head I r h,
    forall h, light_head I r h ->
      exists2 h0, h0 \in Ns & l1norm (h - h0) <= eta &
    (size Ns)%:R <=
      (2 * expR 1 * (1 + 2 * r * Num.sqrt (#|I|.+1)%:R / eta)) ^+ #|I|].
Proof.
move=> r0 e0; set k := #|I|.
pose emb (v : 'rV[RT]_k) : 'rV[RT]_n :=
  \row_i \sum_(a < k) (enum_val a == i)%:R * v 0 a.
pose pull (h : 'rV[RT]_n) : 'rV[RT]_k := \row_a h 0 (enum_val a).
have embv v a : emb v 0 (enum_val a) = v 0 a.
  rewrite mxE (bigD1 a) //= eqxx mul1r big1 ?addr0 // => b ba.
  by rewrite (inj_eq enum_val_inj) (negPf ba) mul0r.
have emb0 v i : i \notin I -> emb v 0 i = 0.
  move=> iI; rewrite mxE big1 // => a _.
  have : enum_val a \in I := enum_valP a.
  by case: eqP => [->|_]; rewrite ?(negPf iI) // mul0r.
have embB v w : emb (v - w) = emb v - emb w.
  apply/rowP => i; rewrite !mxE -sumrB; apply: eq_bigr => a _.
  by rewrite !mxE mulrBr.
have l1emb v : l1norm (emb v) = l1norm v.
  have z : \sum_(i | i \notin I) `|emb v 0 i| = 0.
    by apply: big1 => i /emb0 ->; rewrite normr0.
  rewrite /l1norm (bigID (mem I)) /= z addr0.
  rewrite (big_enum_val (fun i => `|emb v 0 i|)) /=.
  by apply: eq_bigr => a _; rewrite embv.
have pullK (h : 'rV[RT]_n) :
    (forall i, i \notin I -> h 0 i = 0) -> emb (pull h) = h.
  move=> hI; apply/rowP => i; have [iI|iI] := boolP (i \in I).
    by rewrite -(enum_rankK_in iI iI) embv mxE.
  by rewrite emb0 // hI.
have l1pull (h : 'rV[RT]_n) : l1norm (pull h) <= l1norm h.
  rewrite /l1norm; under eq_bigr do rewrite mxE.
  rewrite -(big_enum_val (fun i => `|h 0 i|)) [X in _ <= X](bigID (mem I)) /=.
  by rewrite lerDl sumr_ge0.
pose S' := [set v : 'rV[RT]_k | l1norm v <= r].
have S'r v : S' v -> frobenius v <= r.
  by move=> /= vr; exact: le_trans (frobenius_le_l1norm v) vr.
have e'0 : 0 < eta / Num.sqrt (k.+1)%:R by rewrite divr_gt0 // sqrtr_gt0 ltr0n.
have [Ns' [Ns'S Ns'net Ns'size]] := rV_net r0 e'0 S'r.
exists (map emb Ns'); split.
- move=> h /mapP [v vN ->]; split; first by move=> i iI; exact: emb0.
  by rewrite l1emb; exact: Ns'S.
- move=> h [hI hr]; have [v vN hv] := Ns'net (pull h) (le_trans (l1pull h) hr).
  exists (emb v); first by apply/mapP; exists v.
  rewrite -[X in X - _](pullK h hI) -embB l1emb.
  apply: le_trans (l1norm_le_frobenius _) _.
  apply: le_trans (ler_wpM2l (sqrtr_ge0 _) hv) _.
  rewrite mulrA ler_pdivrMr ?sqrtr_gt0 ?ltr0n // mulrC ler_wpM2l ?(ltW e0) //.
  by rewrite ler_wsqrtr // ler_nat.
- rewrite size_map; apply: (le_trans Ns'size).
  by rewrite invf_div mulrA lexx.
Qed.

End light_nets.
Section nuclear_blocks.
Context {RT : realType}.

Lemma dual_ballP m q (r : RT) (A : 'M[RT]_(m, q)) : 0 <= r ->
  dual_ball r A <-> nuclear A <= r.
Proof.
move=> r0; split => [hA|hA C].
  apply: nuclear_le => B B1; apply: le_trans (hA B) _.
  by rewrite -[leRHS]mulr1 ler_wpM2l.
apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_le_nuclear A C) _.
by rewrite mulrC ler_wpM2r ?opnorm_ge0.
Qed.

Lemma sum_sel l (j : 'I_l) (F : 'I_l -> RT) : \sum_i (j == i)%:R * F i = F j.
Proof.
rewrite (bigD1 j) //= eqxx mul1r.
have -> : \sum_(i < l | i != j) (j == i)%:R * F i = 0.
  by apply: big1 => i /negPf ij; rewrite eq_sym ij mul0r.
by rewrite addr0.
Qed.

(* The matrix whose rows are the unit vectors e_(f a). *)
Definition sel_mx k l (f : 'I_k -> 'I_l) : 'M[RT]_(k, l) :=
  \matrix_(a, i) (f a == i)%:R.

Lemma sel_mx_orth k l (f : 'I_k -> 'I_l) : injective f ->
  sel_mx f *m (sel_mx f)^T = 1%:M.
Proof.
move=> fi; apply/matrixP => a a'; rewrite /sel_mx !mxE.
under eq_bigr => i _ do rewrite !mxE.
by rewrite sum_sel (inj_eq fi) eq_sym.
Qed.

Lemma sel_mx_sub m n p q (A : 'M[RT]_(m, n)) (f : 'I_p -> 'I_m)
    (g : 'I_q -> 'I_n) :
  \matrix_(a, b) A (f a) (g b) = sel_mx f *m A *m (sel_mx g)^T.
Proof.
apply/matrixP => a b; rewrite /sel_mx !mxE.
under eq_bigr => i _ do rewrite !mxE.
under eq_bigr => i _ do under eq_bigr => j _ do rewrite mxE.
under eq_bigr => i _ do rewrite sum_sel mulrC.
by rewrite sum_sel.
Qed.

(* The nuclear norm of a submatrix is at most that of the matrix. *)
Lemma nuclear_submx m n p q (A : 'M[RT]_(m, n)) (f : 'I_p -> 'I_m)
    (g : 'I_q -> 'I_n) :
  injective f -> injective g ->
  nuclear (\matrix_(a, b) A (f a) (g b)) <= nuclear A.
Proof.
move=> fi gi; rewrite sel_mx_sub; apply: nuclear_le => B B1.
have o1 : opnorm (sel_mx f)^T <= 1 := opnorm_trmx_orthorows (sel_mx_orth fi).
have o2 : opnorm (sel_mx g) <= 1.
  by rewrite -opnorm_trmx; exact: opnorm_trmx_orthorows (sel_mx_orth gi).
rewrite mxdot_mulmxr trmxK mxdot_mulmxl; apply: nuclear_ub.
apply: (le_trans (opnorm_mulmx _ _)); rewrite -[leRHS]mul1r.
apply: ler_pM; rewrite ?opnorm_ge0 //.
apply: (le_trans (opnorm_mulmx _ _)); rewrite -[leRHS]mul1r.
by apply: ler_pM; rewrite ?opnorm_ge0.
Qed.

Lemma nuclear_outer_le p q (u : 'rV[RT]_p) (v : 'rV[RT]_q) :
  nuclear (u^T *m v) <= frobenius u * frobenius v.
Proof.
apply: nuclear_le => B B1; rewrite mxdot_mulmxl trmxK.
apply: le_trans (ler_mxdot _ _) _; rewrite mulrC ler_wpM2r ?frobenius_ge0 //.
rewrite -frobenius_trmx trmx_mul.
apply: le_trans (frobenius_mulmx_opnorm _ _) _.
by rewrite opnorm_trmx frobenius_trmx -[leRHS]mul1r ler_wpM2r ?frobenius_ge0.
Qed.

Lemma nuclear_sum_le m n (I : finType) (F : I -> 'M[RT]_(m, n)) :
  nuclear (\sum_i F i) <= \sum_i nuclear (F i).
Proof.
elim/big_ind2: _ => // [|A a B b hA hB].
  by rewrite (eqP (_ : nuclear (0 : 'M[RT]_(m, n)) == 0)) // nuclear_eq0.
by apply: le_trans (nuclearD _ _) (lerD hA hB).
Qed.

End nuclear_blocks.

Section sample_blocks.
Context {RT : realType}.
Local Notation sample n d := ((n * d)%N.-tuple (measurableTypeR RT)).

(* Point i of the sample, as a row vector. *)
Definition sample_point n d (x : sample n d) (i : 'I_n) : 'rV[RT]_d :=
  \row_j sample_entry x i j.

(* The matrices W_i = d^(-1/2) (x_i x_i^T - I) of the paper, whose
   combination coef_adj (sample_feature x) lam is L_X^* lam. *)
Definition sample_feature n d (x : sample n d) (i : 'I_n) : 'M[RT]_d :=
  (Num.sqrt d%:R)^-1 *: ((sample_point x i)^T *m sample_point x i - 1%:M).

(* The block of the rows cU and the columns cJ of L_X^* lam. *)
Lemma stage_map_submx n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (x : sample n d) (lam : 'rV[RT]_n) :
  (forall a b, cU a != cJ b) ->
  stage_map cU cJ x lam =
  \matrix_(a, b) coef_adj (sample_feature x) lam (cU a) (cJ b).
Proof.
move=> UJ; apply/matrixP => a b; rewrite /stage_map /coef_adj !mxE !summxE.
rewrite mulr_sumr; apply: eq_bigr => i _.
rewrite !mxE big_ord1 !mxE big_ord1 !mxE (negPf (UJ a b)) subr0.
by rewrite mulrCA.
Qed.

Lemma nuclear_stage_map_le n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (x : sample n d) (lam : 'rV[RT]_n) :
  injective cU -> injective cJ -> (forall a b, cU a != cJ b) ->
  nuclear (stage_map cU cJ x lam) <= nuclear (coef_adj (sample_feature x) lam).
Proof.
by move=> Ui Ji UJ; rewrite stage_map_submx //; exact: nuclear_submx.
Qed.

Lemma stage_row_sel n d p (c : 'I_p -> 'I_d) (x : sample n d) i :
  stage_row c x i = sample_point x i *m (sel_mx c)^T.
Proof.
apply/rowP => a; rewrite !mxE.
under eq_bigr => j _ do rewrite !mxE mulrC.
by rewrite sum_sel.
Qed.

Lemma frobenius_stage_row n d p (c : 'I_p -> 'I_d) (x : sample n d) i :
  injective c -> frobenius (stage_row c x i) <= frobenius (sample_point x i).
Proof.
move=> ci; rewrite stage_row_sel.
exact: frobenius_mulmx_orthorows (sel_mx_orth ci).
Qed.

(* The l1 bound of the paper: if |x_i|^2 <= b for every i, the nuclear norm
   of a block of L_X^* lam is at most d^(-1/2) b |lam|_1. *)
Lemma nuclear_stage_map_l1 n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (x : sample n d) (lam : 'rV[RT]_n) (b : RT) :
  injective cU -> injective cJ ->
  (forall i, frobenius (sample_point x i) ^+ 2 <= b) ->
  nuclear (stage_map cU cJ x lam) <=
  (Num.sqrt d%:R)^-1 * b * l1norm lam.
Proof.
move=> Ui Ji hb; rewrite /stage_map nuclearZ ger0_norm ?invr_ge0 ?sqrtr_ge0 //.
rewrite -mulrA ler_wpM2l ?invr_ge0 ?sqrtr_ge0 //.
apply: le_trans (nuclear_sum_le _) _; rewrite /l1norm mulr_sumr.
apply: ler_sum => i _; rewrite nuclearZ mulrC ler_wpM2r //.
apply: le_trans (nuclear_outer_le _ _) _; apply: le_trans (hb i); rewrite expr2.
by apply: ler_pM; rewrite ?frobenius_ge0 ?frobenius_stage_row.
Qed.

End sample_blocks.

Section light_union.
Context {RT : realType}.
Local Notation sample n d := ((n * d)%N.-tuple (measurableTypeR RT)).

Lemma stage_mapN n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (x : sample n d) (l1 : 'rV[RT]_n) :
  stage_map cU cJ x (- l1) = - stage_map cU cJ x l1.
Proof.
rewrite /stage_map -scalerN -sumrN; congr (_ *: _).
by apply: eq_bigr => i _; rewrite mxE scaleNr.
Qed.

Lemma measurable_stage_event n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (h t : 'rV[RT]_n) (k : nat) (mu rho gam : RT) :
  measurable (stage_event cU cJ h t k mu rho gam : set (sample n d)).
Proof.
apply: measurableI; last exact: measurable_stage_good.
have mm : measurable_fun setT
    (fun x : sample n d => stage_map cU cJ x (h + t)).
  exact: measurable_stage_map.
have := mm measurableT _ (@measurable_dual_ball _ p q (gam * d%:R)).
by rewrite setTI.
Qed.

(* The light unit tails off I. *)
Definition light_tail n (I : {set 'I_n}) (K d : RT) : set 'rV[RT]_n :=
  [set t : 'rV[RT]_n | [/\ forall i, i \in I -> t 0 i = 0, frobenius t = 1 &
     forall i, `|t 0 i| <= (Num.sqrt (K * d))^-1]].

(* Some pair (h, t) with t a light unit tail off a set I of at most m rows
   and h a head on I has all its blocks of nuclear norm below gam d. *)
Definition light_bad n d L m (K r gam : RT) : set (sample n d) :=
  [set x | exists (I : {set 'I_n}) (h t : 'rV[RT]_n), [/\ (#|I| <= m)%N,
     light_head I r h, light_tail I K d%:R t &
     forall l, (l < L.-1)%N ->
       nuclear (stage_map (blk_cU L d l) (blk_cJ L d l) x (h + t)) <
       gam * d%:R]].

(* Every set of at most m rows is the set of the rows of an m-tuple of
   options, and conversely. *)
Lemma tuple_of_set n m (I : {set 'I_n}) : (#|I| <= m)%N ->
  exists s : m.-tuple (option 'I_n), [set i | Some i \in s]%SET = I.
Proof.
move=> Im.
have sz : size (map Some (enum I) ++ nseq (m - #|I|) None) == m.
  by rewrite size_cat size_map size_nseq -cardE subnKC.
exists (Tuple sz); apply/setP => i; rewrite inE /= mem_cat mem_nseq andbF orbF.
by rewrite (mem_map (@Some_inj _)) mem_enum.
Qed.

Lemma card_tuple_set n m (s : m.-tuple (option 'I_n)) :
  (#|[set i | Some i \in s]%SET| <= m)%N.
Proof.
have -> : [set i | Some i \in s]%SET = [set i | i \in pmap id s]%SET.
  by apply/setP => i; rewrite !inE mem_pmap map_id.
rewrite cardsE (leq_trans (card_size _)) // size_pmap.
by rewrite (leq_trans (count_size _ _)) // size_tuple.
Qed.

Lemma mu_bigsetU_le d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (I : Type) (s : seq I) (P : pred I)
    (F : I -> set T) :
  (forall i, P i -> measurable (F i)) ->
  (mu (\big[setU/set0]_(i <- s | P i) F i) <= \sum_(i <- s | P i) mu (F i))%E.
Proof.
move=> mF.
have : measurable (\big[setU/set0]_(i <- s | P i) F i) /\
    (mu (\big[setU/set0]_(i <- s | P i) F i) <=
     \sum_(i <- s | P i) mu (F i))%E.
  elim/big_rec2: _ => [|i U u Pi [mU hU]]; first by rewrite measure0.
  split; first exact: measurableU (mF i Pi) mU.
  exact: le_trans (measureU2 _ (mF i Pi) mU) (leeD (lexx _) hU).
by case.
Qed.

Lemma bigsetU_seqP (T : Type) (I : eqType) (s : seq I) (F : I -> set T) x :
  (exists2 i, i \in s & F i x) -> (\big[setU/set0]_(i <- s) F i) x.
Proof.
elim: s => [|a s IH] [i]; rewrite ?in_nil // big_cons inE.
case/orP => [/eqP -> Fx|iS Fx]; first by left.
by right; apply: IH; exists i.
Qed.

Local Open Scope ereal_scope.

(* The union bound of the proof of Proposition 3.4: on the events of the a
   priori bound, of the norms of the points and of Corollary 3.13, the bad
   event is contained in a measurable set of probability at most
   (n + 1)^m H^m T^n prod_l (2 C gam)^(k_l q_l): there are at most
   (n + 1)^m sets I, H^m heads and T^n tails in the nets, and each pair has
   the bound of stages_small_ball. *)
Theorem light_union (M mu c0 : RT) : (0 < M)%R -> (0 < mu)%R -> (0 < c0)%R ->
  exists2 C : RT, (0 < C)%R &
  forall n d L m (k : nat -> nat)
    (nu : nat -> probability (measurableTypeR RT) RT) (K r C1 rho gam : RT),
  (forall j, (j < d)%N -> \int[nu j]_x x%:E = 0) ->
  (forall j, (j < d)%N -> \int[nu j]_x ((x ^+ 2)%R)%:E = 1) ->
  (forall j, (j < d)%N -> (2^-1)%:E <=
     \int[nu j]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E) ->
  (forall l, (l < L.-1)%N -> (c0 * d%:R <= (k l)%:R)%R /\
     (c0 * d%:R <= (blk_q L d l)%:R)%R /\ (k l <= blk_p L d l)%N /\
     (k l <= d)%N) ->
  (0 < rho)%R -> (C * rho <= 2 * gam)%R -> (0 < gam)%R -> (0 < C1)%R ->
  (0 <= r)%R -> (0 < d)%N ->
  exists U : set (sample n d), [/\ measurable U,
    tuple_prod (fun j => nu (j %% d)%N) (n * d) U <=
      ((n.+1)%:R ^+ m *
       (2 * expR 1 * (1 + 16 * r * Num.sqrt (m.+1)%:R /
          (gam * Num.sqrt d%:R))) ^+ m *
       (2 * expR 1 * (1 + 8 * C1 / gam)) ^+ n *
       \prod_(l < L.-1) (C * (2 * gam)) ^+ (k l * blk_q L d l))%R%:E &
    forall x : sample n d,
      (forall l (lam : 'rV[RT]_n), (l < L.-1)%N ->
         nuclear (stage_map (blk_cU L d l) (blk_cJ L d l) x lam) <=
         C1 * d%:R * frobenius lam)%R ->
      (forall i, frobenius (sample_point x i) ^+ 2 <= 2 * d%:R)%R ->
      (forall (I : {set 'I_n}) t, (#|I| <= m)%N -> light_tail I K d%:R t ->
         forall l, (l < L.-1)%N ->
           stage_good (blk_cU L d l) t (k l) mu rho x) ->
      light_bad L m K r gam x -> U x].
Proof.
move=> M0 mu0 c00.
have [C C0 hC] := stages_small_ball M0 mu0 c00.
exists C => // n d L m k nu K r C1 rho gam hm0 hm1 hm2 hk rho0 hgam gam0 C10
  r0 d0.
have sd0 : (0 < Num.sqrt d%:R :> RT)%R by rewrite sqrtr_gt0 ltr0n.
pose eh := (gam * Num.sqrt d%:R / 8)%R.
pose et := (gam / (4 * C1))%R.
have eh0 : (0 < eh)%R by rewrite /eh divr_gt0 // mulr_gt0.
have et0 : (0 < et)%R by rewrite /et divr_gt0 // mulr_gt0.
have tail1 (I : {set 'I_n}) t : light_tail I K d%:R t -> (frobenius t <= 1)%R.
  by case=> _ -> _.
pose Nh (I : {set 'I_n}) := projT1 (cid (head_net I r0 eh0)).
have NhP (I : {set 'I_n}) := projT2 (cid (head_net I r0 eh0)).
pose Nt (I : {set 'I_n}) := projT1 (cid (rV_net ler01 et0 (@tail1 I))).
have NtP (I : {set 'I_n}) := projT2 (cid (rV_net ler01 et0 (@tail1 I))).
pose Iof (s : m.-tuple (option 'I_n)) := [set i | Some i \in s]%SET.
pose Ev (I : {set 'I_n}) (h0 t0 : 'rV[RT]_n) :=
  \bigcap_(l < L.-1) stage_event (blk_cU L d l) (blk_cJ L d l) h0 t0 (k l)
    mu rho (2 * gam)%R.
pose U := \big[setU/set0]_(s : m.-tuple (option 'I_n))
  \big[setU/set0]_(h0 <- Nh (Iof s)) \big[setU/set0]_(t0 <- Nt (Iof s))
    Ev (Iof s) h0 t0.
have mEv I h0 t0 : measurable (Ev I h0 t0).
  rewrite /Ev bigcap_mkord; apply: big_ind => //; first exact: measurableI.
  by move=> l _; exact: measurable_stage_event.
exists U; split.
- apply: bigsetU_measurable => s _; apply: bigsetU_measurable => h0' _.
  by apply: bigsetU_measurable => t0 _; exact: mEv.
- pose B := (\prod_(l < L.-1) (C * (2 * gam)) ^+ (k l * blk_q L d l))%R.
  pose Hm := (2 * expR 1 * (1 + 16 * r * Num.sqrt (m.+1)%:R /
    (gam * Num.sqrt d%:R)))%R.
  pose T := (2 * expR 1 * (1 + 8 * C1 / gam))%R.
  have B0 : (0 <= B)%R.
    apply: prodr_ge0 => l _; apply: exprn_ge0.
    by rewrite mulr_ge0 // ?(ltW C0) // mulr_ge0 // ltW.
  have e2 : (1 <= 2 * expR 1 :> RT)%R.
    by have := expR_ge1Dx (1 : RT); lra.
  have Hm1 : (1 <= Hm)%R.
    have z : (0 <= 16 * r * Num.sqrt (m.+1)%:R / (gam * Num.sqrt d%:R))%R.
      apply: divr_ge0; last by apply: mulr_ge0; [exact: ltW|exact: sqrtr_ge0].
      apply: mulr_ge0; last exact: sqrtr_ge0.
      by apply: mulr_ge0; [exact: ler0n|exact: r0].
    by rewrite /Hm; nra.
  have T1 : (1 <= T)%R.
    have z : (0 <= 8 * C1 / gam)%R.
      apply: divr_ge0; last exact: ltW.
      by apply: mulr_ge0; [exact: ler0n|exact: ltW].
    by rewrite /T; nra.
  have Hm0 : (0 <= Hm)%R by apply: le_trans Hm1.
  have g0 : (gam != 0)%R by rewrite gt_eqF.
  have s0 : (Num.sqrt d%:R != 0 :> RT)%R by rewrite gt_eqF.
  have e0 : (0 <= 2 * expR 1 :> RT)%R by have := e2; lra.
  have sizeNh s : ((size (Nh (Iof s)))%:R <= Hm ^+ m)%R.
    have [_ _ hs] := NhP (Iof s); apply: le_trans hs _.
    have km := card_tuple_set s.
    set k' := #|Iof s|.
    pose base := (2 * expR 1 * (1 + 2 * r * Num.sqrt (k'.+1)%:R / eh))%R.
    have base0 : (0 <= base)%R.
      have z : (0 <= 2 * r * Num.sqrt (k'.+1)%:R / eh)%R.
        apply: divr_ge0; last exact: ltW.
        apply: mulr_ge0; last exact: sqrtr_ge0.
        by apply: mulr_ge0; [exact: ler0n|exact: r0].
      by rewrite /base; nra.
    have baseH : (base <= Hm)%R.
      have pos : (0 <= (gam * Num.sqrt d%:R)^-1)%R.
        by rewrite invr_ge0; apply: mulr_ge0; [exact: ltW|exact: sqrtr_ge0].
      have q : (2 * r * Num.sqrt (k'.+1)%:R / eh <=
          16 * r * Num.sqrt (m.+1)%:R / (gam * Num.sqrt d%:R))%R.
        have -> : (2 * r * Num.sqrt (k'.+1)%:R / eh =
            16 * r * Num.sqrt (k'.+1)%:R / (gam * Num.sqrt d%:R))%R.
          by rewrite /eh; field.
        apply: (ler_wpM2r pos); apply: ler_wpM2l.
          by apply: mulr_ge0; [exact: ler0n|exact: r0].
        by apply: ler_wsqrtr; rewrite ler_nat ltnS.
      by rewrite /base /Hm; apply: (ler_wpM2l e0); rewrite lerD2l.
    apply: (le_trans _ (ler_weXn2l Hm1 km)).
    by apply: (lerXn2r k'); rewrite ?nnegrE.
  have sizeNt s : ((size (Nt (Iof s)))%:R <= T ^+ n)%R.
    have [_ _ hs] := NtP (Iof s); apply: le_trans hs _.
    have c0' : (C1 != 0)%R by rewrite gt_eqF.
    by rewrite /T /et (_ : 2 * 1 / (gam / (4 * C1)) = 8 * C1 / gam)%R //; field.
  have hEv (I : {set 'I_n}) h0 t0 : light_head I r h0 ->
      light_tail I K d%:R t0 ->
      tuple_prod (fun j => nu (j %% d)%N) (n * d) (Ev I h0 t0) <= B%:E.
    case=> hI _ [tI _ _].
    have H1 := hC n d L.-1 (blk_p L d) (blk_q L d) k (blk_cU L d) (blk_cJ L d)
      nu [pred i | i \in I] h0 t0 rho (2 * gam)%R.
    have H2 := H1 (fun l => @blk_cJ_inj L d l).
    have H3 := H2 (fun l a b => blk_cUJ a b).
    have H4 := H3 (fun l a => blk_cU_succ a).
    have H5 := H4 (fun l b => blk_cJ_succ b).
    have H6 := H5 hm0 hm1 hm2.
    have H7 := H6 (fun i iI => tI i iI).
    have H8 := H7 (fun i iI => hI i iI).
    have H9 := H8 hk rho0 hgam.
    exact: H9.
  have csum (I' : eqType) (s : seq I') (c : RT) :
      \sum_(i <- s) c%:E = ((size s)%:R * c)%R%:E.
    have cs : count xpredT s = size s by elim: s => //= a s ->.
    by rewrite sumEFin big_const_seq cs iter_addr addr0 mulr_natl.
  have inner s : tuple_prod (fun j => nu (j %% d)%N) (n * d)
      (\big[setU/set0]_(h0 <- Nh (Iof s)) \big[setU/set0]_(t0 <- Nt (Iof s))
        Ev (Iof s) h0 t0) <= (Hm ^+ m * T ^+ n * B)%R%:E.
    have [NhS _ _] := NhP (Iof s); have [NtS _ _] := NtP (Iof s).
    have m1 (h0 : 'rV[RT]_n) : true -> measurable
        (\big[setU/set0]_(t0 <- Nt (Iof s)) Ev (Iof s) h0 t0).
      by move=> _; apply: bigsetU_measurable => t0 _; exact: mEv.
    have m2 (h0 t0 : 'rV[RT]_n) : true -> measurable (Ev (Iof s) h0 t0).
      by move=> _; exact: mEv.
    apply: le_trans (mu_bigsetU_le _ _ m1) _.
    apply: (@le_trans _ _ (\sum_(h0 <- Nh (Iof s))
        ((size (Nt (Iof s)))%:R * B)%R%:E)).
      rewrite big_seq [X in (_ <= X)%E]big_seq.
      apply: lee_sum => h0 h0N; apply: le_trans (mu_bigsetU_le _ _ (m2 h0)) _.
      rewrite -csum big_seq [X in (_ <= X)%E]big_seq; apply: lee_sum => t0 t0N.
      by apply: hEv; [exact: NhS | exact: NtS].
    rewrite csum lee_fin mulrA; apply: (ler_wpM2r B0).
    by apply: ler_pM; rewrite ?ler0n ?sizeNh ?sizeNt.
  have m3 (s : m.-tuple (option 'I_n)) : true -> measurable
      (\big[setU/set0]_(h0 <- Nh (Iof s)) \big[setU/set0]_(t0 <- Nt (Iof s))
        Ev (Iof s) h0 t0).
    move=> _; apply: bigsetU_measurable => h0' _.
    by apply: bigsetU_measurable => t0 _; exact: mEv.
  apply: le_trans (mu_bigsetU_le _ _ m3) _.
  apply: le_trans (lee_sum _ (fun s _ => inner s)) _.
  rewrite sumEFin sumr_const card_tuple card_option card_ord lee_fin.
  rewrite -/Hm -/T -/B -[X in (X <= _)%R]mulr_natl natrX !mulrA.
  exact: lexx.
- move=> x hA hN hG [I [h [t [Im hhd htl hsmall]]]].
  have [s sI] := tuple_of_set Im.
  have [NhS Nhnet _] := NhP I; have [NtS Ntnet _] := NtP I.
  have [h0 h0N hh0] := Nhnet h hhd.
  have [t0 t0N tt0] := Ntnet t htl.
  have g0 : (gam != 0)%R by rewrite gt_eqF.
  have s0 : (Num.sqrt d%:R != 0 :> RT)%R by rewrite gt_eqF.
  have c1 : (C1 != 0)%R by rewrite gt_eqF.
  apply: bigsetU_seqP; exists s; first exact: mem_index_enum.
  rewrite /Iof sI.
  apply: bigsetU_seqP; exists h0 => //.
  apply: bigsetU_seqP; exists t0 => //.
  move=> l /= lL; split; last exact: hG I t0 Im (NtS t0 t0N) l lL.
  apply/dual_ballP; first by rewrite mulr_ge0 ?ler0n // mulr_ge0 // ltW.
  have Ui := @blk_cU_inj L d l; have Ji := @blk_cJ_inj L d l.
  pose S lam := stage_map (blk_cU L d l) (blk_cJ L d l) x lam.
  have tri a b c : (nuclear (S (a + (b + c))) <=
      nuclear (S a) + nuclear (S b) + nuclear (S c))%R.
    rewrite /S stage_mapD; apply: le_trans (nuclearD _ _) _.
    by rewrite -addrA lerD2l stage_mapD; exact: nuclearD.
  have e : (h0 + t0 = (h + t) + ((h0 - h) + (t0 - t)))%R.
    by apply/rowP => i; rewrite !mxE; ring.
  have b1 := hsmall l lL.
  have b2 : (nuclear (S (h0 - h)) <= gam * d%:R / 4)%R.
    apply: le_trans (@nuclear_stage_map_l1 RT n d _ _ (blk_cU L d l)
      (blk_cJ L d l) x (h0 - h)%R (2 * d%:R)%R Ui Ji hN) _.
    rewrite -opprB l1normN.
    apply: le_trans (ler_wpM2l _ hh0) _.
      by rewrite mulr_ge0 ?invr_ge0 ?sqrtr_ge0 // mulr_ge0 ?ler0n.
    by rewrite /eh le_eqVlt; apply/orP; left; apply/eqP; field.
  have b3 : (nuclear (S (t0 - t)) <= gam * d%:R / 4)%R.
    apply: le_trans (hA l (t0 - t)%R lL) _.
    rewrite -opprB frobeniusN.
    apply: le_trans (ler_wpM2l _ tt0) _.
      by rewrite mulr_ge0 ?ler0n // ltW.
    by rewrite /et le_eqVlt; apply/orP; left; apply/eqP; field.
  rewrite -/(S (h0 + t0)%R) e; apply: le_trans (tri _ _ _) _.
  have := ltW b1; rewrite -/(S (h + t)%R) => b1'.
  have gd : (0 <= gam * d%:R)%R by rewrite mulr_ge0 ?ler0n // ltW.
  rewrite -mulrA; lra.
Qed.

End light_union.

Section light_count.
Context {RT : realType}.

Lemma pow_expR (y : RT) (N : nat) : 0 < y -> y ^+ N = expR (N%:R * ln y).
Proof. by move=> y0; rewrite expRM_natl lnK // posrE. Qed.

(* The choice of gamma: 2 C gam <= 1 and the coefficient of d^2 in the
   exponent of the union bound is at most -2. *)
Lemma light_gamma (alpha a C C1 : RT) : 0 < alpha -> alpha < a -> 0 < C ->
  0 < C1 -> exists gam : RT, [/\ 0 < gam, gam <= 1, gam <= C1,
    2 * C * gam <= 1 &
    2 <= a * (- ln (2 * C * gam)) -
      ((alpha + a) / 2) * ln (2 * expR 1 * (1 + 8 * C1 / gam))].
Proof.
move=> a0 aa C0 C10.
have a0' : 0 < a by apply: lt_trans aa.
pose b := (alpha + a) / 2.
pose K' := a * ln (2 * C) + b * ln (18 * expR 1 * C1).
pose Q := 2 * (2 + `|K'|) / (a - alpha).
pose gam := Num.min (Num.min 1 C1) (Num.min (2 * C)^-1 (expR (- Q))).
have C2 : 0 < 2 * C by rewrite mulr_gt0.
have g0 : 0 < gam.
  by rewrite !lt_min ltr01 C10 invr_gt0 C2 expR_gt0.
have g1 : gam <= 1 by rewrite !ge_min lexx.
have gC1 : gam <= C1 by rewrite !ge_min lexx orbT.
have g2 : gam <= (2 * C)^-1 by rewrite !ge_min lexx !orbT.
have gQ : gam <= expR (- Q) by rewrite !ge_min lexx !orbT.
have b0 : 0 <= b by rewrite /b divr_ge0 // addr_ge0 // ltW.
have ab : a - b = (a - alpha) / 2 by rewrite /b; field.
have lng : Q <= - ln gam.
  rewrite lerNr -[- Q]expRK ler_ln ?posrE ?expR_gt0 //.
exists gam; split => //.
  apply: (le_trans (ler_wpM2l (ltW C2) g2)).
  by rewrite mulfV ?(gt_eqF C2).
have e1 : ln (2 * C * gam) = ln (2 * C) + ln gam by rewrite lnM ?posrE.
have T1 : 2 * expR 1 * (1 + 8 * C1 / gam) <= 18 * expR 1 * C1 / gam.
  have : 1 <= C1 / gam by rewrite ler_pdivlMr // mul1r.
  have := expR_gt0 (1 : RT); move=> e0 h.
  have -> : 18 * expR 1 * C1 / gam = 2 * expR 1 * (9 * (C1 / gam)) by ring.
  by apply: ler_wpM2l; rewrite ?mulr_ge0 ?(ltW e0) //; lra.
have e0 := expR_gt0 (1 : RT).
have pT : 0 < 2 * expR 1 * (1 + 8 * C1 / gam).
  by rewrite !mulr_gt0 // addr_gt0 // divr_gt0 // mulr_gt0.
have p18 : 0 < 18 * expR 1 * C1 by rewrite !mulr_gt0.
have pq : 0 < 18 * expR 1 * C1 / gam by rewrite divr_gt0.
have lnT : ln (2 * expR 1 * (1 + 8 * C1 / gam)) <=
    ln (18 * expR 1 * C1) - ln gam.
  by rewrite -ln_div ?posrE // ler_ln ?posrE.
have aa' : a - alpha != 0 by rewrite subr_eq0 (gt_eqF aa).
have aQ : (a - alpha) / 2 * Q = 2 + `|K'| by rewrite /Q; field.
rewrite e1.
have := ler_wpM2l b0 lnT.
have h2' : 0 <= (a - alpha) / 2 by rewrite divr_ge0 // ltW // subr_gt0.
have := ler_wpM2l h2' lng.
rewrite aQ => h1 h2.
have := ler_norm K'; rewrite /K' => hK.
rewrite /b in h2 hK *.
nra.
Qed.

(* The bound of light_union is at most expR (- d) for every large d, when
   n <= ((alpha + a) / 2) d^2, m <= C0 d ln d, r <= d and the exponent
   sum_l k_l q_l is at least a (d - L)^2, for gam as in light_gamma. *)
Lemma light_count (alpha a C C1 gam C0 : RT) (L : nat) :
  0 < alpha -> alpha < a -> a <= 1 / 2 -> 0 < C -> 0 < C1 -> 0 < gam ->
  2 * C * gam <= 1 ->
  2 <= a * (- ln (2 * C * gam)) -
    ((alpha + a) / 2) * ln (2 * expR 1 * (1 + 8 * C1 / gam)) ->
  0 < C0 ->
  exists D : nat, forall (d n m : nat) (r : RT) (k : nat -> nat),
    (D <= d)%N -> n%:R <= (alpha + a) / 2 * d%:R ^+ 2 ->
    m%:R <= C0 * d%:R * ln d%:R -> 0 <= r -> r <= d%:R ->
    a * (d%:R - L%:R) ^+ 2 <= (\sum_(l < L.-1) k l * blk_q L d l)%N%:R ->
    (n.+1)%:R ^+ m *
    (2 * expR 1 * (1 + 16 * r * Num.sqrt (m.+1)%:R /
       (gam * Num.sqrt d%:R))) ^+ m *
    (2 * expR 1 * (1 + 8 * C1 / gam)) ^+ n *
    \prod_(l < L.-1) (C * (2 * gam)) ^+ (k l * blk_q L d l) <=
    expR (- d%:R).
Proof.
move=> al0 aa a12 C0' C10 g0 g2 hg C00.
have a0 : 0 < a by apply: lt_trans aa.
set b := (alpha + a) / 2.
set Lam := - ln (2 * C * gam).
set T := 2 * expR 1 * (1 + 8 * C1 / gam).
have e0 := expR_gt0 (1 : RT).
have e2 : 2 <= expR 1 :> RT by have := expR_ge1Dx (1 : RT); lra.
have T1 : 1 <= T.
  have : 0 <= 8 * C1 / gam.
    by apply: divr_ge0; [apply: mulr_ge0; [exact: ler0n|exact: ltW]|exact: ltW].
  by rewrite /T; nra.
have lnT0 : 0 <= ln T := ln_ge0 T1.
have Cg0 : 0 < 2 * C * gam by rewrite !mulr_gt0.
have Lam0 : 0 <= Lam by rewrite /Lam oppr_ge0 ln_le0.
have b0 : 0 <= b by rewrite /b divr_ge0 // addr_ge0 // ltW.
have b1 : b <= 1 / 2 by rewrite /b; lra.
pose cH := 2 * expR 1 * (1 + 16 * Num.sqrt (C0 + 1) / gam).
have cH1 : 1 <= cH.
  have : 0 <= 16 * Num.sqrt (C0 + 1) / gam.
    apply: divr_ge0; last exact: ltW.
    by apply: mulr_ge0; [exact: ler0n|exact: sqrtr_ge0].
  by rewrite /cH; nra.
have lncH0 : 0 <= ln cH := ln_ge0 cH1.
pose c2 := 4 * C0 * (1 + ln cH) + 64 * C0.
have c20 : 0 <= c2.
  have h4 : 0 <= 4 * C0 by apply: mulr_ge0; [exact: ler0n|exact: ltW].
  have h64 : 0 <= 64 * C0 by apply: mulr_ge0; [exact: ler0n|exact: ltW].
  by rewrite /c2; apply: addr_ge0 => //; apply: mulr_ge0 => //; lra.
pose X := 4 * c2 ^+ 2 + 2 * (2 * a * L%:R * Lam + 1) + 1.
exists (truncn X).+1 => d n m r k dD hn hm r0 rd hN.
set x := d%:R.
have xX : X < x.
  apply: lt_le_trans (truncnS_gt X) _; rewrite /x ler_nat; exact: dD.
have X1 : 1 <= X.
  have : 0 <= 2 * a * L%:R * Lam by rewrite !mulr_ge0 ?ler0n // ltW.
  by rewrite /X; have := sqr_ge0 c2; lra.
have x1 : 1 <= x by apply: le_trans (ltW xX).
have x0 : 0 < x by apply: lt_le_trans x1.
set lam := ln x.
have lam0 : 0 <= lam := ln_ge0 x1.
have lamx : lam <= x := ltW (ln_sublinear x0).
set y := Num.sqrt (Num.sqrt x).
have sx1 : 1 <= Num.sqrt x by rewrite -sqrtr1 ler_wsqrtr.
have y1 : 1 <= y by rewrite /y -sqrtr1 ler_wsqrtr.
have y0 : 0 < y by apply: lt_le_trans y1.
have yy : y ^+ 2 = Num.sqrt x by rewrite /y sqr_sqrtr // sqrtr_ge0.
have sxsx : Num.sqrt x ^+ 2 = x by rewrite sqr_sqrtr // ltW.
have y4 : y ^+ 4 = x by rewrite (_ : 4 = 2 * 2)%N // exprM yy sxsx.
have lamy : lam <= 4 * y.
  rewrite /lam -y4 lnXn // [4 * y]mulr_natl lerMn2r; apply/orP; right.
  exact: ltW (ln_sublinear y0).
have ysx : y <= Num.sqrt x by rewrite -yy; nra.
have sxx : Num.sqrt x <= x by rewrite -{2}sxsx; nra.
(* the first factor *)
have n1 : 0 < (n.+1)%:R :> RT := ltr0Sn _ _.
have hn1 : (n.+1)%:R <= 2 * x ^+ 2.
  rewrite -addn1 natrD; have : 1 <= x ^+ 2 by nra.
  by have := hn; rewrite -/b; nra.
have ln2 : ln 2 <= 1 :> RT.
  by rewrite -[X in _ <= X](expRK 1) ler_ln ?posrE ?expR_gt0.
have lnn : ln (n.+1)%:R <= 1 + 2 * lam.
  have h : ln (n.+1)%:R <= ln (2 * x ^+ 2).
    by rewrite ler_ln ?posrE // mulr_gt0 // exprn_gt0.
  apply: le_trans h _; rewrite lnM ?posrE ?exprn_gt0 // lnXn // -/lam.
  by rewrite mulr2n; lra.
(* the second factor *)
set H := 2 * expR 1 * (1 + 16 * r * Num.sqrt (m.+1)%:R / (gam * Num.sqrt x)).
set sC := Num.sqrt (C0 + 1).
have sC0 : 0 <= sC := sqrtr_ge0 _.
have sm0 : 0 <= Num.sqrt (m.+1)%:R := sqrtr_ge0 _.
have q0 : 0 <= 16 * r * Num.sqrt (m.+1)%:R / (gam * Num.sqrt x).
  apply: divr_ge0; last by apply: mulr_ge0; [exact: ltW|exact: sqrtr_ge0].
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ler0n.
have H1 : 1 <= H by rewrite /H; nra.
have m1 : (m.+1)%:R <= (C0 + 1) * x ^+ 2.
  rewrite -addn1 natrD.
  have : C0 * x * lam <= C0 * x * x.
    by apply: ler_wpM2l => //; apply: mulr_ge0; [exact: ltW|exact: ltW].
  have : 1 <= x ^+ 2 by nra.
  by have := hm; rewrite -/x -/lam; nra.
have sm : Num.sqrt (m.+1)%:R <= sC * x.
  apply: le_trans (ler_wsqrtr m1) _.
  have hs : Num.sqrt (x ^+ 2) = x by rewrite sqrtr_sqr ger0_norm // ltW.
  have hc : 0 <= C0 + 1 by have := C00; lra.
  by rewrite (sqrtrM _ hc) hs.
have g0' : gam != 0 by rewrite gt_eqF.
have sx0' : Num.sqrt x != 0 by rewrite gt_eqF // sqrtr_gt0.
have qb : 16 * r * Num.sqrt (m.+1)%:R / (gam * Num.sqrt x) <=
    16 * sC / gam * x ^+ 2.
  have gx : 0 < gam * Num.sqrt x by rewrite mulr_gt0 // sqrtr_gt0.
  rewrite ler_pdivrMr //.
  have -> : 16 * sC / gam * x ^+ 2 * (gam * Num.sqrt x) =
      16 * (sC * x ^+ 2 * Num.sqrt x) by field.
  have h1 : r * Num.sqrt (m.+1)%:R <= x * (sC * x).
    by apply: ler_pM.
  have h2 : sC * x ^+ 2 <= sC * x ^+ 2 * Num.sqrt x.
    by rewrite ler_peMr // mulr_ge0 // exprn_ge0 // ltW.
  have hAB : r * Num.sqrt (m.+1)%:R <= sC * x ^+ 2 * Num.sqrt x.
    by apply: le_trans h1 _; rewrite mulrCA -expr2.
  rewrite -mulrA; lra.
have Hx : H <= cH * x ^+ 2.
  have hq : 1 + 16 * r * Num.sqrt (m.+1)%:R / (gam * Num.sqrt x) <=
      (1 + 16 * sC / gam) * x ^+ 2.
    have : 1 <= x ^+ 2 by nra.
    by rewrite mulrDl mul1r; lra.
  have e2' : 0 <= 2 * expR 1 :> RT by lra.
  apply: le_trans (ler_wpM2l e2' hq) _.
  by rewrite /cH -/sC mulrA.
have H0 : 0 < H by apply: lt_le_trans H1.
have lnH : ln H <= ln cH + 2 * lam.
  have h : ln H <= ln (cH * x ^+ 2).
    by rewrite ler_ln ?posrE // mulr_gt0 ?exprn_gt0 // (lt_le_trans ltr01).
  apply: le_trans h _; rewrite lnM ?posrE ?exprn_gt0 ?(lt_le_trans ltr01) //.
  by rewrite lnXn // -/lam mulr2n; lra.
(* the third and fourth factors *)
have T0 : 0 < T by apply: lt_le_trans T1.
set N := (\sum_(l < L.-1) k l * blk_q L d l)%N.
have e4 : \prod_(l < L.-1) (C * (2 * gam)) ^+ (k l * blk_q L d l) =
    (2 * C * gam) ^+ N.
  by rewrite (_ : C * (2 * gam) = 2 * C * gam) ?prodrXr //; ring.
rewrite e4 (pow_expR _ n1) (pow_expR _ H0) (pow_expR _ T0) (pow_expR _ Cg0).
rewrite -!expRD ler_expR.
have E1 : m%:R * ln (n.+1)%:R <= m%:R * (1 + 2 * lam).
  by apply: ler_wpM2l => //; exact: ler0n.
have E2 : m%:R * ln H <= m%:R * (ln cH + 2 * lam).
  by apply: ler_wpM2l => //; exact: ler0n.
have E3 : n%:R * ln T <= b * x ^+ 2 * ln T.
  by apply: ler_wpM2r.
have E4 : N%:R * ln (2 * C * gam) <= - (a * (x - L%:R) ^+ 2 * Lam).
  rewrite -[ln _]opprK -/Lam mulrN lerN2; apply: ler_wpM2r => //.
have lamsx : lam <= 4 * Num.sqrt x by lra.
have lam2 : lam * lam <= 16 * Num.sqrt x by rewrite -yy; nra.
have F1 : m%:R * (1 + 2 * lam) + m%:R * (ln cH + 2 * lam) <=
    c2 * (x * Num.sqrt x).
  have hm' : m%:R * (1 + ln cH + 4 * lam) <=
      C0 * x * lam * (1 + ln cH + 4 * lam).
    by apply: ler_wpM2r; [lra|rewrite -/x -/lam].
  have p1 : 0 <= C0 * x * (1 + ln cH).
    by apply: mulr_ge0; [apply: mulr_ge0; apply: ltW|lra].
  have l1 : C0 * x * (1 + ln cH) * lam <=
      C0 * x * (1 + ln cH) * (4 * Num.sqrt x) by exact: ler_wpM2l.
  have p2 : 0 <= 4 * C0 * x by apply: mulr_ge0; [lra|exact: ltW].
  have l2 : 4 * C0 * x * (lam * lam) <= 4 * C0 * x * (16 * Num.sqrt x).
    exact: ler_wpM2l.
  rewrite /c2; nra.
have F2 : b * x ^+ 2 * ln T - a * (x - L%:R) ^+ 2 * Lam <=
    - 2 * x ^+ 2 + 2 * a * L%:R * Lam * x.
  have pL : 0 <= a * L%:R ^+ 2 * Lam.
    by apply: mulr_ge0 => //; apply: mulr_ge0; [exact: ltW|exact: exprn_ge0].
  have px : 0 <= x ^+ 2 := exprn_ge0 _ (ltW x0).
  have hg' : 2 <= a * Lam - b * ln T by move: hg; rewrite -/b -/Lam -/T.
  nra.
have pa : 0 <= 2 * a * L%:R * Lam.
  by apply: mulr_ge0 => //; apply: mulr_ge0; [lra|exact: ler0n].
have c2s : 2 * c2 <= Num.sqrt x.
  have h : (2 * c2) ^+ 2 <= x by rewrite /X in xX; nra.
  have h2c : 0 <= 2 * c2 by lra.
  by rewrite -(ger0_norm h2c) -sqrtr_sqr ler_wsqrtr.
have sxsx' : Num.sqrt x * Num.sqrt x = x by rewrite -expr2 sxsx.
have F3 : c2 * (x * Num.sqrt x) <= x ^+ 2 / 2.
  have p3 : 0 <= x * Num.sqrt x.
    by apply: mulr_ge0; [exact: ltW|exact: sqrtr_ge0].
  nra.
have F4 : 2 * a * L%:R * Lam * x + x <= x ^+ 2 / 2.
  have h : 2 * (2 * a * L%:R * Lam + 1) <= x.
    by rewrite /X in xX; have := sqr_ge0 c2; nra.
  nra.
have px : 0 <= x ^+ 2 := exprn_ge0 _ (ltW x0).
lra.
Qed.

End light_count.
