(* Proposition 3.4 of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 2436-2450, proof lines
   3610-3805 of arxiv_v1.tex): the light-tail quotient-norm lower bound.
   Item S9 of stage 3 of phase 5 (lane B). The parts that do not depend on
   other items are proved, over any realType; the assembly comes next.

   Statement. Let x_1, ..., x_n be the points of a sample whose coordinates
   are independent with laws universality_coordinate_law kappa K0, and let
   n / d^2 tend to alpha in (0, 1/2). There are K > 0 and gamma > 0,
   depending only on alpha and K0, such that for every C0 > 0, with
   probability tending to one: for every set I of at most C0 d ln d rows,
   every t with t_i = 0 on I and |t|_oo <= (K d)^(-1/2) |t|_2, and every h
   with h_i = 0 outside I and |h|_1 <= d^(2/3) |t|_2, the nuclear norm of
   L_X^* (h + t) = d^(-1/2) sum_i (h + t)_i (x_i x_i^T - I) is at least
   gamma d |t|_2.

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
   Inputs of lane C (requests/b-to-c.md): Corollary 3.13 in the form of the
   sorted eigenvalues, and Proposition 3.1 (iii).

   Proved so far:
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
     and c0. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear interval.
From mathcomp Require Import boolp classical_sets cardinality reals Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability.
From mathcomp Require Import measurable_realfun measurable_fun_approximation.
From GaussianAnalysis Require Import measurable_matrix.
From GaussianAnalysis Require Import euclidean opnorm real_spectral von_neumann.
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
