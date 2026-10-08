(* Lemma 3.14 of Koehler and Sohn, "Universality and sharp thresholds for
   ellipsoid fitting" (arXiv 2608.27372, lines 3475-3608 of arxiv_v1.tex):
   the one-stage small-ball bound of the sequential block revealing of
   Proposition 3.4. Everything is stated over any realType; Stdlib's R is
   one of them.

   Setting. A sample is an (n d)-tuple x of coordinates, read as n points
   of R^d: coordinate j of point i is x_(i d + j) (sample_entry). A stage
   is given by two lists of columns, the revealed columns cU : 'I_p -> 'I_d
   (the paper's U_l) and the fresh columns cJ : 'I_q -> 'I_d (the paper's
   I_l), none of which is revealed, and by a set I of revealed rows (the
   support of the head). For a point i, u_i = (x_(i, cU a))_a and
   v_i = (x_(i, cJ b))_b (stage_row), and for lambda in R^n the p x q
   matrix
     stage_map x lambda = d^(-1/2) sum_i lambda_i u_i^T v_i
   is the paper's L*_(X, l) lambda, the U_l x I_l block of L*_X lambda.
   The revealed coordinates (stage_revealed) are those of the rows in I and
   those of the columns cU; they generate the paper's sigma-algebra
   F^I_(l-1). Conditioning on F^I_(l-1) is resampling the other
   coordinates (tuple_merge, library/probability/conditioning.v).

   The nuclear-norm ball of radius r is written by duality: dual_ball r is
   the set of the matrices A with <A, C> <= r opnorm C for every C.

   Main results:
   - measurable_dual_ball: the dual ball is closed, hence measurable.
   - stage_map_merge: for a tail t that vanishes on I, after resampling,
     Q stage_map t is the matrix colsum_mx (library/matrix/covering.v) of
     the fresh coordinates y_(i, cJ j) with the weights
     w_i = d^(-1/2) t_i u_i Q^T.
   - stage_small_ball_flat (Lemma 3.14, conditional form): for a sample
     with independent coordinates, coordinate k of law lam k of mean 0,
     variance 1 and E[x^2 1_(|x| <= M)] >= 1/2, there is a constant C
     depending only on M, mu and c0 such that the following holds. Let x0
     be the revealed coordinates, t a tail that vanishes on I, and Q an
     m x p matrix with orthonormal rows (the paper's isometry of V_(t, l)
     onto R^m) with
       mu |y|^2 <= sum_i t_i^2 <y, u_i Q^T>^2 for every y in R^m
     (the paper's P_V Sigma_(t, l) P_V >= mu P_V),
       |t_i| |u_i| <= rho for every i, and
       c0 d <= m, c0 d <= q, m <= d.
     Then for every gam >= C rho and every p x q matrix B, the resampled
     matrix stage_map t + B is in the dual ball of radius gam d with
     probability at most (C gam)^(m q). The laws may differ from one
     point to another: the fresh coordinates of a column, one for each
     point, have the laws lam (i d + cJ j), and the vector small-ball
     bound takes laws that vary with the index.
   - stage_small_ball: the same when coordinate j of every point has law
     nu j, the setting of the paper.
   The proof is the paper's. The projection by Q maps the dual ball of the
   p x q matrices into that of the m x q matrices. matrix_small_ball
   covers the latter by exp (48 (m + q) d + 33) <= C^(m q) products of
   column balls of radius gam, and the columns of Q stage_map t are
   independent sums sum_i y_(i, cJ j) w_i, each in a ball of radius gam
   with probability at most (C gam)^m by vector_small_ball_moments
   (library/fourier/small_ball.v) applied to the whitened weights
   (d / mu)^(1/2) w_i. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import interval ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype exp sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import lindeberg tuple_rows conditioning.
From GaussianAnalysis Require Import covering small_ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section dual_ball.
Context {RT : realType}.

(* The matrices of nuclear norm at most r, by duality with opnorm. *)
Definition dual_ball m q (r : RT) : set 'M[RT]_(m, q) :=
  [set A | forall C, mxdot A C <= r * opnorm C].
Arguments dual_ball {m q} r.

Lemma closed_dual_ball m q (r : RT) : closed (@dual_ball m q r).
Proof.
have sumc (T : topologicalType) k (f : 'I_k -> T -> RT) :
    (forall i, continuous (f i)) -> continuous (fun x => \sum_(i < k) f i x).
  elim: k f => [|k IH] f hf.
    by under eq_fun do rewrite big_ord0; exact: cst_continuous.
  have -> : (fun x => \sum_(i < k.+1) f i x) =
      (fun x => \sum_(i < k) f (widen_ord (leqnSn k) i) x + f ord_max x).
    by apply/funext => x; rewrite big_ord_recr.
  move=> x; apply: (@continuousD _ _ _
    (fun x => \sum_(i < k) f (widen_ord (leqnSn k) i) x) (f ord_max) x).
    exact: IH.
  exact: hf.
have cont C : continuous (fun A : 'M[RT]_(m, q) => mxdot A C).
  rewrite /mxdot; apply: (sumc _ m) => i; apply: (sumc _ q) => j A.
  apply: (@continuousM _ _ (fun A : 'M[RT]_(m, q) => A i j) (fun=> C i j)).
    exact: coord_continuous.
  exact: cst_continuous.
rewrite (_ : @dual_ball m q r = \bigcap_(C in setT)
    ((fun A => mxdot A C) @^-1` [set x | x <= r * opnorm C])).
  apply/seteqP; split => A /= h C; last exact: h.
  by move=> _; exact: h.
apply: closed_bigI => C _; apply: preimage_closed; last exact: closed_le.
by move=> A _; exact: cont.
Qed.

Lemma measurable_dual_ball m q (r : RT) : measurable (@dual_ball m q r).
Proof.
rewrite -[@dual_ball m q r]setCK; apply: measurableC.
apply: open_measurable_mx; rewrite openC.
exact: closed_dual_ball.
Qed.

(* A matrix Q with orthonormal rows: Q^T is an isometry, Q a contraction. *)
Lemma opnorm_trmx_orthorows m p (Q : 'M[RT]_(m, p)) :
  Q *m Q^T = 1%:M -> opnorm Q^T <= 1.
Proof.
move=> QQ; apply: opnorm_le => x x1; apply: le_trans x1.
rewrite /frobenius ler_sqrt ?mxdot_ge0 // mxdot_mulmxl trmxK mulmxA QQ.
by rewrite mul1mx.
Qed.

Lemma frobenius_mulmx_orthorows m p (Q : 'M[RT]_(m, p)) (u : 'rV[RT]_p) :
  Q *m Q^T = 1%:M -> frobenius (u *m Q^T) <= frobenius u.
Proof.
move=> QQ; rewrite -frobenius_trmx trmx_mul trmxK.
apply: le_trans (frobenius_mulmx_opnorm _ _) _.
rewrite frobenius_trmx -[leRHS]mul1r ler_wpM2r ?frobenius_ge0 //.
by rewrite -opnorm_trmx; exact: opnorm_trmx_orthorows.
Qed.

(* Projecting by a matrix with orthonormal rows keeps the dual ball. *)
Lemma dual_ball_mulmx m p q (Q : 'M[RT]_(m, p)) (r : RT) (A : 'M[RT]_(p, q)) :
  0 <= r -> Q *m Q^T = 1%:M -> dual_ball r A -> dual_ball r (Q *m A).
Proof.
move=> r0 QQ hA C; rewrite mxdot_mulmxl; apply: le_trans (hA _) _.
apply: ler_wpM2l => //; apply: le_trans (opnorm_mulmx _ _) _.
rewrite -[leRHS]mul1r ler_wpM2r ?opnorm_ge0 //.
exact: opnorm_trmx_orthorows.
Qed.

End dual_ball.

(* Coordinate k of a sample of n points of R^d is a coordinate of a point,
   k mod d. *)
Lemma ltn_mod_mul n d k : (k < n * d)%N -> (k %% d < d)%N.
Proof. by case: d => [|d]; rewrite ?muln0 ?ltn0 // ltn_pmod. Qed.

Lemma row_index_inj n d (i i' : 'I_n) (j j' : 'I_d) :
  row_index i j = row_index i' j' -> i = i' /\ j = j'.
Proof.
move=> /(congr1 (@nat_of_ord _)) /= e.
have dp : (0 < d)%N by apply: leq_ltn_trans (ltn_ord j).
have ej : (j : nat) = j'.
  by move: (congr1 (modn^~ d) e); rewrite !modnMDl !modn_small.
split; last exact: val_inj.
apply: val_inj => /=; move: e; rewrite ej => /addIn /eqP.
by rewrite eqn_pmul2r // => /eqP.
Qed.

Section stage.
Context {RT : realType}.
Local Notation sample n d := ((n * d)%N.-tuple (measurableTypeR RT)).

(* Coordinate j of point i. *)
Definition sample_entry n d (x : sample n d) (i : 'I_n) (j : 'I_d) : RT :=
  tnth x (row_index i j).

(* The coordinates of point i in the columns c. *)
Definition stage_row n d p (c : 'I_p -> 'I_d) (x : sample n d) (i : 'I_n) :
    'rV[RT]_p :=
  \row_a sample_entry x i (c a).

(* The block of the columns cU and cJ of d^(-1/2) sum_i lam_i x_i x_i^T. *)
Definition stage_map n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (x : sample n d) (lam : 'rV[RT]_n) : 'M[RT]_(p, q) :=
  (Num.sqrt d%:R)^-1 *:
    \sum_(i < n) lam 0 i *: ((stage_row cU x i)^T *m stage_row cJ x i).

(* The coordinates of the rows in I and of the columns cU. *)
Definition stage_revealed n d p (cU : 'I_p -> 'I_d) (I : {pred 'I_n}) :
    {pred 'I_(n * d)} :=
  [pred k | [exists i, [exists j, (k == row_index i j) &&
     ((i \in I) || [exists a, cU a == j])]]].

Lemma stage_revealedE n d p (cU : 'I_p -> 'I_d) (I : {pred 'I_n})
    (i : 'I_n) (j : 'I_d) :
  (row_index i j \in stage_revealed cU I) =
  (i \in I) || [exists a, cU a == j].
Proof.
rewrite inE /=; apply/existsP/idP => [[i' /existsP [j' /andP [/eqP e h]]]|h].
  by have [-> ->] := row_index_inj e.
by exists i; apply/existsP; exists j; rewrite eqxx.
Qed.

(* The weights of the fresh coordinates in Q stage_map t. *)
Definition stage_weight n d p m (cU : 'I_p -> 'I_d) (Q : 'M[RT]_(m, p))
    (x : sample n d) (t : 'rV[RT]_n) (k : nat) : 'rV[RT]_m :=
  if insub k is Some i then
    ((Num.sqrt d%:R)^-1 * t 0 i) *: (stage_row cU x i *m Q^T)
  else 0.

Lemma stage_map_merge n d p q m (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (I : {pred 'I_n}) (Q : 'M[RT]_(m, p)) (t : 'rV[RT]_n)
    (x0 y : sample n d) :
  (forall a b, cU a != cJ b) -> (forall i, i \in I -> t 0 i = 0) ->
  Q *m stage_map cU cJ (tuple_merge (stage_revealed cU I) x0 y) t =
  colsum_mx (fun i j => row_index i (cJ j)) (stage_weight cU Q x0 t) y.
Proof.
move=> hUJ ht; apply/matrixP => a j; rewrite !mxE.
set X := tuple_merge (stage_revealed cU I) x0 y.
(* the revealed columns of X are those of x0, its fresh columns those of y
   outside the rows of I *)
have hX i b : tnth X (row_index i (cU b)) = tnth x0 (row_index i (cU b)).
  rewrite /X tnth_merge stage_revealedE; case: ifPn => // /negP [].
  by apply/orP; right; apply/existsP; exists b.
have hY i : i \notin I ->
    tnth X (row_index i (cJ j)) = tnth y (row_index i (cJ j)).
  move=> iI; rewrite /X tnth_merge stage_revealedE (negbTE iI) /=.
  have -> : [exists a, cU a == cJ j] = false.
    by apply/existsP => -[b /eqP h]; move: (hUJ b j); rewrite h eqxx.
  by [].
have hS b : stage_map cU cJ X t b j = (Num.sqrt d%:R)^-1 *
    \sum_(i < n) t 0 i * (tnth x0 (row_index i (cU b)) *
      tnth X (row_index i (cJ j))).
  rewrite /stage_map !mxE summxE; congr (_ * _); apply: eq_bigr => i _.
  by rewrite !mxE big_ord1 !mxE /sample_entry hX.
under eq_bigr do rewrite hS mulr_sumr mulr_sumr.
rewrite exchange_big /=; apply: eq_bigr => i _.
rewrite /stage_weight valK !mxE.
have [iI|iI] := boolP (i \in I).
  rewrite ht // mulr0 mul0r mulr0.
  by apply: big1 => b _; rewrite !(mul0r, mulr0).
rewrite hY // mulr_sumr mulr_sumr; apply: eq_bigr => b _.
by rewrite !mxE /sample_entry; ring.
Qed.

Lemma measurable_stage_map n d p q (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (t : 'rV[RT]_n) :
  measurable_fun setT (fun x : sample n d => stage_map cU cJ x t).
Proof.
apply/measurable_fun_mxP => b j.
rewrite (_ : (fun x => _) = (fun x : sample n d => (Num.sqrt d%:R)^-1 *
    \sum_(i < n) t 0 i * (tnth x (row_index i (cU b)) *
      tnth x (row_index i (cJ j))))).
  apply/funext => x; rewrite /stage_map !mxE summxE; congr (_ * _).
  by apply: eq_bigr => i _; rewrite !mxE big_ord1 !mxE.
apply: measurable_funM => //; apply: measurable_sum => i.
apply: measurable_funM => //.
by apply: measurable_funM; exact: measurable_tnth.
Qed.

(* The constants of Lemma 3.14: the size of the covering and the small-ball
   probabilities of the columns. *)
Lemma stage_small_ball_arith (c0 mu Cv gam : RT) (m q d : nat) :
  0 < c0 -> 0 < mu -> 0 < Cv -> 0 < gam -> (0 < m)%N -> (0 < q)%N ->
  c0 * d%:R <= m%:R -> c0 * d%:R <= q%:R ->
  expR (48 * (m + q)%:R * d%:R + 33) *
    (Cv * (Num.sqrt (d%:R / mu) * gam / Num.sqrt m%:R)) ^+ m ^+ q <=
  (expR (96 / c0 + 33) * (Cv / Num.sqrt (mu * c0)) * gam) ^+ (m * q).
Proof.
move=> c00 mu0 Cv0 gam0 m0 q0 hm hq.
have mR : 0 < m%:R :> RT by rewrite ltr0n.
have qR : 0 < q%:R :> RT by rewrite ltr0n.
have d0 : 0 <= d%:R :> RT by rewrite ler0n.
(* the covering: 48 (m + q) d + 33 <= (96 / c0 + 33) m q *)
have key : c0 * d%:R * (m + q)%:R <= 2 * (m%:R * q%:R).
  have h1 : c0 * d%:R * m%:R <= q%:R * m%:R by rewrite ler_wpM2r // ltW.
  have h2 : c0 * d%:R * q%:R <= m%:R * q%:R by rewrite ler_wpM2r // ltW.
  rewrite natrD mulrDr; lra.
have hexp : 48 * (m + q)%:R * d%:R + 33 <= (m * q)%:R * (96 / c0 + 33).
  have mq1 : 1 <= (m * q)%:R :> RT by rewrite ler1n muln_gt0 m0.
  have h48 : 48 * (m + q)%:R * d%:R <= 96 * (m%:R * q%:R) / c0.
    by rewrite ler_pdivlMr //; lra.
  rewrite mulrDr natrM mulrA [_ * (96 : RT)]mulrC -mulrA mulrA.
  rewrite -natrM; lra.
(* the columns: (d / mu)^(1/2) gam / m^(1/2) <= gam / (mu c0)^(1/2) *)
have mu0' : 0 <= mu := ltW mu0.
have c00' : 0 <= c0 := ltW c00.
have mR' : 0 <= m%:R :> RT := ltW mR.
have heta : Num.sqrt (d%:R / mu) * gam / Num.sqrt m%:R <=
    (Num.sqrt (mu * c0))^-1 * gam.
  rewrite mulrAC ler_pM2r //.
  rewrite -(sqrtrV mR') -(sqrtrV (mulr_ge0 mu0' c00')).
  rewrite -sqrtrM ?divr_ge0 // ler_sqrt ?invr_ge0 ?mulr_ge0 //.
  have mc : 0 < mu * c0 * m%:R by rewrite !mulr_gt0.
  have mun := lt0r_neq0 mu0; have c0n := lt0r_neq0 c00.
  have mn := lt0r_neq0 mR.
  have -> : d%:R / mu * m%:R^-1 = c0 * d%:R * (mu * c0 * m%:R)^-1.
    by field.
  have -> : (mu * c0)^-1 = m%:R * (mu * c0 * m%:R)^-1 by field.
  by rewrite ler_wpM2r // invr_ge0 ltW.
have eta0 : 0 <= Num.sqrt (d%:R / mu) * gam / Num.sqrt m%:R.
  by rewrite !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 // ltW.
rewrite -exprM -[X in _ <= X ^+ _]mulrA [X in _ <= X]exprMn -expRM_natl.
apply: ler_pM.
- exact: expR_ge0.
- by rewrite exprn_ge0 // mulr_ge0 // ltW.
- by rewrite ler_expR.
apply: lerXn2r.
- by rewrite nnegrE mulr_ge0 // ltW.
- by rewrite nnegrE !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 // ltW.
rewrite -[X in _ <= X]mulrA; apply: ler_wpM2l; [exact: ltW|exact: heta].
Qed.

Local Open Scope ereal_scope.

(* Lemma 3.14, given the revealed coordinates x0, for a sample whose
   coordinate k has law lam k. *)
Theorem stage_small_ball_flat (M mu c0 : RT) : (0 < M)%R -> (0 < mu)%R ->
  (0 < c0)%R ->
  exists2 C : RT, (0 < C)%R &
  forall n d p q m (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (lam : nat -> probability (measurableTypeR RT) RT) (I : {pred 'I_n})
    (t : 'rV[RT]_n) (Q : 'M[RT]_(m, p)) (B : 'M[RT]_(p, q))
    (x0 : sample n d) (rho gam : RT),
  injective cJ -> (forall a b, cU a != cJ b) ->
  (forall k, (k < n * d)%N -> \int[lam k]_x x%:E = 0) ->
  (forall k, (k < n * d)%N -> \int[lam k]_x ((x ^+ 2)%R)%:E = 1) ->
  (forall k, (k < n * d)%N -> (2^-1)%:E <=
     \int[lam k]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E) ->
  (forall i, i \in I -> t 0 i = 0)%R ->
  (Q *m Q^T = 1%:M)%R ->
  (forall y : 'rV[RT]_m, mu * mxdot y y <=
     \sum_(i < n) (t 0 i * mxdot y (stage_row cU x0 i *m Q^T)) ^+ 2)%R ->
  (forall i, `|t 0 i| * frobenius (stage_row cU x0 i) <= rho)%R ->
  (c0 * d%:R <= m%:R)%R -> (c0 * d%:R <= q%:R)%R -> (m <= d)%N ->
  (0 < rho)%R -> (C * rho <= gam)%R ->
  tuple_prod lam (n * d)
    [set y | dual_ball (gam * d%:R)%R
       (stage_map cU cJ (tuple_merge (stage_revealed cU I) x0 y) t + B)%R]
  <= ((C * gam) ^+ (m * q))%R%:E.
Proof.
move=> M0 mu0 c00.
have [Cv Cv0 hCv] := @vector_small_ball_moments RT M M0.
pose C := Num.max Cv (expR (96 / c0 + 33) * (Cv / Num.sqrt (mu * c0)))%R.
exists C; first by rewrite lt_max Cv0.
move=> n d p q m cU cJ lam I t Q B x0 rho gam cJinj hUJ h0 h1 h2 ht QQ hcov
  hrho hm hq md rho0 hgam.
have CvC : (Cv <= C)%R by rewrite le_max lexx.
have gam0 : (0 < gam)%R.
  by apply: lt_le_trans hgam; rewrite mulr_gt0 // (lt_le_trans Cv0).
pose S := stage_revealed cU I.
pose E := [set y : sample n d | dual_ball (gam * d%:R)%R
  (stage_map cU cJ (tuple_merge S x0 y) t + B)%R].
have mE : measurable E.
  have mm : measurable_fun setT
      (fun y : sample n d => (stage_map cU cJ (tuple_merge S x0 y) t + B)%R).
    apply: measurable_addmx; last exact: measurable_cst.
    apply: measurableT_comp (measurable_stage_map cU cJ t) _.
    exact: measurableT_comp (measurable_tuple_merge S) (pair1_measurable x0).
  by have := mm measurableT _ (@measurable_dual_ball _ p q (gam * d%:R)%R);
    rewrite setTI.
rewrite -/S -/E.
have [m0|m0] := posnP m.
  by rewrite m0 mul0n expr0; exact: probability_le1.
have [q0|q0] := posnP q.
  by rewrite q0 muln0 expr0; exact: probability_le1.
have d0 : (0 < d)%N := leq_trans m0 md.
(* projected by Q, the matrix has the independent columns
   sum_i y_(i, cJ j) w_i *)
pose g (i : 'I_n) (j : 'I_q) := row_index i (cJ j).
have ginj i j i' j' : g i j = g i' j' -> i = i' /\ j = j'.
  by move=> /row_index_inj [-> /cJinj ->].
pose w := stage_weight cU Q x0 t.
pose E' := [set y : sample n d | dual_ball (gam * d%:R)%R
  (colsum_mx g w y + Q *m B)%R].
have mE' : measurable E'.
  have mm : measurable_fun setT
      (fun y : sample n d => colsum_mx g w y + Q *m B)%R.
    apply: measurable_addmx; last exact: measurable_cst.
    exact: measurable_colsum_mx.
  by have := mm measurableT _ (@measurable_dual_ball _ m q (gam * d%:R)%R);
    rewrite setTI.
have sub : E `<=` E'.
  move=> y hy; rewrite /E' /= -(stage_map_merge Q x0 y hUJ ht) -mulmxDr.
  by apply: dual_ball_mulmx => //; rewrite mulr_ge0 // ltW.
apply: le_trans (le_measure _ (mem_set mE) (mem_set mE') sub) _.
clear sub mE.
(* the small-ball probability of a column, after whitening the weights by
   s = (d / mu)^(1/2) *)
pose s := Num.sqrt (d%:R / mu).
pose eta := (s * gam / Num.sqrt m%:R)%R.
have dR : (0 < d%:R :> RT)%R by rewrite ltr0n.
have s0 : (0 < s)%R by rewrite sqrtr_gt0 divr_gt0.
have sE : (s * (Num.sqrt d%:R)^-1 = (Num.sqrt mu)^-1)%R.
  rewrite /s sqrtrM ?ler0n // sqrtrV ?ltW // mulrAC divff ?mul1r //.
  by rewrite gt_eqF // sqrtr_gt0.
clear mE' E S.
have hw (k : 'I_n) : (w k = ((Num.sqrt d%:R)^-1 * t 0 k) *:
    (stage_row cU x0 k *m Q^T))%R.
  by rewrite /w /stage_weight valK.
have etaE : (eta * Num.sqrt m%:R = s * gam)%R.
  by rewrite /eta -mulrA mulVf ?mulr1 // gt_eqF // sqrtr_gt0 ltr0n.
have hcol (j : 'I_q) (nu' : nat -> probability (measurableTypeR RT) RT) :
    (forall i : 'I_n, nu' i = lam (g i j)) -> forall z : 'rV[RT]_m,
    tuple_prod nu' n [set u | (frobenius
       (\sum_(i < n) tnth u i *: w i - z) <= gam)%R] <=
    ((Cv * eta) ^+ m)%R%:E.
  move=> hnu' z.
  have hnuj k (kn : (k < n)%N) : nu' k = lam (g (Ordinal kn) j).
    exact: (hnu' (Ordinal kn)).
  have hsc (u : n.-tuple (measurableTypeR RT)) :
      (\sum_(i < n) tnth u i *: (s *: w i) - s *: z =
       s *: (\sum_(i < n) tnth u i *: w i - z))%R.
    rewrite scalerBr scaler_sumr; congr (_ - _)%R; apply: eq_bigr => i _.
    by rewrite !scalerA mulrC.
  rewrite (_ : [set u | _] = [set u : n.-tuple (measurableTypeR RT) |
      (frobenius (\sum_(i < n) tnth u i *: (s *: w i) - s *: z) <=
       eta * Num.sqrt m%:R)%R]).
    by apply/seteqP; split => u /=;
      rewrite hsc frobeniusZ ger0_norm ?(ltW s0) // etaE ler_pM2l.
  apply: (hCv m n nu' (fun k => s *: w k) (s *: z) (rho / Num.sqrt mu)%R eta).
  - by move=> k kn; rewrite (hnuj k kn); exact: (h0 _ (ltn_ord _)).
  - by move=> k kn; rewrite (hnuj k kn); exact: (h1 _ (ltn_ord _)).
  - by move=> k kn; rewrite (hnuj k kn); exact: (h2 _ (ltn_ord _)).
  - move=> x.
    have key (k : 'I_n) : (mxdot x (s *: w k) =
        (Num.sqrt mu)^-1 * (t 0 k * mxdot x (stage_row cU x0 k *m Q^T)))%R.
      by rewrite hw !mxdotZr !mulrA -sE.
    under eq_bigr do rewrite key exprMn exprVn sqr_sqrtr ?(ltW mu0) //.
    by rewrite -mulr_sumr -(ler_pM2l mu0) mulrA divff ?mul1r ?gt_eqF.
  - by rewrite divr_gt0 // sqrtr_gt0.
  - move=> k kn.
    have hk := hrho (Ordinal kn).
    have hu := frobenius_mulmx_orthorows (stage_row cU x0 (Ordinal kn)) QQ.
    have -> : (frobenius (s *: w k) = (Num.sqrt mu)^-1 *
        (`|t 0 (Ordinal kn)| *
         frobenius (stage_row cU x0 (Ordinal kn) *m Q^T)))%R.
      rewrite (hw (Ordinal kn)) !frobeniusZ normrM mulrA.
      rewrite (ger0_norm (ltW s0)) ger0_norm ?invr_ge0 ?sqrtr_ge0 //.
      by rewrite -sE !mulrA.
    rewrite mulrC ler_wpM2r ?invr_ge0 ?sqrtr_ge0 //.
    by apply: le_trans hk; rewrite ler_wpM2l ?normr_ge0.
  have h1' : (Cv * rho <= gam)%R.
    by apply: le_trans hgam; rewrite ler_wpM2r // ltW.
  have h2' : ((Num.sqrt mu)^-1 <= s / Num.sqrt m%:R)%R.
    rewrite -sE ler_wpM2l ?(ltW s0) //.
    rewrite lef_pV2 ?posrE ?sqrtr_gt0 ?ltr0n // ler_sqrt ?ler0n //.
    by rewrite ler_nat.
  rewrite mulrA /eta [(s * gam)%R]mulrC -mulrA.
  rewrite [X in (X <= _)%R]mulrA -[X in (_ <= X)%R]mulrA.
  by apply: ler_pM => //; rewrite mulr_ge0 // ltW.
(* the covering of the dual ball of the m x q matrices *)
have r0 : (0 < gam * d%:R)%R by rewrite mulr_gt0.
have eta0 : (0 <= eta)%R.
  by rewrite /eta divr_ge0 ?sqrtr_ge0 // mulr_ge0 // ltW.
have pc0 : (0 <= (Cv * eta) ^+ m)%R by rewrite exprn_ge0 // mulr_ge0 // ltW.
have := @matrix_small_ball RT m q (n * d) n g lam w
  (Q *m B) (dual_ball (gam * d%:R)%R) (gam * d%:R)%R gam ((Cv * eta) ^+ m)%R
  ginj m0 q0 r0 gam0 pc0 (@measurable_dual_ball _ m q _) (fun A hA => hA)
  hcol.
move=> hmsb; apply: le_trans hmsb _; rewrite lee_fin.
have -> : (48 * (m + q)%:R * (gam * d%:R) / gam = 48 * (m + q)%:R * d%:R)%R.
  by have gn := lt0r_neq0 gam0; field.
apply: le_trans (stage_small_ball_arith c00 mu0 Cv0 gam0 m0 q0 hm hq) _.
apply: lerXn2r.
- by rewrite nnegrE !mulr_ge0 ?expR_ge0 ?divr_ge0 ?sqrtr_ge0 // ltW.
- by rewrite nnegrE mulr_ge0 // ?ltW // (lt_le_trans Cv0).
by rewrite ler_wpM2r ?(ltW gam0) // le_max lexx orbT.
Qed.

(* Lemma 3.14 for a sample whose coordinate j of every point has law
   nu j. *)
Theorem stage_small_ball (M mu c0 : RT) : (0 < M)%R -> (0 < mu)%R ->
  (0 < c0)%R ->
  exists2 C : RT, (0 < C)%R &
  forall n d p q m (cU : 'I_p -> 'I_d) (cJ : 'I_q -> 'I_d)
    (nu : nat -> probability (measurableTypeR RT) RT) (I : {pred 'I_n})
    (t : 'rV[RT]_n) (Q : 'M[RT]_(m, p)) (B : 'M[RT]_(p, q))
    (x0 : sample n d) (rho gam : RT),
  injective cJ -> (forall a b, cU a != cJ b) ->
  (forall j, (j < d)%N -> \int[nu j]_x x%:E = 0) ->
  (forall j, (j < d)%N -> \int[nu j]_x ((x ^+ 2)%R)%:E = 1) ->
  (forall j, (j < d)%N -> (2^-1)%:E <=
     \int[nu j]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E) ->
  (forall i, i \in I -> t 0 i = 0)%R ->
  (Q *m Q^T = 1%:M)%R ->
  (forall y : 'rV[RT]_m, mu * mxdot y y <=
     \sum_(i < n) (t 0 i * mxdot y (stage_row cU x0 i *m Q^T)) ^+ 2)%R ->
  (forall i, `|t 0 i| * frobenius (stage_row cU x0 i) <= rho)%R ->
  (c0 * d%:R <= m%:R)%R -> (c0 * d%:R <= q%:R)%R -> (m <= d)%N ->
  (0 < rho)%R -> (C * rho <= gam)%R ->
  tuple_prod (fun k => nu (k %% d)%N) (n * d)
    [set y | dual_ball (gam * d%:R)%R
       (stage_map cU cJ (tuple_merge (stage_revealed cU I) x0 y) t + B)%R]
  <= ((C * gam) ^+ (m * q))%R%:E.
Proof.
move=> M0 mu0 c00; have [C C0 hC] := stage_small_ball_flat M0 mu0 c00.
exists C => // n d p q m cU cJ nu I t Q B x0 rho gam cJinj hUJ h0 h1 h2.
by apply: hC => // k /ltn_mod_mul kd; [exact: h0|exact: h1|exact: h2].
Qed.

End stage.
