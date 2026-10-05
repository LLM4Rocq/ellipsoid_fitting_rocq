(* The good event of the non-backtracking column frame: the bounds on the
   square-free columns used by the column remainder estimates.

   For a sample x of N rows of d coordinates put C = 'I_d * 'I_d,
   X = pmnb_X d (tval x), so X i (a, b) = [a < b] x_ia x_ib,
   R_q = pmcr_rankone N C X q and Q_q = pmcr_column_norm N C X q.
   1. Identities, deterministic:
      - X i q ^ 2 = [q.1 < q.2] (x_i,q.1 x_i,q.2)^2 (pmccf_X_sq);
      - Q_q = [q.1 < q.2] paper_main_column_q N d x q.1 q.2, the column norm
        of PaperMainColumnConcentration (pmccf_column_norm);
      - sum_q R_q = (1/2) V V^T for the square-free block V of
        PaperMainFeatureGramBlocks, whose entries are sqrt 2 x_ia x_ib for
        a < b and 0 otherwise (pmccf_rankone_sum);
      - the row sum sum_q X i q ^ 2 is the diagonal entry (sum_q R_q)_ii
        (pmccf_row_sum), so it equals (1/2) (V V^T)_ii;
      - 2 'C(d, 2) = d (d - 1) (pmccf_bin2).
   2. Fix c > 0 and C0 = 2 + 109 / c (paper_main_frame_constant). Let N(d)
      have eventual density >= c and eventually 0 < N(d) <= d^2. For every
      delta > 0 the frame event of PaperMainColumnConcentrationFrameEvents
      is measurable with probability tending to 0, and for all large d,
      outside it, with U = C0 N, m = d and M = 'C(d, 2), the conditions
      paper_main_column_frame_good hold (paper_main_column_frame):
      - every Q_q <= U, and |Q_q / N - 1| <= delta when q.1 < q.2;
      - every X i q ^ 2 <= m, and 0 <= m <= U;
      - u^T (sum_q R_q) u <= U |u|^2 for every u;
      - every row sum sum_q X i q ^ 2 <= U;
      - every row sum satisfies |(sum_q X i q ^ 2) / M - 1| <= delta,
        from |(V V^T)_ii / d^2 - 1| <= delta / 4, 2 M = d (d - 1), d >= 2 and
        delta (d - 1) >= 2 (pmccf_row_scalar).
      The deterministic step, from the bounds of
      paper_main_column_frame_raw outside the frame event, is
      paper_main_column_frame_good_outside. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainAsymptotics PaperMainGeometryPsd PaperMainGeometryHeadCoefficients
  PaperMainFeatureGramBlocks PaperMainColumnConcentration PaperMainColumnConcentrationFrameEvents
  PaperMainSquarefreeEdgeLower PaperMainSquarefreeWalkNB PaperMainColumnRemainder.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. Identities for the square-free columns. *)
Lemma pmccf_point N d (x : paper_main_sample N d) (i : nat) (a : 'I_d) :
  paper_main_point x i a 0 = List.nth (i * d + a) (tval x) 0.
Proof. by rewrite /paper_main_point mxE. Qed.

Lemma pmccf_X N d (x : paper_main_sample N d) (i : 'I_N) (q : 'I_d * 'I_d) :
  @pmnb_X R d (tval x) N i q =
  ((q.1 < q.2)%N)%:R * (paper_main_point x i q.1 0 * paper_main_point x i q.2 0).
Proof. by rewrite /pmnb_X !pmccf_point. Qed.

Lemma pmccf_X_sq N d (x : paper_main_sample N d) (i : 'I_N) (q : 'I_d * 'I_d) :
  (@pmnb_X R d (tval x) N i q) ^+ 2 =
  ((q.1 < q.2)%N)%:R * (paper_main_point x i q.1 0 * paper_main_point x i q.2 0) ^+ 2.
Proof. by rewrite pmccf_X exprMn; case: (q.1 < q.2)%N; rewrite /= ?expr1n ?expr0n. Qed.

Lemma pmccf_column_norm N d (x : paper_main_sample N d) (q : 'I_d * 'I_d) :
  pmcr_column_norm N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q =
  ((q.1 < q.2)%N)%:R * paper_main_column_q N d x q.1 q.2.
Proof.
rewrite /pmcr_column_norm /paper_main_column_q /pmcc_q mulr_sumr.
by apply: eq_bigr => i _; rewrite pmccf_X_sq !pmccf_point.
Qed.

Lemma pmccf_rankone_sum N d (x : paper_main_sample N d) :
  \sum_(q : 'I_d * 'I_d) pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q =
  2^-1 *: (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T).
Proof.
apply/matrixP => i j.
have H2 : 2 != 0 :> R by rewrite pnatr_eq0.
rewrite summxE [RHS]mxE paper_main_squarefree_gram_entry mulrA mulVf // mul1r.
rewrite pair_bigA /=; apply: eq_bigr => q _.
rewrite mxE !pmccf_X.
by case: (q.1 < q.2)%N; rewrite /= ?mulr1n ?mulr0n ?mul1r ?mul0r.
Qed.

Lemma pmccf_row_sum N d (x : paper_main_sample N d) (i : 'I_N) :
  \sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2 =
  (\sum_(q : 'I_d * 'I_d) pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q) i i.
Proof. by rewrite summxE; apply: eq_bigr => q _; rewrite mxE expr2. Qed.

Lemma pmccf_form_unit n (S : 'M[R]_n) (i : 'I_n) :
  ((delta_mx i (0 : 'I_1))^T *m S *m delta_mx i (0 : 'I_1)) 0 0 = S i i.
Proof. by rewrite trmx_delta -rowE -colE !mxE. Qed.

Lemma pmccf_norm_unit n (i : 'I_n) :
  ((delta_mx i (0 : 'I_1))^T *m delta_mx i (0 : 'I_1)) 0 0 = 1 :> R.
Proof. by rewrite trmx_delta mul_delta_mx mxE !eqxx. Qed.

Lemma pmccf_bin2 d : ('C(d, 2) * 2)%N = (d * d.-1)%N.
Proof.
rewrite bin2 muln2 halfK.
by case: d => [|d] //=; rewrite oddM /= andNb subn0.
Qed.

(* The row normalization by M = 'C(d, 2). *)
Lemma pmccf_row_scalar (k s delta : R) : 2 <= k -> 0 < delta -> 2 <= delta * (k - 1) ->
  `|s / k ^+ 2 - 1| <= delta / 4 -> `|s / (k * (k - 1)) - 1| <= delta.
Proof.
move=> Hk Hd Hdk Hs.
have Hk0 : 0 < k by lra.
have Hk1 : 0 < k - 1 by lra.
have Hkk : 0 < k * (k - 1) by rewrite mulr_gt0.
have Hk2 : 0 < k ^+ 2 by rewrite exprn_gt0.
have H1 : `|s - k ^+ 2| <= delta / 4 * k ^+ 2.
  have E : s - k ^+ 2 = (s / k ^+ 2 - 1) * k ^+ 2 by rewrite mulrBl divfK ?gt_eqF // mul1r.
  by rewrite E normrM (gtr0_norm Hk2); apply: ler_wpM2r => //; exact: ltW.
have H2 : `|s - k * (k - 1)| <= `|s - k ^+ 2| + k.
  have E : s - k * (k - 1) = (s - k ^+ 2) + k by ring.
  by rewrite E; apply: le_trans (ler_normD _ _) _; rewrite (gtr0_norm Hk0).
have E : s / (k * (k - 1)) - 1 = (s - k * (k - 1)) / (k * (k - 1)).
  by rewrite mulrBl divff ?gt_eqF.
rewrite E normrM normfV (gtr0_norm Hkk) ler_pdivrMr //.
apply: le_trans H2 _.
have Hk2' : 0 <= k - 2 by rewrite subr_ge0.
have Hp1 : 0 <= delta * k * (k - 2) by rewrite !mulr_ge0 // ltW.
have Hdk' : 0 <= delta * (k - 1) - 2 by rewrite subr_ge0.
have Hp2 : 0 <= k * (delta * (k - 1) - 2) by rewrite mulr_ge0 // ltW.
nra.
Qed.

(* 2. The frame conditions. *)
Definition paper_main_column_frame_good N d (C0 delta : R) (x : paper_main_sample N d) : Prop :=
  [/\ (forall q : 'I_d * 'I_d,
         pmcr_column_norm N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q <= C0 * N%:R) /\
      (forall q : 'I_d * 'I_d, (q.1 < q.2)%N ->
         `|pmcr_column_norm N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q / N%:R - 1| <= delta),
      (forall (i : 'I_N) (q : 'I_d * 'I_d), (@pmnb_X R d (tval x) N i q) ^+ 2 <= d%:R) /\
        0 <= d%:R :> R /\ d%:R <= C0 * N%:R,
      (forall u : 'cV[R]_N,
         (u^T *m (\sum_(q : 'I_d * 'I_d)
            pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q) *m u) 0 0 <=
         C0 * N%:R * (u^T *m u) 0 0),
      (forall i : 'I_N, \sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2 <= C0 * N%:R) &
      (forall i : 'I_N,
         `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <=
         delta)].

(* Deterministic: outside the frame event, for d >= 2, delta (d - 1) >= 2,
   0 < N <= d^2 and c d^2 <= N, the frame conditions hold. *)
Theorem paper_main_column_frame_good_outside N d (c delta : R) (x : paper_main_sample N d) :
  0 < c -> 0 < delta -> (2 <= d)%N -> 2 <= delta * (d%:R - 1) -> (0 < N)%N -> (N <= d ^ 2)%N ->
  c * d%:R ^+ 2 <= N%:R -> ~ paper_main_column_frame_event N d delta x ->
  paper_main_column_frame_good N d (paper_main_frame_constant c) delta x.
Proof.
move=> Hc Hdelta Hd2 Hdd HN HNd HcN Hx.
have Hd : (0 < d)%N by apply: leq_trans Hd2.
have [Hcols Hcoord Hgram Hdiag] := paper_main_column_frame_raw N d c delta x Hc Hdelta Hd HN HNd HcN Hx.
have [HC2 HC109] := paper_main_frame_constant_ge c Hc.
set C0 := paper_main_frame_constant c in HC2 HC109 *.
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
have HC0 : 0 <= C0 by lra.
have HU2 : 2 * N%:R <= C0 * N%:R by apply: ler_wpM2r => //; exact: ltW.
have HU109 : 109 / c * N%:R <= C0 * N%:R by apply: ler_wpM2r => //; exact: ltW.
have Hd1 : 1 <= d%:R :> R by rewrite ler1n.
have H109 : 109 * d%:R ^+ 2 <= 109 / c * N%:R.
  have H109c : 0 <= 109 / c by rewrite divr_ge0 // ltW.
  have := ler_wpM2l H109c HcN.
  by rewrite mulrA divfK ?gt_eqF.
have HdU : d%:R <= C0 * N%:R.
  have Hdd2 : d%:R <= d%:R ^+ 2 :> R by nra.
  lra.
have Hform : forall u : 'cV[R]_N,
    (u^T *m (\sum_(q : 'I_d * 'I_d)
       pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q) *m u) 0 0 <=
    C0 * N%:R * (u^T *m u) 0 0.
  move=> u; rewrite pmccf_rankone_sum -scalemxAr -scalemxAl mxE.
  have Hq := Hgram u.
  have Hu := pmh_vec_sqr_ge0 _ u.
  have HB := ler_wpM2r Hu HU109.
  have HB0 : 0 <= 109 / c * N%:R * (u^T *m u) 0 0.
    have H109c : 0 <= 109 / c by rewrite divr_ge0 // ltW.
    by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ltW.
  lra.
split.
- split.
  + move=> q; rewrite pmccf_column_norm.
    case: (boolP (q.1 < q.2)%N) => Hq.
      rewrite /= ?mulr1n mul1r; have [HQ _] := Hcols q.1 q.2 Hq.
      exact: le_trans HQ HU2.
    by rewrite /= ?mulr0n mul0r; apply: mulr_ge0 => //; exact: ltW.
  + move=> q Hq; rewrite pmccf_column_norm Hq /= ?mulr1n mul1r.
    exact: (Hcols q.1 q.2 Hq).2.
- split; last by split; [exact: ler0n | exact: HdU].
  move=> i q; rewrite pmccf_X_sq.
  by case: (q.1 < q.2)%N; rewrite /= ?mulr1n ?mulr0n ?mul1r ?mul0r; [exact: Hcoord | exact: ler0n].
- exact: Hform.
- move=> i; have H := Hform (delta_mx i 0).
  by rewrite pmccf_form_unit pmccf_norm_unit mulr1 -pmccf_row_sum in H.
- move=> i.
  have HM2 : ('C(d, 2))%:R * 2 = d%:R * (d%:R - 1) :> R.
    have := congr1 (fun n : nat => n%:R : R) (pmccf_bin2 d); rewrite /= !natrM => ->.
    by rewrite -subn1 natrB.
  rewrite pmccf_row_sum pmccf_rankone_sum mxE.
  set s := (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) i i.
  have E : 2^-1 * s / ('C(d, 2))%:R = s / (d%:R * (d%:R - 1)).
    by rewrite -HM2 invfM; ring.
  rewrite E; apply: pmccf_row_scalar => //.
    by rewrite (ler_nat R 2 d).
  exact: Hdiag i.
Qed.

(* For every delta > 0, the frame event is measurable, its probability
   tends to 0, and outside it the frame conditions hold for all large d. *)
Theorem paper_main_column_frame (N : nat -> nat) (c : R) :
  0 < c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N) ->
  2 <= paper_main_frame_constant c /\
  forall delta : R, 0 < delta ->
  exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    exists D : nat, forall d, (D <= d)%N -> forall x : paper_main_sample (N d) d, ~ E d x ->
      paper_main_column_frame_good (N d) d (paper_main_frame_constant c) delta x.
Proof.
move=> Hc Hlow Hup.
split; first by have [] := paper_main_frame_constant_ge c Hc.
move=> delta Hdelta.
exists (fun d => paper_main_column_frame_event (N d) d delta); split.
  by move=> d; exact: paper_main_column_frame_event_measurable.
split; first exact: (paper_main_column_frame_event_limit N c delta Hc Hdelta Hlow Hup).
have [D1 HD1] := Hlow.
have [D2 HD2] := Hup.
have [K HK] := INR_unbounded (2 / delta)%R.
exists (maxn (maxn D1 D2) (maxn 2 K.+1)) => d Hd x Hx.
rewrite !geq_max in Hd; case/andP: Hd => /andP [HdD1 HdD2] /andP [Hd2 HdK].
have Hd0 : (0 < d)%N by apply: leq_trans Hd2.
have [HN HNd] := HD2 d HdD2.
have Hd0R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0 // ltr0n.
have HcN : c * d%:R ^+ 2 <= (N d)%:R.
  by have := HD1 d HdD1; rewrite /paper_main_density ler_pdivlMr.
have Hdd : 2 <= delta * (d%:R - 1).
  have HK' : 2 / delta < K%:R by rewrite -[K%:R]INRE; apply/RltP; exact: HK.
  have HKd : K%:R <= d%:R - 1 :> R.
    have : (K.+1)%:R <= d%:R :> R by rewrite ler_nat.
    by rewrite -natr1; lra.
  have H1 := ler_wpM2l (ltW Hdelta) HKd.
  have H2 : delta * (2 / delta) < delta * K%:R by rewrite ltr_pM2l.
  have E2 : delta * (2 / delta) = 2 by rewrite mulrC divfK ?gt_eqF.
  rewrite E2 in H2; lra.
exact: paper_main_column_frame_good_outside.
Qed.
