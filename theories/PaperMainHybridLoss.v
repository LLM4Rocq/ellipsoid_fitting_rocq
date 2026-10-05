(* The bounded loss gap for the hybrid model.

   The empirical risk of u in R^N is (1/N) sum_i phi(u_i) with
   phi(t) = 1 - exp(-t^2) (paper_main_loss), and
   exp(-1) min(t^2, 1) <= phi(t) (paper_main_loss_sandwich).
   If every kept set J with |J| >= N - k satisfies ||S_J u|| >= c4 sqrt N,
   and delta N < k + 1, then the risk is at least exp(-1) min(delta, c4^2):
   when more than k coordinates satisfy |u_i| > 1 their losses alone give
   exp(-1) (k + 1) / N > exp(-1) delta; otherwise they are deleted and the
   remaining coordinates have |u_i| <= 1, so phi(u_i) >= exp(-1) u_i^2 and
   the residual bound gives exp(-1) c4^2.
   Combined with PaperMainHybridResidual, the hybrid risk gap holds for every
   symmetric H, PSD B with ||H||_F^2 + ||B||_F^2 >= 1/4 and every b; no
   upper bound on ||H||_F^2 + ||B||_F^2 is used. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import PaperMainTranslatedLoss GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainGeometryHomogeneous
  PaperMainGaussianFeatureCoordinates
  PaperMainHeadSmallBallNet PaperMainHeadSmallBallUniform PaperMainProjectedBulkEscape
  PaperMainProjectedBulkComplement PaperMainProjectedBulkConditional PaperMainHybridResidual.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition paper_main_hybrid_risk N (u : 'cV[R]_N) : R :=
  ((\sum_(i < N) paper_main_loss (u i 0))%R / INR N)%Rcoq.

Theorem paper_main_hybrid_loss_gap N k (u : 'cV[R]_N) (delta c4 : R) :
  (0 < N)%N -> (delta * INR N < INR k + 1)%Rcoq -> (0 <= c4)%Rcoq ->
  (forall J : {set 'I_N}, (N - k <= #|J|)%N ->
     (c4 * sqrt (INR N) <=
      paper_main_projected_norm (paper_main_projected_selector J *m u))%Rcoq) ->
  (exp (-1) * Rmin delta (c4 ^ 2) <= paper_main_hybrid_risk N u)%Rcoq.
Proof.
move=> HN Hk Hc4 Hres.
have HNR : (0 < INR N)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have He : (0 < exp (-1))%Rcoq by apply: exp_pos.
have Hloss0 : forall i : 'I_N, (0 <= paper_main_loss (u i 0))%R.
  by move=> i; apply/RleP; exact: (proj1 (paper_main_loss_bounds _)).
have Hsplit : forall P : pred 'I_N,
    (\sum_(i | P i) paper_main_loss (u i 0) <= \sum_i paper_main_loss (u i 0))%R.
  move=> P; rewrite [X in (_ <= X)%R](bigID P) /= lerDl.
  by apply: sumr_ge0 => i _; exact: Hloss0.
set I := [set i : 'I_N | (1 < `|u i 0|)%R]%SET.
rewrite /paper_main_hybrid_risk.
set S := (\sum_(i < N) paper_main_loss (u i 0))%R.
suff HS : (exp (-1) * Rmin delta (c4 ^ 2) * INR N <= S)%Rcoq.
  apply: (Rmult_le_reg_r (INR N)) => //.
  have -> : (S / INR N * INR N = S)%Rcoq by field; lra.
  exact: HS.
case: (leqP #|I| k) => HI.
  set J := (~: I)%SET.
  have HJ : (N - k <= #|J|)%N.
    have HJc : #|J| = (N - #|I|)%N by rewrite /J cardsCs finset.setCK card_ord.
    by rewrite HJc; exact: leq_sub2l.
  have HR := Hres J HJ.
  have Hsq : (c4 ^ 2 * INR N <=
      paper_main_projected_sqnorm (paper_main_projected_selector J *m u))%Rcoq.
    have H0 : (0 <= c4 * sqrt (INR N))%Rcoq by apply: Rmult_le_pos => //; exact: sqrt_pos.
    have Hs0 := paper_main_projected_sqnorm_ge0 (paper_main_projected_selector J *m u).
    move/RleP: Hs0 => Hs0.
    have := Rmult_le_compat _ _ _ _ H0 H0 HR HR.
    rewrite /paper_main_projected_norm sqrt_sqrt //.
    have -> : (c4 * sqrt (INR N) * (c4 * sqrt (INR N)) =
        c4 ^ 2 * (sqrt (INR N) * sqrt (INR N)))%Rcoq by ring.
    by rewrite sqrt_sqrt; lra.
  have HJS : (exp (-1) * paper_main_projected_sqnorm (paper_main_projected_selector J *m u)
      <= S)%Rcoq.
    rewrite paper_main_hybrid_selector_sqnorm.
    apply/RleP.
    rewrite RmultE mulr_sumr.
    apply: le_trans (Hsplit (fun i => i \in J)).
    apply: ler_sum => i HiJ.
    have HiI : ~~ (i \in I) by move: HiJ; rewrite /J inE.
    have Hi : (`|u i 0| <= 1)%R by move: HiI; rewrite /I inE -leNgt.
    set ui := u i 0 in Hi *.
    have Hi' : (Rabs ui <= 1)%Rcoq by apply/RleP; rewrite RabsE.
    have Hu2 : (ui ^ 2 <= 1)%Rcoq.
      have H0 := Rabs_pos ui.
      have : (Rabs ui * Rabs ui <= 1)%Rcoq by nra.
      by rewrite -Rabs_mult Rabs_right /= ?Rmult_1_r; nra.
    have [Hs _] := paper_main_loss_sandwich ui.
    rewrite Rmin_left // in Hs.
    apply/RleP; rewrite -RmultE -RpowE.
    exact: Hs.
  have Hm : (Rmin delta (c4 ^ 2) <= c4 ^ 2)%Rcoq by apply: Rmin_r.
  have H1 : (exp (-1) * Rmin delta (c4 ^ 2) * INR N <= exp (-1) * (c4 ^ 2 * INR N))%Rcoq.
    rewrite Rmult_assoc; apply: Rmult_le_compat_l; first lra.
    by apply: Rmult_le_compat_r; lra.
  have H2 : (exp (-1) * (c4 ^ 2 * INR N) <=
      exp (-1) * paper_main_projected_sqnorm (paper_main_projected_selector J *m u))%Rcoq.
    by apply: Rmult_le_compat_l; lra.
  lra.
have HIS : (exp (-1) * INR #|I| <= S)%Rcoq.
  have -> : (exp (-1) * INR #|I|)%Rcoq = (\sum_(i in I) exp (-1))%R.
    by rewrite sumr_const RmultE INRE mulr_natr.
  apply/RleP.
  apply: le_trans (Hsplit (fun i => i \in I)).
  apply: ler_sum => i HiI.
  have Hi : (1 < `|u i 0|)%R by move: HiI; rewrite /I inE.
  set ui := u i 0 in Hi *.
  have Hi' : (1 < Rabs ui)%Rcoq by apply/RltP; rewrite RabsE.
  have Hu2 : (1 <= ui ^ 2)%Rcoq.
    have H0 := Rabs_pos ui.
    have : (1 <= Rabs ui * Rabs ui)%Rcoq by nra.
    by rewrite -Rabs_mult Rabs_right /= ?Rmult_1_r; nra.
  have [Hs _] := paper_main_loss_sandwich ui.
  rewrite Rmin_right // in Hs.
  apply/RleP; lra.
have Hk1 : (INR k + 1 <= INR #|I|)%Rcoq.
  have := le_INR _ _ (elimT ssrnat.leP HI); rewrite S_INR; lra.
have Hm : (Rmin delta (c4 ^ 2) <= delta)%Rcoq by apply: Rmin_l.
have H1 : (exp (-1) * Rmin delta (c4 ^ 2) * INR N <= exp (-1) * (delta * INR N))%Rcoq.
  rewrite Rmult_assoc; apply: Rmult_le_compat_l; first lra.
  by apply: Rmult_le_compat_r; lra.
have H2 : (exp (-1) * (delta * INR N) <= exp (-1) * INR #|I|)%Rcoq.
  by apply: Rmult_le_compat_l; lra.
lra.
Qed.

(* The hybrid risk gap: the deterministic residual gap of
   PaperMainHybridResidual followed by the loss gap. *)

Corollary paper_main_hybrid_risk_gap N r mi k (h : paper_main_sample N r)
    (x : (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R))
    (beta C0 delta : R) :
  (0 < N)%N -> (0 < beta)%Rcoq -> (0 < C0)%Rcoq -> (delta * INR N < INR k + 1)%Rcoq ->
  (forall (H : 'M[R]_r) (b : R) (J : {set 'I_N}), paper_main_symmetric H ->
     (N - k <= #|J|)%N ->
     (INR N / 4864 * paper_main_head_small_ball_sigma2 H b <=
      paper_main_head_small_ball_energy H b J h)%Rcoq) ->
  (forall J : {set 'I_N}, (N - k <= #|J|)%N ->
     forall (v : nat -> R) (c : 'cV[R]_(r * r + 1)), paper_main_projected_psd_set mi v ->
     (beta * sqrt (INR N) < paper_main_projected_norm (paper_main_projected_residual N
        (paper_main_symmetric_dimension mi) (r * r + 1) J
        (paper_main_projected_selector J *m paper_main_hybrid_head_matrix N r h) x v c))%Rcoq) ->
  (forall B : 'M[R]_(S mi), paper_main_symmetric B ->
     (paper_main_projected_norm (paper_main_hybrid_bulk_value N mi x B) <=
      C0 * sqrt (INR N) * paper_main_frobenius B)%Rcoq) ->
  forall (H : 'M[R]_r) (b : R) (B : 'M[R]_(S mi)),
    paper_main_symmetric H -> paper_main_psd B ->
    (1 / 4 <= paper_main_frobenius H ^ 2 + paper_main_frobenius B ^ 2)%Rcoq ->
    (exp (-1) * Rmin delta (paper_main_hybrid_gap_constant beta C0 ^ 2) <=
     paper_main_hybrid_risk N (paper_main_hybrid_residual N r mi h x H b B))%Rcoq.
Proof.
move=> HN Hb HC Hk Hhead Hbulk Hop H b B HH HB Hn.
apply: (paper_main_hybrid_loss_gap N k) => //.
  exact: Rlt_le (paper_main_hybrid_gap_constant_pos beta C0 Hb HC).
move=> J HJ.
exact: (paper_main_hybrid_residual_gap N r mi k h x beta C0 Hb HC Hhead Hbulk Hop H b B J
  HH HB Hn HJ).
Qed.
