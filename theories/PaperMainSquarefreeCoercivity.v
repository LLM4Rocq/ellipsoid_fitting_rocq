(* From the non-backtracking lower box to the coercivity of the raw feature
   Gram matrix. Deterministic.

   For a sample x of N rows of d coordinates put C = 'I_d * 'I_d,
   X = pmnb_X d (tval x), M = 'C(d, 2), R_c = pmcr_rankone N C X c and
   D_c = pmcr_diagonal N C X c, so pmlo_T 1 = kap (sum_c R_c - sum_c D_c)
   (pmlo_T1, pmcr_column_split) and u^T (sum_c D_c) u = sum_i D_i u_i^2 with
   the row sums D_i = sum_c X i c ^ 2.
   1. paper_main_squarefree_rankone_lower: let kap > 0 with kap^2 N M = 1
      and s = kap N, so 1 / kap = M s. If 0 <= s <= 3/4, every
      |D_i / M - 1| <= 1/64 and the lower box -(49/24) I <= pmlo_T 1 - s I
      holds, then for every u
        u^T (sum_c R_c) u >= M (63/64 + s^2 - (49/24) s) |u|^2
                          >= (M / 64) |u|^2,
      since 1 + s^2 - (49/24) s - 1/32 = (s - 3/4) (s - 31/24) >= 0 on
      [0, 3/4]. paper_main_squarefree_coercivity_generic: the square-free
      Gram is 2 sum_c R_c (pmccf_rankone_sum), so it is at least (M / 32) I,
      and 2 M = d (d - 1) >= d^2 / 2 for d >= 2 gives (d^2 / 128) I. The
      full raw feature Gram is above the square-free Gram
      (paper_main_squarefree_gram_le), so it is coercive with constant
      d^2 / 128.
   2. paper_main_squarefree_coercivity: the exact normalization
      kap = (sqrt (N M))^-1 satisfies the hypotheses on kap
      (pmcr_normalization).
   3. paper_main_squarefree_coercivity_scale: if d >= 9 and 4 N <= d^2,
      then s^2 = N / M <= 9 / 16, so 0 <= s <= 3/4. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadCorrection PaperMainGeometrySeparation
  PaperMainFeatureGramBlocks PaperMainSquarefreeEdgeLower PaperMainColumnRemainder
  PaperMainColumnRemainderBounds PaperMainSquarefreeWalkNB PaperMainColumnConcentrationFrame
  PaperMainColumnConcentrationScaling PaperMainColumnRemainderScaling.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Quadratic forms of the first NB matrix and of the diagonal part. *)
Lemma pmscv_T1_form N (C : finType) (X : 'I_N -> C -> R) (kap : R) (u : 'cV[R]_N) :
  (u^T *m pmlo_T N C X kap 1 *m u) 0 0 =
  kap * ((u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 -
         (u^T *m (\sum_c pmcr_diagonal N C X c) *m u) 0 0).
Proof.
rewrite pmlo_T1.
under eq_bigr do rewrite pmcr_column_split.
rewrite -scaler_sumr sumrB -scalemxAr -scalemxAl mxE.
by rewrite mulmxBr mulmxBl !mxE.
Qed.

Lemma pmscv_diag_form N (C : finType) (X : 'I_N -> C -> R) (u : 'cV[R]_N) :
  (u^T *m (\sum_c pmcr_diagonal N C X c) *m u) 0 0 = \sum_i (\sum_c X i c ^+ 2) * u i 0 ^+ 2.
Proof.
rewrite -paper_main_quadratic_formE /paper_main_quadratic_form.
apply: eq_bigr => i _.
have Hent : forall j : 'I_N, (\sum_c pmcr_diagonal N C X c) i j = (\sum_c X i c ^+ 2) *+ (i == j).
  by move=> j; rewrite summxE -sumrMnl; apply: eq_bigr => c _; rewrite /pmcr_diagonal !mxE.
rewrite (bigD1 i) //= Hent eqxx mulr1n.
have Hz : \sum_(j < N | j != i) u i 0 * (\sum_c pmcr_diagonal N C X c) i j * u j 0 = 0.
  by apply: big1 => j Hji; rewrite Hent eq_sym (negbTE Hji) mulr0n mulr0 mul0r.
by rewrite Hz addr0 expr2; ring.
Qed.

(* The scalar inequality behind the constant 1/64. *)
Lemma pmscv_scalar (s : R) : 0 <= s -> s <= 3 / 4 -> 1 / 32 <= 1 + s ^+ 2 - 49 / 24 * s.
Proof.
move=> Hs0 Hs1.
have H : 0 <= (3 / 4 - s) * (31 / 24 - s) by apply: mulr_ge0; lra.
nra.
Qed.

(* 2. From the lower box to coercivity, for every kap with kap^2 N M = 1. *)
Theorem paper_main_squarefree_rankone_lower N d (x : paper_main_sample N d) (kap : R) :
  (0 < N)%N -> (2 <= d)%N -> 0 < kap -> kap ^+ 2 * N%:R * ('C(d, 2))%:R = 1 ->
  0 <= kap * N%:R -> kap * N%:R <= 3 / 4 ->
  (forall i : 'I_N,
     `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <= 1 / 64) ->
  paper_main_loewner_le (- (49 / 24) *: 1%:M)
    (pmlo_T N [the finType of ('I_d * 'I_d)%type] (@pmnb_X R d (tval x) N) kap 1 - (kap * N%:R) *: 1%:M) ->
  forall u : 'cV[R]_N,
    ('C(d, 2))%:R / 64 * (u^T *m u) 0 0 <=
    (u^T *m (\sum_(q : 'I_d * 'I_d) pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q) *m u) 0 0.
Proof.
move=> HN Hd Hk Hnorm Hs0 Hs1 Hrow Hbox u.
have HM0 : 0 < ('C(d, 2))%:R :> R by rewrite ltr0n bin_gt0.
have Hq := pmh_vec_sqr_ge0 _ u.
have Hb := Hbox.2 u.
rewrite !pms_formB !paper_main_form_scale !pmh_form_id !paper_main_quadratic_formE pmscv_T1_form in Hb.
set q := (u^T *m u) 0 0 in Hq Hb *.
set M := ('C(d, 2))%:R in Hnorm Hrow HM0 *.
set s := kap * N%:R in Hs0 Hs1 Hb *.
set r := (u^T *m (\sum_c pmcr_rankone N [the finType of ('I_d * 'I_d)%type] (pmnb_X d x) c) *m u) 0 0 in Hb.
set t := (u^T *m (\sum_c pmcr_diagonal N [the finType of ('I_d * 'I_d)%type] (pmnb_X d x) c) *m u) 0 0 in Hb.
change (M / 64 * q <= r).
have Hinv : M * s * kap = 1.
  have G : forall a b c : R, a * (b * c) * b = b ^+ 2 * c * a by move=> a b c; ring.
  by transitivity (kap ^+ 2 * N%:R * M); [exact (G M kap N%:R) | exact Hnorm].
have Ht : 63 / 64 * M * q <= t.
  rewrite /t pmscv_diag_form /q pmh_vec_dot mulr_sumr.
  apply: ler_sum => i _.
  have HDi : 63 / 64 * M <= \sum_c pmnb_X d x i c ^+ 2.
    have := Hrow i; rewrite ler_norml => /andP [H _].
    have H' : 63 / 64 <= (\sum_(q : 'I_d * 'I_d) pmnb_X d x i q ^+ 2) / M by lra.
    rewrite ler_pdivlMr // in H'; exact H'.
  by rewrite -expr2; apply: ler_wpM2r; [exact: sqr_ge0 | exact HDi].
have Hsc := pmscv_scalar s Hs0 Hs1.
have Hb' : (s - 49 / 24) * q <= kap * (r - t) by lra.
have HMs : 0 <= M * s by rewrite mulr_ge0 // ltW.
have H1 := ler_wpM2l HMs Hb'.
have E1 : M * s * (kap * (r - t)) = r - t by rewrite mulrA Hinv mul1r.
rewrite E1 in H1.
have HMq : 0 <= M * q by rewrite mulr_ge0 // ltW.
have H2 : M * q * (1 / 64) <= M * q * (63 / 64 + s ^+ 2 - 49 / 24 * s).
  by apply: ler_wpM2l => //; lra.
nra.
Qed.

Theorem paper_main_squarefree_coercivity_generic N d (x : paper_main_sample N d) (kap : R) :
  (0 < N)%N -> (2 <= d)%N -> 0 < kap -> kap ^+ 2 * N%:R * ('C(d, 2))%:R = 1 ->
  0 <= kap * N%:R -> kap * N%:R <= 3 / 4 ->
  (forall i : 'I_N,
     `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <= 1 / 64) ->
  paper_main_loewner_le (- (49 / 24) *: 1%:M)
    (pmlo_T N [the finType of ('I_d * 'I_d)%type] (@pmnb_X R d (tval x) N) kap 1 - (kap * N%:R) *: 1%:M) ->
  paper_main_head_coercive (paper_main_feature_gram N d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> HN Hd Hk Hnorm Hs0 Hs1 Hrow Hbox u.
have HL := paper_main_squarefree_rankone_lower N d x kap HN Hd Hk Hnorm Hs0 Hs1 Hrow Hbox u.
rewrite pmccf_rankone_sum -scalemxAr -scalemxAl [X in _ <= X]mxE in HL.
have HGu := (paper_main_squarefree_gram_le N d x).2 u.
rewrite pms_formB !paper_main_quadratic_formE in HGu.
have HM := paper_main_frame_binomial_twice d.
have Hd2 : 2 <= d%:R :> R by rewrite (ler_nat R 2 d).
have HdM : d%:R ^+ 2 <= 4 * ('C(d, 2))%:R :> R by nra.
have Hq := pmh_vec_sqr_ge0 _ u.
have H4 := ler_wpM2r Hq HdM.
nra.
Qed.

(* 3. The exact normalization. *)
Theorem paper_main_squarefree_coercivity N d (x : paper_main_sample N d) :
  (0 < N)%N -> (2 <= d)%N ->
  0 <= (Num.sqrt ((N%:R : R) * ('C(d, 2))%:R))^-1 * N%:R ->
  (Num.sqrt ((N%:R : R) * ('C(d, 2))%:R))^-1 * N%:R <= 3 / 4 ->
  (forall i : 'I_N,
     `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <= 1 / 64) ->
  paper_main_loewner_le (- (49 / 24) *: 1%:M)
    (pmlo_T N [the finType of ('I_d * 'I_d)%type] (@pmnb_X R d (tval x) N)
       ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) 1 -
     ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1 * N%:R) *: 1%:M) ->
  paper_main_head_coercive (paper_main_feature_gram N d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> HN Hd Hs0 Hs1 Hrow Hbox.
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
have HM0 : 0 < ('C(d, 2))%:R :> R by rewrite ltr0n bin_gt0.
have [Hk0 [Hk1 _]] := pmcr_normalization N%:R ('C(d, 2))%:R HN0 HM0.
exact (paper_main_squarefree_coercivity_generic N d x _ HN Hd Hk0 Hk1 Hs0 Hs1 Hrow Hbox).
Qed.

(* 4. Applicability: d >= 9 and 4 N <= d^2 give 0 <= s <= 3/4. *)
Theorem paper_main_squarefree_coercivity_scale N d :
  (0 < N)%N -> (9 <= d)%N -> (4 * N <= d ^ 2)%N ->
  0 <= (Num.sqrt ((N%:R : R) * ('C(d, 2))%:R))^-1 * N%:R /\
  (Num.sqrt ((N%:R : R) * ('C(d, 2))%:R))^-1 * N%:R <= 3 / 4.
Proof.
move=> HN Hd9 HN4.
have Hd2 : (2 <= d)%N by apply: leq_trans Hd9.
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
have HM0 : 0 < ('C(d, 2))%:R :> R by rewrite ltr0n bin_gt0.
have [Hk0 [Hk1 Hk2]] := pmcr_normalization N%:R ('C(d, 2))%:R HN0 HM0.
set kap := (Num.sqrt (N%:R * ('C(d, 2))%:R))^-1 in Hk0 Hk1 Hk2 *.
have Hs0 : 0 <= kap * N%:R by rewrite mulr_ge0 // ltW.
split => //.
have HM := paper_main_frame_binomial_twice d.
have Hd9R : 9 <= d%:R :> R by rewrite (ler_nat R 9 d).
have HN4R : 4 * N%:R <= d%:R ^+ 2 :> R.
  by have := HN4; rewrite -(ler_nat R) natrM natrX.
have HsN : (kap * N%:R) ^+ 2 = N%:R / ('C(d, 2))%:R.
  by rewrite exprMn expr2 mulrA Hk2 mulrC.
have H916 : (N%:R : R) / ('C(d, 2))%:R <= 9 / 16.
  rewrite ler_pdivrMr //; nra.
have H34 : (kap * N%:R) ^+ 2 <= (3 / 4) ^+ 2 by rewrite HsN; lra.
by rewrite ler_sqr ?nnegrE // in H34; lra.
Qed.
