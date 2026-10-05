(* Raw head-data operator bound for one fixed injective selection of sample
   points, under the actual law of the sample.

   x : paper_main_sample N d has the law paper_main_probability N d, the
   measure gaussian_product_law (N * d). For an injective s : 'I_m -> 'I_N,
   X_J is the d x m matrix with columns x_(s k). pmdo_list s xs lists its
   entries in the layout of paper_main_gordon_matrix_value (PaperMainGordonScalar),
   entry (a, k) at position a * m + k.
   - Linear form. For list vectors u of R^d and v of R^m, u^T X_J v is the
     linear form of the sample coordinates with coefficients
     pmdo_coef u v, which is u_a v_k at position s_k d + a and 0 elsewhere
     (pmdo_linear_value). Since s is injective, its squared norm is
     |u|^2 |v|^2 (pmdo_coef_norm). So for unit u, v the existing unit linear
     tail applies in the actual law; no selected-row law is used.
   - Net tests (pmdo_test_tail). For unit nets z (r points of R^d) and w
     (q points of R^m), the event "B <= |z_y^T X_J w_t| for some y < r,
     t < q" is measurable with probability at most r q 2 exp(-B^2/2).
   - Loewner bridge (pmdo_loewner). If |u^T X_J v| <= L |u| |v| for all
     u, v (paper_main_gordon_operator_bound d m), then
     paper_main_head_data_gram x s <= L^2 I in Loewner order.
   - Fixed selection (paper_main_data_head_operator_fixed). For d, m > 0 and
     t > 0 there is a measurable event of probability at most 2 exp(-t)
     outside which paper_main_head_data_gram x s <= 8 (C (d + m) + t) I,
     with C = paper_main_gordon_entropy_constant (1/4) = 20 ln 2. The nets
     are those of paper_main_gordon_operator_discretization
     (PaperMainGordonOperatorNet), with ln r + ln q <= C (d + m) and
     operator norm at most twice the net bound.
   No independence of rows, rotation law, tail bound or coercivity is
   assumed. Nothing from the paper is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGeometryGram
  PaperMainGeometrySeparation PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainMatrixDuality PaperMainGordonProcessCovariance
  PaperMainGordonScalar PaperMainGordonBilinear PaperMainGordonNets PaperMainGordonEntropy
  PaperMainGordonOperatorNet PaperMainGaussianLinearLaw PaperMainGaussianTails
  PaperMainGaussianUnion PaperMainGaussianFeatureTail PaperMainDataFeatureMomentsCoordinates
  PaperMainDataSampleTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* A selection read on nat indices. *)
Definition pmdo_sel {m N : nat} (s : 'I_m -> 'I_N) (k : nat) : nat :=
  if insub k is Some k' then nat_of_ord (s k') else 0%N.

Lemma pmdo_sel_ord m N (s : 'I_m -> 'I_N) (k : 'I_m) : pmdo_sel s k = s k.
Proof. by rewrite /pmdo_sel valK. Qed.

Lemma pmdo_sel_lt m N (s : 'I_m -> 'I_N) k : (k < m)%N -> (pmdo_sel s k < N)%N.
Proof.
by move=> Hk; rewrite -[k]/(nat_of_ord (Ordinal Hk)) pmdo_sel_ord; exact: ltn_ord.
Qed.

Lemma pmdo_sel_inj m N (s : 'I_m -> 'I_N) k k' :
  injective s -> (k < m)%N -> (k' < m)%N -> pmdo_sel s k = pmdo_sel s k' -> k = k'.
Proof.
move=> Hs Hk Hk'.
rewrite -[k]/(nat_of_ord (Ordinal Hk)) -[k']/(nat_of_ord (Ordinal Hk')) !pmdo_sel_ord.
by move=> /val_inj /Hs ->.
Qed.

(* Sums over blocks of length d. *)
Lemma pmdo_sum_blocks N d (F : nat -> R) :
  finite_sum F (List.seq 0 (N * d)) =
  finite_sum (fun i => finite_sum (fun a => F (i * d + a)%N) (List.seq 0 d)) (List.seq 0 N).
Proof.
elim: N => [//|N IH].
rewrite mulSn addnC.
have -> : (N * d + d)%N = Nat.add (N * d) d by [].
by rewrite finite_sum_seq_split IH finite_sum_seq_S.
Qed.

Lemma pmdo_block_mod d i a : (a < d)%N -> ((i * d + a) %% d)%N = a.
Proof. by move=> Ha; rewrite modnMDl modn_small. Qed.

Lemma pmdo_block_div d i a : (a < d)%N -> ((i * d + a) %/ d)%N = i.
Proof.
move=> Ha; have Hd : (0 < d)%N by apply: leq_ltn_trans (leq0n a) Ha.
by rewrite divnMDl // divn_small // addn0.
Qed.

Section Selection.
Variables (N d m : nat) (s : 'I_m -> 'I_N).

(* The selected d x m matrix X_J, entry (a, k) at position a * m + k. *)
Definition pmdo_list (xs : list R) : list R :=
  List.map (fun l => List.nth (pmdo_sel s (l %% m) * d + l %/ m)%N xs 0)
    (List.seq 0 (d * m)).

Lemma pmdo_list_length xs : List.length (pmdo_list xs) = (d * m)%N.
Proof. exact: length_map_seq. Qed.

Lemma pmdo_list_nth xs a k : (a < d)%N -> (k < m)%N ->
  List.nth (a * m + k)%N (pmdo_list xs) 0 = List.nth (pmdo_sel s k * d + a)%N xs 0.
Proof.
move=> Ha Hk.
have Hl : (a * m + k < d * m)%coq_nat.
  have /ssrnat.ltP Ha' := Ha; have /ssrnat.ltP Hk' := Hk.
  rewrite -!multE -!plusE; nia.
by rewrite /pmdo_list (nth_map_seq _ _ _ Hl) pmdo_block_mod // pmdo_block_div.
Qed.

(* The coefficient vector of u^T X_J v in the sample coordinates. *)
Definition pmdo_spread (v : nat -> R) (i : nat) : R :=
  finite_sum (fun k => pmdf_kron i (pmdo_sel s k) * v k) (List.seq 0 m).

Definition pmdo_coef (u v : nat -> R) (l : nat) : R :=
  u (l %% d)%N * pmdo_spread v (l %/ d)%N.

Lemma pmdo_spread_sum (v g : nat -> R) :
  finite_sum (fun i => pmdo_spread v i * g i) (List.seq 0 N) =
  finite_sum (fun k => v k * g (pmdo_sel s k)) (List.seq 0 m).
Proof.
rewrite /pmdo_spread.
transitivity (finite_sum (fun i => finite_sum (fun k =>
    pmdf_kron (pmdo_sel s k) i * (v k * g i)) (List.seq 0 m)) (List.seq 0 N)).
  apply: finite_sum_ext => i _; rewrite -finite_sum_scale_r.
  by apply: finite_sum_ext => k _; rewrite pmdf_kron_sym; ring.
rewrite finite_sum_swap; apply: finite_sum_ext => k /List.in_seq Hk.
apply: (pmds_kron_sum N (pmdo_sel s k) (fun i => v k * g i)).
by apply/ssrnat.ltP; apply: pmdo_sel_lt; apply/ssrnat.ltP; lia.
Qed.

Lemma pmdo_coef_sum (u v f : nat -> R) :
  finite_sum (fun l => pmdo_coef u v l * f l) (List.seq 0 (N * d)) =
  finite_sum (fun a => finite_sum (fun k => u a * v k * f (pmdo_sel s k * d + a)%N)
    (List.seq 0 m)) (List.seq 0 d).
Proof.
rewrite pmdo_sum_blocks.
transitivity (finite_sum (fun i => finite_sum (fun a =>
    u a * (pmdo_spread v i * f (i * d + a)%N)) (List.seq 0 d)) (List.seq 0 N)).
  apply: finite_sum_ext => i _; apply: finite_sum_ext => a /List.in_seq Ha.
  have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
  by rewrite /pmdo_coef pmdo_block_mod // pmdo_block_div //; ring.
rewrite finite_sum_swap; apply: finite_sum_ext => a _.
rewrite finite_sum_scale (pmdo_spread_sum v (fun i => f (i * d + a)%N)) -finite_sum_scale.
by apply: finite_sum_ext => k _; ring.
Qed.

Lemma pmdo_spread_sel (v : nat -> R) k : injective s -> (k < m)%N ->
  pmdo_spread v (pmdo_sel s k) = v k.
Proof.
move=> Hs Hk; rewrite /pmdo_spread.
transitivity (finite_sum (fun k' => pmdf_kron k k' * v k') (List.seq 0 m)).
  apply: finite_sum_ext => k' /List.in_seq Hk'.
  have Hk'' : (k' < m)%N by apply/ssrnat.ltP; lia.
  congr (_ * _); rewrite /pmdf_kron.
  case: (Nat.eqb_spec (pmdo_sel s k) (pmdo_sel s k')) => [E|E];
    case: (Nat.eqb_spec k k') => [E'|E'] //.
  - by case: E'; exact: (pmdo_sel_inj _ _ s k k' Hs Hk Hk'' E).
  - by case: E; rewrite E'.
by apply: pmds_kron_sum; apply/ssrnat.ltP.
Qed.

Lemma pmdo_coef_norm (u v : nat -> R) :
  injective s ->
  paper_main_gordon_dot (N * d) (pmdo_coef u v) (pmdo_coef u v) =
  paper_main_gordon_dot d u u * paper_main_gordon_dot m v v.
Proof.
move=> Hs; rewrite /paper_main_gordon_dot (pmdo_coef_sum u v (pmdo_coef u v)).
transitivity (finite_sum (fun a => finite_sum (fun k =>
    (u a * u a) * (v k * v k)) (List.seq 0 m)) (List.seq 0 d)).
  apply: finite_sum_ext => a /List.in_seq Ha; apply: finite_sum_ext => k /List.in_seq Hk.
  have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
  have Hk' : (k < m)%N by apply/ssrnat.ltP; lia.
  by rewrite /pmdo_coef pmdo_block_mod // pmdo_block_div // pmdo_spread_sel //; ring.
rewrite -finite_sum_scale_r; apply: finite_sum_ext => a _.
by rewrite finite_sum_scale.
Qed.

Lemma pmdo_linear_value (u v : nat -> R) (x : paper_main_sample N d) :
  paper_main_gaussian_linear_random (N * d) (pmdo_coef u v) x =
  paper_main_gordon_matrix_value d m u v (pmdo_list (tval x)).
Proof.
rewrite /paper_main_gaussian_linear_random /paper_main_gordon_dot pmdo_coef_sum.
rewrite /paper_main_gordon_matrix_value; apply: finite_sum_ext => a /List.in_seq Ha.
apply: finite_sum_ext => k /List.in_seq Hk.
have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
have Hk' : (k < m)%N by apply/ssrnat.ltP; lia.
by rewrite (pmdo_list_nth _ _ _ Ha' Hk').
Qed.

End Selection.

Section Tests.
Variables (N d m : nat) (s : 'I_m -> 'I_N).

(* Net tests: some pair of net points gives |z_y^T X_J w_t| >= b. *)
Definition pmdo_test_set (r q : nat) (z w : nat -> nat -> R) (b : R) :
    set (paper_main_sample N d) :=
  [set x | exists y t, (y < r)%N /\ (t < q)%N /\
    Rle b (Rabs (paper_main_gordon_matrix_value d m (z y) (w t)
      (pmdo_list N d m s (tval x))))].

Lemma pmdo_test_tail r q z w b :
  injective s -> 0 < b ->
  (forall y, (y < r)%N -> paper_main_gordon_dot d (z y) (z y) = 1) ->
  (forall t, (t < q)%N -> paper_main_gordon_dot m (w t) (w t) = 1) ->
  measurable (pmdo_test_set r q z w b) /\
  (paper_main_probability N d (pmdo_test_set r q z w b) <=
    (INR r * INR q * (2 * exp (- b ^ 2 / 2)))%:E)%E.
Proof.
move=> Hs Hb Hz Hw.
have Hp : (0%:E <= (INR r * INR q * (2 * exp (- b ^ 2 / 2)))%:E)%E.
  rewrite lee_fin; apply: mulr_ge0; first by apply: mulr_ge0; apply/RleP; exact: pos_INR.
  by apply: mulr_ge0 => //; apply/RleP; exact: Rlt_le _ _ (exp_pos _).
case: (posnP q) => [Hq0|Hq].
  have -> : pmdo_test_set r q z w b = set0.
    by apply/seteqP; split => x // [y [t [_ [Ht _]]]]; move: Ht; rewrite Hq0.
  split; first exact: measurable0.
  by rewrite /paper_main_probability measure0.
pose E := fun c => [set x : paper_main_sample N d | Rle b (Rabs
  (paper_main_gaussian_linear_random (N * d)
    (pmdo_coef N d m s (z (c %/ q)%N) (w (c %% q)%N)) x))].
have HE : pmdo_test_set r q z w b = paper_main_finite_event_union (List.seq 0 (r * q)) E.
  apply/seteqP; split => x.
  - move=> [y [t [Hy [Ht H]]]]; apply/paper_main_finite_event_union_member.
    exists (y * q + t)%N; split.
      apply/List.in_seq; split; first lia.
      have /ssrnat.ltP Hy' := Hy; have /ssrnat.ltP Ht' := Ht.
      rewrite -!multE -!plusE; nia.
    by rewrite /E /= pmdo_block_div // pmdo_block_mod // pmdo_linear_value.
  - move/paper_main_finite_event_union_member => [c [Hc H]].
    have /ssrnat.ltP Hc' : (c < r * q)%coq_nat by move/List.in_seq: Hc; lia.
    exists (c %/ q)%N, (c %% q)%N; split; first by rewrite ltn_divLR.
    split; first exact: ltn_pmod.
    by move: H; rewrite /E /= pmdo_linear_value.
have Hunit : forall c, List.In c (List.seq 0 (r * q)) ->
    paper_main_gordon_dot (N * d) (pmdo_coef N d m s (z (c %/ q)%N) (w (c %% q)%N))
      (pmdo_coef N d m s (z (c %/ q)%N) (w (c %% q)%N)) = 1.
  move=> c Hc; have /ssrnat.ltP Hc' : (c < r * q)%coq_nat by move/List.in_seq: Hc; lia.
  have Hcd : (c %/ q < r)%N by rewrite ltn_divLR.
  by rewrite pmdo_coef_norm // (Hz _ Hcd) (Hw _ (ltn_pmod c Hq)); ring.
have HM : forall c, List.In c (List.seq 0 (r * q)) -> measurable (E c).
  by move=> c _; exact: paper_main_gaussian_linear_absolute_measurable.
have HP : forall c, List.In c (List.seq 0 (r * q)) ->
    (gaussian_product_law (N * d) (E c) <= (2 * exp (- b ^ 2 / 2))%:E)%E.
  by move=> c Hc; exact: paper_main_gaussian_unit_linear_absolute_tail (Hunit c Hc) Hb.
rewrite HE; split; first exact: paper_main_gaussian_union_measurable.
apply: le_trans.
  exact: (paper_main_gaussian_union_bound (N * d) _ E _ HM HP).
by rewrite List.length_seq -multE mult_INR.
Qed.

(* The Loewner bridge: an operator bound for X_J bounds the head Gram. *)
Lemma pmdo_loewner (x : paper_main_sample N d) L :
  paper_main_gordon_operator_bound d m (pmdo_list N d m s (tval x)) L ->
  paper_main_loewner_le (paper_main_head_data_gram x s) ((L ^ 2) *: 1%:M)%R.
Proof.
move=> [HL HB].
have HGs : paper_main_symmetric (paper_main_head_data_gram x s).
  move=> i j; rewrite !summxE; apply: eq_bigr => k _.
  by rewrite !mxE !big_ord1 !mxE mulrC.
split.
  apply: pmh_symmetricB => //.
  by apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
move=> wv.
pose u := fun a : nat => if insub a is Some a' then (wv a' ord0 : R) else 0.
pose v := fun k : nat => if insub k is Some k' then
  ((wv^T *m paper_main_point x (s k')) ord0 ord0)%R else 0.
have Hu : finite_sum (fun a => u a ^ 2) (List.seq 0 d) = ((wv^T *m wv) ord0 ord0)%R.
  rewrite paper_main_finite_sum_public pmh_vec_dot; apply: eq_bigr => a _.
  by rewrite /u valK RpowE expr2.
have Hv : finite_sum (fun k => v k ^ 2) (List.seq 0 m) =
    (\sum_(k < m) ((wv^T *m paper_main_point x (s k)) ord0 ord0) ^+ 2)%R.
  rewrite paper_main_finite_sum_public; apply: eq_bigr => k _.
  by rewrite /v valK RpowE.
have Hmv : paper_main_gordon_matrix_value d m u v (pmdo_list N d m s (tval x)) =
    finite_sum (fun k => v k ^ 2) (List.seq 0 m).
  rewrite /paper_main_gordon_matrix_value finite_sum_swap.
  apply: finite_sum_ext => k /List.in_seq Hk.
  have Hk' : (k < m)%N by apply/ssrnat.ltP; lia.
  transitivity (v k * finite_sum (fun a => u a *
      List.nth (pmdo_sel s k * d + a)%N (tval x : list R) 0) (List.seq 0 d)).
    rewrite -finite_sum_scale; apply: finite_sum_ext => a /List.in_seq Ha.
    have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
    by rewrite (pmdo_list_nth _ _ _ _ _ _ _ Ha' Hk'); ring.
  have -> : finite_sum (fun a => u a * List.nth (pmdo_sel s k * d + a)%N (tval x : list R) 0)
      (List.seq 0 d) = v k.
    rewrite /v -[k]/(nat_of_ord (Ordinal Hk')) valK pmdo_sel_ord.
    rewrite paper_main_finite_sum_public pmh_vec_dot; apply: eq_bigr => a _.
    by rewrite /u valK /paper_main_point !mxE.
  ring.
set SV := finite_sum (fun k => v k ^ 2) (List.seq 0 m) in Hv Hmv.
set W := ((wv^T *m wv) ord0 ord0)%R in Hu.
have HSV0 : 0 <= SV by apply: finite_sum_nonneg => k _; exact: pow2_ge_0.
have HW0 : 0 <= W by apply/RleP; exact: pmh_vec_sqr_ge0.
have H := HB u v.
rewrite Hmv /euclidean_norm /squared_norm Hu -/SV (Rabs_pos_eq _ HSV0) in H.
have Hfin : SV <= L ^ 2 * W.
  have Ha2 := sqrt_sqrt _ HSV0; have Hc2 := sqrt_sqrt _ HW0.
  have Ha0 := sqrt_pos SV; have Hc0 := sqrt_pos W.
  case: (Req_dec (sqrt SV) 0) => Ha.
    by rewrite -Ha2 Ha; nra.
  have Hap : 0 < sqrt SV by lra.
  have Hac : sqrt SV <= L * sqrt W.
    apply: (Rmult_le_reg_r (sqrt SV)) => //; nra.
  rewrite -Ha2 -Hc2; nra.
rewrite pms_formB paper_main_form_scale pmh_form_id /paper_main_head_data_gram pmh_form_sumr.
rewrite subr_ge0; apply/RleP; apply: Rle_trans Hfin.
right; rewrite Hv; apply: eq_bigr => k _.
by rewrite paper_main_quadratic_formE paper_main_form_rank1E.
Qed.

End Tests.

(* The probability arithmetic: r q 2 exp(-b^2/2) <= 2 exp(-t). *)
Lemma pmdo_rate (r q : nat) (C D t b : R) :
  (0 < r)%coq_nat -> (0 < q)%coq_nat -> ln (INR r) + ln (INR q) <= C * D ->
  b ^ 2 = 2 * (C * D + t) ->
  INR r * INR q * (2 * exp (- b ^ 2 / 2)) <= 2 * exp (- t).
Proof.
move=> Hr Hq Hent Hb2.
have Hr0 : 0 < INR r by apply: lt_0_INR.
have Hq0 : 0 < INR q by apply: lt_0_INR.
have E1 : INR r * INR q = exp (ln (INR r) + ln (INR q)) by rewrite exp_plus !exp_ln.
have E2 := pmds_exp_le _ _ Hent.
have E3 : exp (C * D) * exp (- b ^ 2 / 2) = exp (- t).
  by rewrite -exp_plus Hb2; congr exp; field.
have He := Rlt_le _ _ (exp_pos (- b ^ 2 / 2)).
rewrite E1.
apply: Rle_trans (_ : exp (C * D) * (2 * exp (- b ^ 2 / 2)) <= _).
  by apply: Rmult_le_compat_r => //; lra.
by rewrite -E3; lra.
Qed.

(* One fixed injective selection. *)
Theorem paper_main_data_head_operator_fixed N d m (s : 'I_m -> 'I_N) (t : R) :
  injective s -> (0 < d)%N -> (0 < m)%N -> 0 < t ->
  exists E : set (paper_main_sample N d),
    measurable E /\
    (paper_main_probability N d E <= (2 * exp (- t))%:E)%E /\
    forall x, ~ E x ->
      paper_main_loewner_le (paper_main_head_data_gram x s)
        ((8 * (paper_main_gordon_entropy_constant (1/4) * (INR d + INR m) + t) : R) *: 1%:M)%R.
Proof.
move=> Hs Hd Hm Ht.
have /ssrnat.ltP Hd' := Hd; have /ssrnat.ltP Hm' := Hm.
have [r [q [z [w [Hr [Hq [Hz [Hw [Hent Hnet]]]]]]]]] :=
  paper_main_gordon_operator_discretization d m Hd' Hm'.
set C := paper_main_gordon_entropy_constant (1/4) in Hent Hnet *.
have HC := paper_main_gaussian_entropy_positive; rewrite -/C in HC.
have HD : 0 <= INR d + INR m by have := pos_INR d; have := pos_INR m; lra.
set b := paper_main_gaussian_operator_threshold d m t.
have Hpos : 0 < 2 * (C * (INR d + INR m) + t) by nra.
have Hb2 : b ^ 2 = 2 * (C * (INR d + INR m) + t).
  by rewrite /b /paper_main_gaussian_operator_threshold -/C (pow2_sqrt _ (Rlt_le _ _ Hpos)).
have Hb : 0 < b.
  by rewrite /b /paper_main_gaussian_operator_threshold -/C; exact: sqrt_lt_R0.
have Hz' : forall y, (y < r)%N -> paper_main_gordon_dot d (z y) (z y) = 1.
  by move=> y /ssrnat.ltP Hy; exact: Hz.
have Hw' : forall t', (t' < q)%N -> paper_main_gordon_dot m (w t') (w t') = 1.
  by move=> t' /ssrnat.ltP Ht'; exact: Hw.
have [HM HP] := pmdo_test_tail N d m s r q z w b Hs Hb Hz' Hw'.
exists (pmdo_test_set N d m s r q z w b); split => //; split.
  apply: le_trans HP _; rewrite lee_fin; apply/RleP.
  exact: (pmdo_rate r q C (INR d + INR m) t b Hr Hq Hent Hb2).
move=> x Hx.
have Hlen := pmdo_list_length N d m s (tval x).
have Htests : forall y t', (y < r)%coq_nat -> (t' < q)%coq_nat ->
    Rabs (paper_main_gordon_matrix_value d m (z y) (w t') (pmdo_list N d m s (tval x))) <= b.
  move=> y t' Hy Ht'; apply: Rlt_le; apply: Rnot_le_lt => H; apply: Hx.
  by exists y, t'; split; [exact/ssrnat.ltP | split; [exact/ssrnat.ltP | exact: H]].
have Hnorm := Hnet _ b Hlen (Rlt_le _ _ Hb) Htests.
have Hbound := proj2 (paper_main_gordon_operator_norm_characterization d m _ (2 * b) Hlen) Hnorm.
have -> : 8 * (C * (INR d + INR m) + t) = (2 * b) ^ 2.
  by rewrite Rpow_mult_distr Hb2; ring.
exact: pmdo_loewner Hbound.
Qed.
