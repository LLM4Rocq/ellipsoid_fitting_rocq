(* Binomial tails for counts of rows of the Gaussian sample. For a predicate
   rho on R^d let A = {h : paper_main_sample 1 d | rho (row 0 of h)} be the
   row event, with probability a under the law of one row, and
     count_n(x) = #{i < n | rho (row i of x)}      (paper_main_head_row_count).
   Splitting off the first row (paper_main_split_points 1 n d, whose law is
   the product law: paper_main_split_points_rectangle) gives the binomial
   recursion
     P_(n+1)(count <= s) = a P_n(count <= s - 1) + (1 - a) P_n(count <= s),
   and the same for {s <= count} with s - 1. By induction over n, for every
   real s:
   - if a >= p, then P_n(count <= s) <= 2^s (1 - p/2)^n;
   - if a <= q, then P_n(s <= count) <= 2^(-s) (1 + q)^n.
   The count events are measurable. Only the rectangle law of the sample is
   used; no moment generating function or product integral. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainSampling PaperMainHeadLaw
  PaperMainDataSampleTail PaperMainHeadSmallBallFourth.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

Definition paper_main_head_row_event d (rho : 'cV[R]_d -> Prop) : set (paper_main_sample 1 d) :=
  [set h | rho (paper_main_point h 0)].

Definition paper_main_head_row_count n d (rho : 'cV[R]_d -> Prop)
    (x : paper_main_sample n d) : R :=
  finite_sum (fun i => if pselect (rho (paper_main_point x i)) then 1 else 0) (List.seq 0 n).

Lemma paper_main_head_row_count0 d rho (x : paper_main_sample 0 d) :
  paper_main_head_row_count 0 d rho x = 0.
Proof. by []. Qed.

Lemma paper_main_head_row_count_cons n d rho (x : paper_main_sample n.+1 d) :
  paper_main_head_row_count n.+1 d rho x =
  (if pselect (rho (paper_main_point x 0)) then 1 else 0) +
  paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x).
Proof.
rewrite /paper_main_head_row_count paper_main_head_small_ball_sum_cons.
congr (_ + _); apply: finite_sum_ext => i _.
by rewrite paper_main_drop_points_point.
Qed.

Lemma paper_main_head_row_take_point n d (x : paper_main_sample n.+1 d) :
  paper_main_point (paper_main_take_points 1 n d x) 0 = paper_main_point x 0.
Proof. exact: (pmds_take_point 1 n d x 0 isT). Qed.

(* The decomposition of the count events along the first row. *)

Lemma paper_main_head_row_count_le_split n d rho (s : R) :
  [set x : paper_main_sample n.+1 d | Rle (paper_main_head_row_count n.+1 d rho x) s] =
  paper_main_split_points 1 n d @^-1`
    ((paper_main_head_row_event d rho `*`
      [set t | Rle (paper_main_head_row_count n d rho t) (s - 1)]) `|`
     (~` paper_main_head_row_event d rho `*`
      [set t | Rle (paper_main_head_row_count n d rho t) s])).
Proof.
apply/seteqP; split => x Hx.
- change ((rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x)) (s - 1)) \/
    (~ rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x)) s)).
  rewrite paper_main_head_row_take_point.
  change (Rle (paper_main_head_row_count n.+1 d rho x) s) in Hx.
  rewrite paper_main_head_row_count_cons in Hx.
  by case: (pselect (rho (paper_main_point x 0))) Hx => Hr /= Hx; [left | right]; split => //; lra.
- change ((rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x)) (s - 1)) \/
    (~ rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x)) s)) in Hx.
  change (Rle (paper_main_head_row_count n.+1 d rho x) s).
  rewrite paper_main_head_row_take_point in Hx.
  rewrite paper_main_head_row_count_cons.
  by case: (pselect (rho (paper_main_point x 0))) Hx => Hr /= [[H1 H2]|[H1 H2]] //; lra.
Qed.

Lemma paper_main_head_row_count_ge_split n d rho (s : R) :
  [set x : paper_main_sample n.+1 d | Rle s (paper_main_head_row_count n.+1 d rho x)] =
  paper_main_split_points 1 n d @^-1`
    ((paper_main_head_row_event d rho `*`
      [set t | Rle (s - 1) (paper_main_head_row_count n d rho t)]) `|`
     (~` paper_main_head_row_event d rho `*`
      [set t | Rle s (paper_main_head_row_count n d rho t)])).
Proof.
apply/seteqP; split => x Hx.
- change ((rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle (s - 1) (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x))) \/
    (~ rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle s (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x)))).
  rewrite paper_main_head_row_take_point.
  change (Rle s (paper_main_head_row_count n.+1 d rho x)) in Hx.
  rewrite paper_main_head_row_count_cons in Hx.
  by case: (pselect (rho (paper_main_point x 0))) Hx => Hr /= Hx; [left | right]; split => //; lra.
- change ((rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle (s - 1) (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x))) \/
    (~ rho (paper_main_point (paper_main_take_points 1 n d x) 0) /\
      Rle s (paper_main_head_row_count n d rho (paper_main_drop_points 1 n d x)))) in Hx.
  change (Rle s (paper_main_head_row_count n.+1 d rho x)).
  rewrite paper_main_head_row_take_point in Hx.
  rewrite paper_main_head_row_count_cons.
  by case: (pselect (rho (paper_main_point x 0))) Hx => Hr /= [[H1 H2]|[H1 H2]] //; lra.
Qed.

(* The binomial recursion of the probabilities. *)

Lemma paper_main_head_row_split_prob n d (A : set (paper_main_sample 1 d))
    (B C : set (paper_main_sample n d)) :
  measurable A -> measurable B -> measurable C ->
  paper_main_probability (1 + n) d
    (paper_main_split_points 1 n d @^-1` ((A `*` B) `|` (~` A `*` C))) =
  (paper_main_probability 1 d A * paper_main_probability n d B +
   paper_main_probability 1 d (~` A) * paper_main_probability n d C)%E.
Proof.
move=> mA mB mC.
have mS := paper_main_split_points_measurable 1 n d.
have m1 : measurable (paper_main_split_points 1 n d @^-1` (A `*` B)).
  by have H := mS measurableT _ (measurableX mA mB); rewrite setTI in H.
have m2 : measurable (paper_main_split_points 1 n d @^-1` (~` A `*` C)).
  by have H := mS measurableT _ (measurableX (measurableC mA) mC); rewrite setTI in H.
have Hdisj : paper_main_split_points 1 n d @^-1` (A `*` B) `&`
    paper_main_split_points 1 n d @^-1` (~` A `*` C) = set0.
  by apply/seteqP; split => x // [[H1 _] [H2 _]]; exact: H2 H1.
have R1 := paper_main_split_points_rectangle 1 n d A B mA mB.
have R2 := paper_main_split_points_rectangle 1 n d (~` A) C (measurableC mA) mC.
rewrite preimage_setU.
have HU := measureU (gaussian_product_law ((1 + n) * d)%N) m1 m2 Hdisj.
rewrite /paper_main_probability in R1 R2 *.
rewrite HU.
congr (_ + _)%E; [exact: R1 | exact: R2].
Qed.

(* Scalar steps. *)

Lemma paper_main_head_row_rpower_pos (s : R) : 0 < Rpower 2 s.
Proof. by rewrite /Rpower; apply: exp_pos. Qed.

Lemma paper_main_head_row_rpower_ge1 (s : R) : 0 <= s -> 1 <= Rpower 2 s.
Proof.
move=> Hs; rewrite /Rpower -exp_0.
have Hl : 0 < ln 2 by rewrite -ln_1; apply: ln_increasing; lra.
case: (Rle_lt_or_eq_dec 0 s Hs) => H.
- by apply/Rlt_le/exp_increasing; nra.
- by rewrite -H Rmult_0_l; lra.
Qed.

Lemma paper_main_head_row_rpower_pred (s : R) : Rpower 2 (s - 1) = Rpower 2 s / 2.
Proof.
rewrite /Rminus Rpower_plus Rpower_Ropp (Rpower_1 2 ltac:(lra)).
by rewrite /Rdiv.
Qed.

Lemma paper_main_head_row_rpower_opp_pred (s : R) : Rpower 2 (- (s - 1)) = 2 * Rpower 2 (- s).
Proof.
have -> : - (s - 1) = - s + 1 by ring.
rewrite Rpower_plus (Rpower_1 2 ltac:(lra)).
ring.
Qed.

Lemma paper_main_head_row_lower_step (a p c u v s : R) :
  0 <= p -> p <= a -> a <= 1 -> 0 <= c ->
  u <= Rpower 2 (s - 1) * c -> v <= Rpower 2 s * c -> 0 <= u -> 0 <= v ->
  a * u + (1 - a) * v <= Rpower 2 s * (c * (1 - p / 2)).
Proof.
move=> Hp Hpa Ha1 Hc Hu Hv Hu0 Hv0.
rewrite paper_main_head_row_rpower_pred in Hu.
have HX := paper_main_head_row_rpower_pos s.
set X := Rpower 2 s in Hu Hv HX *.
have H1 : a * u <= a * (X / 2 * c) by apply: Rmult_le_compat_l; lra.
have H2 : (1 - a) * v <= (1 - a) * (X * c) by apply: Rmult_le_compat_l; lra.
have H3 : 0 <= X * c by apply: Rmult_le_pos; lra.
have E : a * (X / 2 * c) + (1 - a) * (X * c) = X * c * (1 - a / 2) by field.
have H4 : X * c * (1 - a / 2) <= X * c * (1 - p / 2).
  by apply: Rmult_le_compat_l; lra.
have E2 : X * (c * (1 - p / 2)) = X * c * (1 - p / 2) by ring.
lra.
Qed.

Lemma paper_main_head_row_upper_step (a q c u v s : R) :
  0 <= a -> a <= q -> a <= 1 -> 0 <= c ->
  u <= Rpower 2 (- (s - 1)) * c -> v <= Rpower 2 (- s) * c ->
  a * u + (1 - a) * v <= Rpower 2 (- s) * (c * (1 + q)).
Proof.
move=> Ha Haq Ha1 Hc Hu Hv.
rewrite paper_main_head_row_rpower_opp_pred in Hu.
have HX := paper_main_head_row_rpower_pos (- s).
set X := Rpower 2 (- s) in Hu Hv HX *.
have H1 : a * u <= a * (2 * X * c) by apply: Rmult_le_compat_l; lra.
have H2 : (1 - a) * v <= (1 - a) * (X * c) by apply: Rmult_le_compat_l; lra.
have H3 : 0 <= X * c by apply: Rmult_le_pos; lra.
have E : a * (2 * X * c) + (1 - a) * (X * c) = X * c * (1 + a) by ring.
have H4 : X * c * (1 + a) <= X * c * (1 + q) by apply: Rmult_le_compat_l; lra.
have E2 : X * (c * (1 + q)) = X * c * (1 + q) by ring.
lra.
Qed.

(* The binomial lower tail. *)

Theorem paper_main_head_row_count_lower d (rho : 'cV[R]_d -> Prop) (p : R) :
  measurable (paper_main_head_row_event d rho) -> 0 <= p ->
  (p%:E <= paper_main_probability 1 d (paper_main_head_row_event d rho))%E ->
  forall n (s : R),
    measurable [set x : paper_main_sample n d | Rle (paper_main_head_row_count n d rho x) s] /\
    (paper_main_probability n d [set x | Rle (paper_main_head_row_count n d rho x) s] <=
      ((Rpower 2 s * (1 - p / 2) ^ n)%Rcoq)%:E)%E.
Proof.
move=> mA Hp HpA.
set A := paper_main_head_row_event d rho in mA HpA *.
have HfA : paper_main_probability 1 d A \is a fin_num by apply: fin_num_measure.
set a := fine (paper_main_probability 1 d A).
have Ha : paper_main_probability 1 d A = a%:E by rewrite /a fineK.
have Ha0 : 0 <= a by apply/RleP; apply: fine_ge0; exact: measure_ge0.
have Ha1 : a <= 1.
  have H := probability_le1 (gaussian_product_law (1 * d)%N) mA.
  have : (a%:E <= 1)%E by rewrite -Ha; exact: H.
  by rewrite lee_fin => /RleP.
have HAc : paper_main_probability 1 d (~` A) = (1 - a)%:E.
  have H := probability_setC (gaussian_product_law (1 * d)%N) mA.
  rewrite /paper_main_probability H.
  by rewrite -/(paper_main_probability 1 d A) Ha EFinB.
have Hpa : p <= a.
  have : (p%:E <= a%:E)%E by rewrite -Ha.
  by rewrite lee_fin => /RleP.
elim=> [|n IH] s.
  case: (Rle_lt_dec 0 s) => Hs.
    have -> : [set x : paper_main_sample 0 d | Rle (paper_main_head_row_count 0 d rho x) s] =
        setT.
      by apply/seteqP; split => x // _ /=; rewrite paper_main_head_row_count0.
    split; first exact: measurableT.
    have H1 : paper_main_probability 0 d setT = 1%E by exact: probability_setT.
    rewrite H1 lee_fin; apply/RleP.
    rewrite /= Rmult_1_r.
    exact: paper_main_head_row_rpower_ge1.
  have -> : [set x : paper_main_sample 0 d | Rle (paper_main_head_row_count 0 d rho x) s] =
      set0.
    by apply/seteqP; split => x //= H; rewrite paper_main_head_row_count0 in H; lra.
  split; first exact: measurable0.
  have H0 : paper_main_probability 0 d set0 = 0%E by exact: measure0.
  rewrite H0 lee_fin; apply/RleP.
  rewrite /= Rmult_1_r.
  exact/Rlt_le/paper_main_head_row_rpower_pos.
have [mB HB] := IH (s - 1).
have [mC HC] := IH s.
rewrite paper_main_head_row_count_le_split.
split.
  have mU : measurable ((A `*` [set t | Rle (paper_main_head_row_count n d rho t) (s - 1)]) `|`
      (~` A `*` [set t | Rle (paper_main_head_row_count n d rho t) s])).
    by apply: measurableU; apply: measurableX => //; apply: measurableC.
  have H := paper_main_split_points_measurable 1 n d measurableT _ mU.
  by rewrite setTI in H.
change (paper_main_probability (1 + n) d (paper_main_split_points 1 n d @^-1`
  ((A `*` [set t | Rle (paper_main_head_row_count n d rho t) (s - 1)]) `|`
   (~` A `*` [set t | Rle (paper_main_head_row_count n d rho t) s]))) <=
  ((Rpower 2 s * (1 - p / 2) ^ n.+1)%Rcoq)%:E)%E.
rewrite paper_main_head_row_split_prob // Ha HAc.
set PB := paper_main_probability n d
  [set t | Rle (paper_main_head_row_count n d rho t) (s - 1)] in HB *.
set PC := paper_main_probability n d
  [set t | Rle (paper_main_head_row_count n d rho t) s] in HC *.
have HfB : PB \is a fin_num by apply: fin_num_measure.
have HfC : PC \is a fin_num by apply: fin_num_measure.
have HB0 : 0 <= fine PB by apply/RleP; apply: fine_ge0; exact: measure_ge0.
have HC0 : 0 <= fine PC by apply/RleP; apply: fine_ge0; exact: measure_ge0.
rewrite -(fineK HfB) -(fineK HfC) in HB HC *.
rewrite lee_fin in HB; move/RleP in HB.
rewrite lee_fin in HC; move/RleP in HC.
rewrite -!EFinM -EFinD lee_fin; apply/RleP.
have Hc : 0 <= (1 - p / 2) ^ n by apply: pow_le; lra.
have E : (1 - p / 2) ^ n.+1 = (1 - p / 2) ^ n * (1 - p / 2) by rewrite /= Rmult_comm.
rewrite E.
exact: (paper_main_head_row_lower_step a p ((1 - p / 2) ^ n) (fine PB) (fine PC) s
  Hp Hpa Ha1 Hc HB HC HB0 HC0).
Qed.

(* The binomial upper tail. *)

Theorem paper_main_head_row_count_upper d (rho : 'cV[R]_d -> Prop) (q : R) :
  measurable (paper_main_head_row_event d rho) -> 0 <= q ->
  (paper_main_probability 1 d (paper_main_head_row_event d rho) <= q%:E)%E ->
  forall n (s : R),
    measurable [set x : paper_main_sample n d | Rle s (paper_main_head_row_count n d rho x)] /\
    (paper_main_probability n d [set x | Rle s (paper_main_head_row_count n d rho x)] <=
      ((Rpower 2 (- s) * (1 + q) ^ n)%Rcoq)%:E)%E.
Proof.
move=> mA Hq0 HpA.
set A := paper_main_head_row_event d rho in mA HpA *.
have HfA : paper_main_probability 1 d A \is a fin_num by apply: fin_num_measure.
set a := fine (paper_main_probability 1 d A).
have Ha : paper_main_probability 1 d A = a%:E by rewrite /a fineK.
have Ha0 : 0 <= a by apply/RleP; apply: fine_ge0; exact: measure_ge0.
have Ha1 : a <= 1.
  have H := probability_le1 (gaussian_product_law (1 * d)%N) mA.
  have : (a%:E <= 1)%E by rewrite -Ha; exact: H.
  by rewrite lee_fin => /RleP.
have HAc : paper_main_probability 1 d (~` A) = (1 - a)%:E.
  have H := probability_setC (gaussian_product_law (1 * d)%N) mA.
  rewrite /paper_main_probability H.
  by rewrite -/(paper_main_probability 1 d A) Ha EFinB.
have Haq : a <= q.
  have : (a%:E <= q%:E)%E by rewrite -Ha.
  by rewrite lee_fin => /RleP.
elim=> [|n IH] s.
  case: (Rle_lt_dec s 0) => Hs.
    have -> : [set x : paper_main_sample 0 d | Rle s (paper_main_head_row_count 0 d rho x)] =
        setT.
      by apply/seteqP; split => x // _ /=; rewrite paper_main_head_row_count0.
    split; first exact: measurableT.
    have H1 : paper_main_probability 0 d setT = 1%E by exact: probability_setT.
    rewrite H1 lee_fin; apply/RleP.
    rewrite /= Rmult_1_r.
    apply: paper_main_head_row_rpower_ge1; lra.
  have -> : [set x : paper_main_sample 0 d | Rle s (paper_main_head_row_count 0 d rho x)] =
      set0.
    by apply/seteqP; split => x //= H; rewrite paper_main_head_row_count0 in H; lra.
  split; first exact: measurable0.
  have H0 : paper_main_probability 0 d set0 = 0%E by exact: measure0.
  rewrite H0 lee_fin; apply/RleP.
  rewrite /= Rmult_1_r.
  exact/Rlt_le/paper_main_head_row_rpower_pos.
have [mB HB] := IH (s - 1).
have [mC HC] := IH s.
rewrite paper_main_head_row_count_ge_split.
split.
  have mU : measurable ((A `*` [set t | Rle (s - 1) (paper_main_head_row_count n d rho t)]) `|`
      (~` A `*` [set t | Rle s (paper_main_head_row_count n d rho t)])).
    by apply: measurableU; apply: measurableX => //; apply: measurableC.
  have H := paper_main_split_points_measurable 1 n d measurableT _ mU.
  by rewrite setTI in H.
change (paper_main_probability (1 + n) d (paper_main_split_points 1 n d @^-1`
  ((A `*` [set t | Rle (s - 1) (paper_main_head_row_count n d rho t)]) `|`
   (~` A `*` [set t | Rle s (paper_main_head_row_count n d rho t)]))) <=
  ((Rpower 2 (- s) * (1 + q) ^ n.+1)%Rcoq)%:E)%E.
rewrite paper_main_head_row_split_prob // Ha HAc.
set PB := paper_main_probability n d
  [set t | Rle (s - 1) (paper_main_head_row_count n d rho t)] in HB *.
set PC := paper_main_probability n d
  [set t | Rle s (paper_main_head_row_count n d rho t)] in HC *.
have HfB : PB \is a fin_num by apply: fin_num_measure.
have HfC : PC \is a fin_num by apply: fin_num_measure.
rewrite -(fineK HfB) -(fineK HfC) in HB HC *.
rewrite lee_fin in HB; move/RleP in HB.
rewrite lee_fin in HC; move/RleP in HC.
rewrite -!EFinM -EFinD lee_fin; apply/RleP.
have Hc : 0 <= (1 + q) ^ n by apply: pow_le; lra.
have E : (1 + q) ^ n.+1 = (1 + q) ^ n * (1 + q) by rewrite /= Rmult_comm.
rewrite E.
exact: (paper_main_head_row_upper_step a q ((1 + q) ^ n) (fine PB) (fine PC) s
  Ha0 Haq Ha1 Hc HB HC).
Qed.

(* Exponential forms. *)

Lemma paper_main_head_row_exp_mul (u : R) (n : nat) : exp (u * INR n) = exp u ^ n.
Proof.
elim: n => [|n IH]; first by rewrite /= Rmult_0_r exp_0.
by rewrite S_INR Rmult_plus_distr_l Rmult_1_r exp_plus IH /= Rmult_comm.
Qed.

Lemma paper_main_head_row_pow_exp (u : R) (n : nat) :
  0 <= 1 + u -> (1 + u) ^ n <= exp (u * INR n).
Proof.
move=> Hu.
have H1 : 1 + u <= exp u by apply: exp_ineq1_le.
rewrite paper_main_head_row_exp_mul; apply: pow_incr; lra.
Qed.

Corollary paper_main_head_row_count_lower_exp d (rho : 'cV[R]_d -> Prop) (p : R) (n : nat) :
  measurable (paper_main_head_row_event d rho) -> 0 <= p ->
  (p%:E <= paper_main_probability 1 d (paper_main_head_row_event d rho))%E ->
  (paper_main_probability n d
    [set x | Rle (paper_main_head_row_count n d rho x) (p * INR n / 4)] <=
    ((exp (- (p * INR n) * (1 / 2 - ln 2 / 4)))%Rcoq)%:E)%E.
Proof.
move=> mA Hp HpA.
have Hp1 : p <= 1.
  have H := probability_le1 (gaussian_product_law (1 * d)%N) mA.
  have : (p%:E <= 1)%E by exact: le_trans HpA H.
  by rewrite lee_fin => /RleP.
have [_ H] := paper_main_head_row_count_lower d rho p mA Hp HpA n (p * INR n / 4).
apply: le_trans H _; rewrite lee_fin; apply/RleP.
have H1 : (1 - p / 2) ^ n <= exp (- (p / 2) * INR n).
  have -> : 1 - p / 2 = 1 + - (p / 2) by ring.
  by apply: paper_main_head_row_pow_exp; lra.
have H2 : 0 < Rpower 2 (p * INR n / 4) by exact: paper_main_head_row_rpower_pos.
have E : exp (- (p * INR n) * (1 / 2 - ln 2 / 4)) =
    Rpower 2 (p * INR n / 4) * exp (- (p / 2) * INR n).
  rewrite /Rpower -exp_plus; congr exp; field.
rewrite E; apply: Rmult_le_compat_l; lra.
Qed.

Corollary paper_main_head_row_count_upper_exp d (rho : 'cV[R]_d -> Prop) (q s : R) (n : nat) :
  measurable (paper_main_head_row_event d rho) -> 0 <= q ->
  (paper_main_probability 1 d (paper_main_head_row_event d rho) <= q%:E)%E ->
  (paper_main_probability n d
    [set x | Rle s (paper_main_head_row_count n d rho x)] <=
    ((exp (q * INR n - s * ln 2))%Rcoq)%:E)%E.
Proof.
move=> mA Hq HqA.
have [_ H] := paper_main_head_row_count_upper d rho q mA Hq HqA n s.
apply: le_trans H _; rewrite lee_fin; apply/RleP.
have H1 : (1 + q) ^ n <= exp (q * INR n) by apply: paper_main_head_row_pow_exp; lra.
have H2 : 0 < Rpower 2 (- s) by exact: paper_main_head_row_rpower_pos.
have E : exp (q * INR n - s * ln 2) = Rpower 2 (- s) * exp (q * INR n).
  rewrite /Rpower -exp_plus; congr exp; ring.
rewrite E; apply: Rmult_le_compat_l; lra.
Qed.
