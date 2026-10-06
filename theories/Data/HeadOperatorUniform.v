(* The raw head-data operator bound, uniformly over all injective selections
   of at most K sample points.

   x : paper_main_sample N d has the law paper_main_probability N d. For
   u > 0 put C = paper_main_gordon_entropy_constant (1/4) = 20 ln 2 and
   t = ln (K + 1) + K ln (N + 1) + u. There is a measurable event E with
   P(E) <= 2 exp(-u) such that outside E, for every m <= K and every
   injective s : 'I_m -> 'I_N,
     paper_main_head_data_gram x s <= 8 (C (d + K) + t) I
   in Loewner order (paper_main_data_head_operator_uniform).

   Construction. One pair of quarter nets is chosen for each column count m
   (pmdou_nets, from paper_main_gordon_operator_discretization by choice).
   The threshold b = paper_main_gaussian_operator_threshold d K t is common
   to all m <= K. The exception for (m, s) is the net-test event of
   Data.HeadOperator. For each m, its union over the finite
   functions sf : {ffun 'I_m -> 'I_N} with injectiveb sf has probability at
   most N^m 2 exp(-t) <= (N + 1)^K 2 exp(-t) (pmdou_level_rate). The union
   over 1 <= m <= K then has probability at most
   (K + 1) (N + 1)^K 2 exp(-t) = 2 exp(-u) (pmdou_count_rate). The
   combinatorial factor (K + 1) (N + 1)^K bounds sum_(m <= K) N^m. m = 0 is
   trivial (empty Gram); N = 0 leaves no selection with m > 0; d = 0 is
   trivial (0 x 0 matrices). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityProductDefinitions Gaussian.Law.ProductBasics
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous
  Geometry.HeadCorrection Geometry.HeadFeature Gordon.ProcessCovariance
  Gordon.Scalar Gordon.Bilinear Gordon.Nets Gordon.Entropy Gordon.OperatorNet
  Gaussian.Tail.LinearMeasurable Gaussian.Tail.UnitLinear
  Gaussian.Tail.UnionBound Gaussian.Symmetric.FeatureTail Data.SampleTail
  Data.HeadOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* Quarter nets for one column count. *)
Record pmdou_net := PmdouNet {
  pmdou_r : nat; pmdou_q : nat;
  pmdou_z : nat -> nat -> R; pmdou_w : nat -> nat -> R }.

Definition pmdou_good d m (nt : pmdou_net) : Prop :=
  [/\ (0 < pmdou_r nt)%coq_nat /\ (0 < pmdou_q nt)%coq_nat,
    (forall y, (y < pmdou_r nt)%N ->
      paper_main_gordon_dot d (pmdou_z nt y) (pmdou_z nt y) = 1),
    (forall t, (t < pmdou_q nt)%N ->
      paper_main_gordon_dot m (pmdou_w nt t) (pmdou_w nt t) = 1),
    ln (INR (pmdou_r nt)) + ln (INR (pmdou_q nt)) <=
      paper_main_gordon_entropy_constant (1/4) * (INR d + INR m) &
    forall xs B, List.length xs = (d * m)%N -> 0 <= B ->
      (forall y t, (y < pmdou_r nt)%coq_nat -> (t < pmdou_q nt)%coq_nat ->
        Rabs (paper_main_gordon_matrix_value d m (pmdou_z nt y) (pmdou_w nt t) xs) <= B) ->
      paper_main_gordon_operator_norm d m xs <= 2 * B].

Lemma pmdou_nets d : (0 < d)%N ->
  exists f : nat -> pmdou_net, forall m, (0 < m)%N -> pmdou_good d m (f m).
Proof.
move=> Hd.
have H : forall m, exists nt, (0 < m)%N -> pmdou_good d m nt.
  move=> m; case: (posnP m) => [->|Hm].
    by exists (PmdouNet 0 0 (fun _ _ => 0) (fun _ _ => 0)).
  have [r [q [z [w [Hr [Hq [Hz [Hw [Hent Hnet]]]]]]]]] :=
    paper_main_gordon_operator_discretization d m (elimT ssrnat.ltP Hd) (elimT ssrnat.ltP Hm).
  exists (PmdouNet r q z w) => _; split => //=.
  - by move=> y /ssrnat.ltP; exact: Hz.
  - by move=> t /ssrnat.ltP; exact: Hw.
have [g Hg] := choice H.
by exists g.
Qed.

Lemma pmdou_ln_ge0 x : 1 <= x -> 0 <= ln x.
Proof.
move=> Hx; rewrite -ln_1; case: (Rle_lt_or_eq_dec 1 x Hx) => [H|<-]; last exact: Rle_refl.
by apply: Rlt_le; apply: ln_increasing => //; lra.
Qed.

(* The counting arithmetic. *)
Lemma pmdou_INR_expn N m : INR (N ^ m)%N = INR N ^ m.
Proof. by elim: m => [//|m IH]; rewrite expnS -multE mult_INR IH. Qed.

Lemma pmdou_level_rate N m K (t : R) : (m <= K)%coq_nat ->
  INR (N ^ m)%N * (2 * exp (- t)) <= (INR N + 1) ^ K * (2 * exp (- t)).
Proof.
move=> HmK; rewrite pmdou_INR_expn.
apply: Rmult_le_compat_r; first by have := exp_pos (- t); lra.
apply: Rle_trans (_ : INR N ^ m <= (INR N + 1) ^ m) _.
  by apply: pow_incr; have := pos_INR N; lra.
by apply: Rle_pow => //; have := pos_INR N; lra.
Qed.

Lemma pmdou_count_rate N K u :
  (INR K + 1) * ((INR N + 1) ^ K *
    (2 * exp (- (ln (INR K + 1) + INR K * ln (INR N + 1) + u)))) = 2 * exp (- u).
Proof.
have HK : 0 < INR K + 1 by have := pos_INR K; lra.
have HN : 0 < INR N + 1 by have := pos_INR N; lra.
have HNK : 0 < (INR N + 1) ^ K by exact: pow_lt.
have E1 : exp (- (ln (INR K + 1) + INR K * ln (INR N + 1) + u)) =
    / (INR K + 1) * / (INR N + 1) ^ K * exp (- u).
  rewrite -(ln_pow _ HN) !Ropp_plus_distr !exp_plus !exp_Ropp !exp_ln //.
rewrite E1; field; lra.
Qed.

Section Uniform.
Variables (N d : nat) (f : nat -> pmdou_net) (b : R).

Definition pmdou_event m (s : 'I_m -> 'I_N) : set (paper_main_sample N d) :=
  pmdo_test_set N d m s (pmdou_r (f m)) (pmdou_q (f m)) (pmdou_z (f m)) (pmdou_w (f m)) b.

(* All injective selections of m points, as a finite union. *)
Definition pmdou_level m : set (paper_main_sample N d) :=
  [set x | exists sf : {ffun 'I_m -> 'I_N}, injectiveb sf /\ pmdou_event m sf x].

Definition pmdou_index m (j : nat) : set (paper_main_sample N d) :=
  if (insub j : option 'I_#|{ffun 'I_m -> 'I_N}|) is Some j'
  then (if injectiveb (enum_val j') then pmdou_event m (enum_val j') else set0)
  else set0.

Lemma pmdou_levelE m :
  pmdou_level m =
  paper_main_finite_event_union (List.seq 0 #|{ffun 'I_m -> 'I_N}|) (pmdou_index m).
Proof.
apply/seteqP; split => x.
- move=> [sf [Hi H]]; apply/paper_main_finite_event_union_member.
  exists (enum_rank sf : nat); split.
    by apply/List.in_seq; split; [lia | have /ssrnat.ltP := ltn_ord (enum_rank sf)].
  by rewrite /pmdou_index valK enum_rankK Hi.
- move/paper_main_finite_event_union_member => [j [_ H]].
  move: H; rewrite /pmdou_index; case: insubP => [j' _ _ | _ []].
  case Hi: (injectiveb (enum_val j')) => // H.
  by exists (enum_val j').
Qed.

(* All selections of 1 <= m <= K points. *)
Definition pmdou_event_all K : set (paper_main_sample N d) :=
  [set x | exists m, (0 < m)%N /\ (m <= K)%N /\ pmdou_level m x].

Definition pmdou_count_index (m : nat) : set (paper_main_sample N d) :=
  if (0 < m)%N then pmdou_level m else set0.

Lemma pmdou_event_allE K :
  pmdou_event_all K = paper_main_finite_event_union (List.seq 0 (K + 1)) pmdou_count_index.
Proof.
apply/seteqP; split => x.
- move=> [m [Hm [HmK H]]]; apply/paper_main_finite_event_union_member.
  exists m; split; last by rewrite /pmdou_count_index Hm.
  apply/List.in_seq; split; first lia.
  by have /ssrnat.leP := HmK; rewrite -plusE; lia.
- move/paper_main_finite_event_union_member => [m [Hm H]].
  move: H; rewrite /pmdou_count_index; case: (posnP m) => [_ /= []|Hm0 /= H].
  exists m; split => //; split => //.
  by apply/ssrnat.leP; move/List.in_seq: Hm; rewrite -plusE; lia.
Qed.

End Uniform.

Lemma pmdou_gram_finfun N d m (x : paper_main_sample N d) (s : 'I_m -> 'I_N) :
  paper_main_head_data_gram x (finfun s) = paper_main_head_data_gram x s.
Proof. by apply: eq_bigr => k _; rewrite ffunE. Qed.

Lemma pmdou_loewner_dim0 N (x : paper_main_sample N 0) m (s : 'I_m -> 'I_N) (B : R) :
  paper_main_loewner_le (paper_main_head_data_gram x s) (B *: 1%:M)%R.
Proof. by split; [move=> [] | move=> v; rewrite /paper_main_quadratic_form big_ord0]. Qed.

Lemma pmdou_loewner_m0 N d (x : paper_main_sample N d) (s : 'I_0 -> 'I_N) (B : R) :
  0 <= B -> paper_main_loewner_le (paper_main_head_data_gram x s) (B *: 1%:M)%R.
Proof.
move=> HB; rewrite /paper_main_loewner_le /paper_main_head_data_gram big_ord0 subr0.
by apply: pmh_psd_scalar; apply/RleP.
Qed.

(* The uniform bound. *)
Theorem paper_main_data_head_operator_uniform N d K (u : R) :
  0 < u ->
  exists E : set (paper_main_sample N d),
    measurable E /\
    (paper_main_probability N d E <= (2 * exp (- u))%:E)%E /\
    forall x, ~ E x -> forall m (s : 'I_m -> 'I_N), (m <= K)%N -> injective s ->
      paper_main_loewner_le (paper_main_head_data_gram x s)
        ((8 * (paper_main_gordon_entropy_constant (1/4) * (INR d + INR K) +
          (ln (INR K + 1) + INR K * ln (INR N + 1) + u)) : R) *: 1%:M)%R.
Proof.
move=> Hu.
have Hpos2 : (0%:E <= (2 * exp (- u))%:E)%E.
  rewrite lee_fin; apply: mulr_ge0 => //; apply/RleP; exact: Rlt_le _ _ (exp_pos _).
case: (posnP d) => [Hd0|Hd].
  exists set0; split; first exact: measurable0.
  split; first by rewrite /paper_main_probability measure0.
  move: Hd0 => -> x _ m s _ _; exact: pmdou_loewner_dim0.
have [f Hf] := pmdou_nets d Hd.
set C := paper_main_gordon_entropy_constant (1/4).
have HC : 0 < C := paper_main_gaussian_entropy_positive.
set t := ln (INR K + 1) + INR K * ln (INR N + 1) + u.
have HlnK : 0 <= ln (INR K + 1) by apply: pmdou_ln_ge0; have := pos_INR K; lra.
have HlnN : 0 <= ln (INR N + 1) by apply: pmdou_ln_ge0; have := pos_INR N; lra.
have Ht : 0 < t by have := pos_INR K; rewrite /t; nra.
have HD : 0 <= INR d + INR K by have := pos_INR d; have := pos_INR K; lra.
have Hpos : 0 < 2 * (C * (INR d + INR K) + t) by nra.
set b := paper_main_gaussian_operator_threshold d K t.
have Hb2 : b ^ 2 = 2 * (C * (INR d + INR K) + t).
  by rewrite /b /paper_main_gaussian_operator_threshold -/C (pow2_sqrt _ (Rlt_le _ _ Hpos)).
have Hb : 0 < b.
  by rewrite /b /paper_main_gaussian_operator_threshold -/C; exact: sqrt_lt_R0.
(* One injective selection with 1 <= m <= K. *)
have Hsel : forall m (sf : 'I_m -> 'I_N), (0 < m)%N -> (m <= K)%N -> injective sf ->
    measurable (pmdou_event N d f b m sf) /\
    (gaussian_product_law (N * d) (pmdou_event N d f b m sf) <= (2 * exp (- t))%:E)%E.
  move=> m sf Hm HmK Hs.
  have [[Hr Hq] Hz Hw Hent _] := Hf m Hm.
  have [HM HP] := pmdo_test_tail N d m sf _ _ _ _ b Hs Hb Hz Hw.
  split => //; apply: le_trans HP _; rewrite lee_fin; apply/RleP.
  apply: (pmdo_rate _ _ C (INR d + INR K) t b Hr Hq) => //.
  apply: Rle_trans Hent _; rewrite -/C; apply: Rmult_le_compat_l; first lra.
  by have := le_INR _ _ (elimT ssrnat.leP HmK); lra.
(* One level m: at most N^m selections. *)
have Hlevel : forall m, (0 < m)%N -> (m <= K)%N ->
    measurable (pmdou_level N d f b m) /\
    (gaussian_product_law (N * d) (pmdou_level N d f b m) <=
      ((INR N + 1) ^ K * (2 * exp (- t)))%:E)%E.
  move=> m Hm HmK.
  have HM : forall j, List.In j (List.seq 0 #|{ffun 'I_m -> 'I_N}|) ->
      measurable (pmdou_index N d f b m j).
    move=> j _; rewrite /pmdou_index; case: insubP => [j' _ _ | _]; last exact: measurable0.
    case Hi: (injectiveb (enum_val j')); last exact: measurable0.
    exact: (Hsel m _ Hm HmK (elimT (injectiveP _) Hi)).1.
  have HP : forall j, List.In j (List.seq 0 #|{ffun 'I_m -> 'I_N}|) ->
      (gaussian_product_law (N * d) (pmdou_index N d f b m j) <= (2 * exp (- t))%:E)%E.
    have H2t : (0%:E <= (2 * exp (- t))%:E)%E.
      rewrite lee_fin; apply: mulr_ge0 => //; apply/RleP; exact: Rlt_le _ _ (exp_pos _).
    move=> j _; rewrite /pmdou_index; case: insubP => [j' _ _ | _]; last by rewrite measure0.
    case Hi: (injectiveb (enum_val j')); last by rewrite measure0.
    exact: (Hsel m _ Hm HmK (elimT (injectiveP _) Hi)).2.
  rewrite pmdou_levelE; split; first exact: paper_main_gaussian_union_measurable.
  apply: le_trans.
    exact: (paper_main_gaussian_union_bound (N * d) _ _ _ HM HP).
  rewrite List.length_seq card_ffun !card_ord lee_fin; apply/RleP.
  exact: (pmdou_level_rate N m K t (elimT ssrnat.leP HmK)).
exists (pmdou_event_all N d f b K).
have HMc : forall m, List.In m (List.seq 0 (K + 1)) ->
    measurable (pmdou_count_index N d f b m).
  move=> m Hm; rewrite /pmdou_count_index; case: (posnP m) => [_|Hm0] /=.
    exact: measurable0.
  by apply: (Hlevel m Hm0 _).1; apply/ssrnat.leP; move/List.in_seq: Hm; rewrite -plusE; lia.
have HPc : forall m, List.In m (List.seq 0 (K + 1)) ->
    (gaussian_product_law (N * d) (pmdou_count_index N d f b m) <=
      ((INR N + 1) ^ K * (2 * exp (- t)))%:E)%E.
  move=> m Hm; rewrite /pmdou_count_index; case: (posnP m) => [_|Hm0] /=.
    rewrite measure0 lee_fin; apply: mulr_ge0; first by apply/RleP; apply: pow_le;
      have := pos_INR N; lra.
    by apply: mulr_ge0 => //; apply/RleP; exact: Rlt_le _ _ (exp_pos _).
  by apply: (Hlevel m Hm0 _).2; apply/ssrnat.leP; move/List.in_seq: Hm; rewrite -plusE; lia.
rewrite pmdou_event_allE; split; first exact: paper_main_gaussian_union_measurable.
split.
  apply: le_trans.
    exact: (paper_main_gaussian_union_bound (N * d) _ _ _ HMc HPc).
  rewrite List.length_seq lee_fin; apply/RleP.
  rewrite -RmultE plus_INR /= (pmdou_count_rate N K u).
  exact: Rle_refl.
move=> x Hx m s HmK Hs.
have HB0 : 0 <= 8 * (C * (INR d + INR K) + t) by nra.
case: (posnP m) => [Hm0|Hm].
  by move: s Hs; rewrite Hm0 => s _; exact: pmdou_loewner_m0.
have [[Hr Hq] Hz Hw _ Hnet] := Hf m Hm.
pose sf := finfun s.
have Hsf : injectiveb sf by apply/injectiveP => k k'; rewrite !ffunE; exact: Hs.
have Hnot : ~ pmdou_event N d f b m sf x.
  move=> H; apply: Hx; rewrite -pmdou_event_allE.
  by exists m; split => //; split => //; exists sf.
have Hlen := pmdo_list_length N d m sf (tval x).
have Htests : forall y t', (y < pmdou_r (f m))%coq_nat -> (t' < pmdou_q (f m))%coq_nat ->
    Rabs (paper_main_gordon_matrix_value d m (pmdou_z (f m) y) (pmdou_w (f m) t')
      (pmdo_list N d m sf (tval x))) <= b.
  move=> y t' Hy Ht'; apply: Rlt_le; apply: Rnot_le_lt => H; apply: Hnot.
  by exists y, t'; split; [exact/ssrnat.ltP | split; [exact/ssrnat.ltP | exact: H]].
have Hnorm := Hnet _ b Hlen (Rlt_le _ _ Hb) Htests.
have Hbound := proj2 (paper_main_gordon_operator_norm_characterization d m _ (2 * b) Hlen) Hnorm.
have -> : 8 * (C * (INR d + INR K) + t) = (2 * b) ^ 2.
  by rewrite Rpow_mult_distr Hb2; ring.
by rewrite -pmdou_gram_finfun; exact: pmdo_loewner Hbound.
Qed.
