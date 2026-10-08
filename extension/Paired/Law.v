(* The paired law as a finite mixture of product laws, at Stdlib's R: item
   P2 of phase 6 (notes/paired-law-plan-v2.md, section 4.3;
   notes/mixture-product-universality.md, section 5). The definitions are
   those of PairedDefinitions: h = paired_kernel and the pair density
   paired_pair_density eps x y = 1 + eps h(x) h(y).

   1. The pair density as a mixture of two products. For eps < 0, with
      s = sqrt (- eps),
        1 + eps h(x) h(y) =
          ((1 + s h(x)) (1 - s h(y)) + (1 - s h(x)) (1 + s h(y))) / 2,
      and for eps >= 0,
        1 + eps h(x) h(y) =
          eps / (1 + eps) (1 - h(x)) (1 - h(y)) +
          1 / (1 + eps) (1 + eps h(x)) (1 + eps h(y)).
      pair_weight eps b, pair_left eps b and pair_right eps b, b : bool,
      are the weight and the two parameters of each term
      (pair_density_mix). The weights are nonnegative of sum one
      (pair_weight_ge0, pair_weight_sum); for -1 <= eps <= 7/3 the
      parameters lie in [-1, 7/3] (pair_left_range, pair_right_range),
      the range where 1 + a h is nonnegative on [-sqrt 3, sqrt 3]; their
      means under the weights vanish (pair_left_mean, pair_right_mean), so
      the fourth moments of the mixture are those of the uniform law.
   2. Products: a product over the coordinates j < 2 m regroups into a
      product over the pairs (prod_pairs, prod_pairs_odd for any d), and a
      product over the n * d coordinates of a sample into a product over
      the points and their coordinates (prod_flat).
   3. The density of a point. A component of the law of a point is a
      tuple c of d / 2 bits, one per pair; coordinate j of component c has
      the parameter paired_param eps d c j: pair_left or pair_right of the
      bit of its pair, and 0 for the last coordinate of an odd d; the
      weight of c is the product of the weights of its bits
      (paired_cweight). Then the density of a point is the mixture
      \prod_k (1 + eps h(x_(2k)) h(x_(2k+1))) =
        \sum_c paired_cweight eps d c \prod_(j < d) (1 + a_(c, j) h(x_j))
      (paired_point_density), by big_tuple_distr of
      library/probability/mixture.v. The mean of a parameter under the
      weights vanishes (paired_param_mean).
   4. The components as indices: paired_N d is the number of tuples of
      d / 2 bits, and component c < paired_N d is the tuple enum_val c
      (paired_comp, sum_paired_comp).
   5. The paired law as a finite mixture of product laws, for
      -1 <= eps <= 7/3 and a law mu with paired_uniform_spec mu (the
      uniform law): component c has weight paired_w eps d c, the weight of
      its tuple, and coordinate j of component c has the law
      paired_mu eps mu d c j = paired_law mu a with a = paired_param of the
      tuple (Paired/Uniform). The weights are nonnegative of sum one
      (paired_w_ge0, paired_w_sum), the coordinate laws are component laws
      with constant 3 (paired_mu_component), and every coordinate has the
      fourth moment 9/5 under the mixture (paired_mu_fourth: the fourth
      moment of paired_law mu a is 9/5 + 8 a / 35, and the means of the
      parameters vanish). paired_probability_mixture: on every measurable
      event, paired_probability eps mu n d is the mixture_probability of
      these components. The proof expands the sample density into a sum,
      over the label tuples of the n points, of the weights times the
      products of the densities 1 + a h at the coordinates
      (paired_point_density for each point, big_tuple_distr for the
      points, prod_flat); outside the null event where a coordinate leaves
      [-sqrt 3, sqrt 3] (paired_uniform_null), these are the densities
      paired_density of Paired/Uniform, and the integral of their product
      over the event is the labelled law (tuple_prod_density of
      library/probability/density_law.v). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg density_law mixture.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions PairedDefinitions.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Paired Require Import Uniform.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The pair density as a mixture of two products. *)

Definition pair_weight (eps : R) (b : bool) : R :=
  if eps < 0 then 2^-1 else if b then (1 + eps)^-1 else eps / (1 + eps).

Definition pair_left (eps : R) (b : bool) : R :=
  if eps < 0 then (if b then Num.sqrt (- eps) else - Num.sqrt (- eps))
  else if b then eps else -1.

Definition pair_right (eps : R) (b : bool) : R :=
  if eps < 0 then - pair_left eps b else pair_left eps b.

Lemma pair_weight_ge0 eps b : 0 <= pair_weight eps b.
Proof.
rewrite /pair_weight; case: ltP => [_|e0] /=; first by rewrite invr_ge0 ler0n.
have e1 : 0 < 1 + eps by apply: (lt_le_trans ltr01); rewrite lerDl.
by case: b; rewrite ?invr_ge0 ?divr_ge0 // ltW.
Qed.

Lemma pair_weight_sum eps : \sum_(b : bool) pair_weight eps b = 1.
Proof.
rewrite big_bool /pair_weight; case: ltP => [_|e0] /=; first by field.
have e1 : 1 + eps != 0.
  by rewrite gt_eqF //; apply: (lt_le_trans ltr01); rewrite lerDl.
by field.
Qed.

Lemma pair_density_mix eps x y :
  paired_pair_density eps x y =
  \sum_(b : bool) pair_weight eps b *
    ((1 + pair_left eps b * paired_kernel x) *
     (1 + pair_right eps b * paired_kernel y)).
Proof.
rewrite big_bool /paired_pair_density /pair_weight /pair_right /pair_left.
set hx := paired_kernel x; set hy := paired_kernel y.
case: ltP => [e0|e0] /=.
  have ss : Num.sqrt (- eps) ^+ 2 = - eps by rewrite sqr_sqrtr // oppr_ge0 ltW.
  move: ss; set s := Num.sqrt (- eps) => ss.
  have -> : eps = - s ^+ 2 by rewrite ss opprK.
  by field.
have e1 : 1 + eps != 0.
  by rewrite gt_eqF //; apply: (lt_le_trans ltr01); rewrite lerDl.
by field.
Qed.

Lemma pair_left_range eps b : - 1 <= eps <= 7%:R / 3%:R ->
  - 1 <= pair_left eps b <= 7%:R / 3%:R.
Proof.
move=> /andP[e1 e2]; rewrite /pair_left.
have h73 : 1 <= 7%:R / 3%:R :> R by rewrite ler_pdivlMr // mul1r ler_nat.
case: ltP => [e0|e0] /=; last by case: b => /=; apply/andP; split; lra.
have s1 : Num.sqrt (- eps) <= 1 by rewrite -sqrtr1 ler_sqrt ?ler01 // lerNl.
have s0 : 0 <= Num.sqrt (- eps) := sqrtr_ge0 _.
by case: b => /=; apply/andP; split; lra.
Qed.

Lemma pair_right_range eps b : - 1 <= eps <= 7%:R / 3%:R ->
  - 1 <= pair_right eps b <= 7%:R / 3%:R.
Proof.
move=> he; rewrite /pair_right; case: ltP => e0 /=; last exact: pair_left_range.
have h73 : 1 <= 7%:R / 3%:R :> R by rewrite ler_pdivlMr // mul1r ler_nat.
have s0 : 0 <= Num.sqrt (- eps) := sqrtr_ge0 _.
have s1 : Num.sqrt (- eps) <= 1.
  by case/andP: he => e1 _; rewrite -sqrtr1 ler_sqrt ?ler01 // lerNl.
rewrite /pair_left e0 /=.
by case: b => /=; apply/andP; split; lra.
Qed.

Lemma pair_left_mean eps :
  \sum_(b : bool) pair_weight eps b * pair_left eps b = 0.
Proof.
rewrite big_bool /pair_weight /pair_left; case: ltP => [_|e0] /=.
  by rewrite mulrN addrN.
have e1 : 1 + eps != 0.
  by rewrite gt_eqF //; apply: (lt_le_trans ltr01); rewrite lerDl.
by field.
Qed.

Lemma pair_right_mean eps :
  \sum_(b : bool) pair_weight eps b * pair_right eps b = 0.
Proof.
rewrite /pair_right; case: ltP => _ /=; last exact: pair_left_mean.
under eq_bigr do rewrite mulrN.
by rewrite sumrN pair_left_mean oppr0.
Qed.

(* 2. Products over pairs and over the coordinates of a sample. *)

Lemma prod_pairs (m : nat) (G : nat -> R) :
  \prod_(j < m.*2) G j = \prod_(k < m) (G k.*2 * G k.*2.+1).
Proof.
elim: m => [|m IH]; first by rewrite !big_ord0.
by rewrite doubleS !big_ord_recr /= IH mulrA.
Qed.

(* For an odd d, the last coordinate has no pair; its factor is one. *)
Lemma prod_pairs_odd (d : nat) (G : nat -> R) : (odd d -> G d.-1 = 1) ->
  \prod_(j < d) G j = \prod_(k < d./2) (G k.*2 * G k.*2.+1).
Proof.
move=> h1; rewrite -prod_pairs.
have hd : d = (d./2.*2 + odd d)%N by rewrite addnC odd_double_half.
move: h1; move: (d./2) (odd d) hd => m b -> /=.
case: b => /= [h1|_]; last by rewrite addn0.
have h2 : G m.*2 = 1 by move: h1; rewrite addn1 /= => h1; exact: h1.
by rewrite addn1 big_ord_recr /= h2 mulr1.
Qed.

Lemma prod_flat (n d : nat) (F : nat -> R) :
  \prod_(k < n * d) F k = \prod_(i < n) \prod_(j < d) F (i * d + j)%N.
Proof.
elim: n => [|n IH]; first by rewrite mul0n !big_ord0.
by rewrite big_ord_recr /= -IH mulSnr big_split_ord.
Qed.

(* 3. The density of a point. *)

(* The parameter of coordinate j in the component c of the law of a point:
   one bit per pair (2k, 2k + 1), the left parameter for the even
   coordinate and the right one for the odd coordinate, and 0 for the last
   coordinate of an odd d. *)
Definition paired_param (eps : R) (d : nat) (c : (d./2).-tuple bool)
    (j : nat) : R :=
  if (j < (d./2).*2)%N then
    (if odd j then pair_right eps (nth false c j./2)
     else pair_left eps (nth false c j./2))
  else 0.

(* The weight of a component. *)
Definition paired_cweight (eps : R) (d : nat) (c : (d./2).-tuple bool) : R :=
  \prod_(k < d./2) pair_weight eps (tnth c k).

Lemma paired_cweight_ge0 eps d c : 0 <= paired_cweight eps d c.
Proof. by apply: prodr_ge0 => k _; exact: pair_weight_ge0. Qed.

Lemma paired_cweight_sum eps d :
  \sum_(c : (d./2).-tuple bool) paired_cweight eps d c = 1.
Proof.
rewrite /paired_cweight (big_tuple_distr (fun _ b => pair_weight eps b)).
by rewrite big1 // => k _; exact: pair_weight_sum.
Qed.

Lemma paired_param_range eps d c j : - 1 <= eps <= 7%:R / 3%:R ->
  - 1 <= paired_param eps d c j <= 7%:R / 3%:R.
Proof.
move=> he; rewrite /paired_param; case: ifP => _.
  by case: ifP => _; [exact: pair_right_range | exact: pair_left_range].
have h73 : 0 <= 7%:R / 3%:R :> R by rewrite divr_ge0 // ler0n.
by apply/andP; split => //; rewrite lerNl oppr0 ler01.
Qed.

Lemma paired_point_density (eps : R) (d : nat) (x : nat -> R) :
  \prod_(k < d./2) paired_pair_density eps (x (2 * k)%N) (x (2 * k + 1)%N) =
  \sum_(c : (d./2).-tuple bool) paired_cweight eps d c *
    \prod_(j < d) (1 + paired_param eps d c j * paired_kernel (x j)).
Proof.
under eq_bigr do rewrite pair_density_mix.
rewrite -(big_tuple_distr (fun k b => pair_weight eps b *
  ((1 + pair_left eps b * paired_kernel (x (2 * k)%N)) *
   (1 + pair_right eps b * paired_kernel (x (2 * k + 1)%N))))).
apply: eq_bigr => c _; rewrite big_split /= -/(paired_cweight eps d c).
congr (_ * _).
pose G j := 1 + paired_param eps d c j * paired_kernel (x j).
have hlast : odd d -> G d.-1 = 1.
  by move=> od; rewrite /G /paired_param (odd_halfK od) ltnn /= mul0r addr0.
rewrite (prod_pairs_odd d G hlast); apply: eq_bigr => k _.
have kd : (k.*2.+1 < (d./2).*2)%N by rewrite ltn_Sdouble ltn_ord.
have kd' : (k.*2 < (d./2).*2)%N by rewrite ltn_double ltn_ord.
rewrite /G /paired_param kd kd' /= odd_double /= uphalf_double half_double.
by rewrite -(tnth_nth false c k) mul2n addn1.
Qed.

(* The mean of a parameter under the weights of the components vanishes:
   the fourth moments of the mixture are those of the uniform law. *)
Lemma paired_param_mean eps d (j : nat) :
  \sum_(c : (d./2).-tuple bool) paired_cweight eps d c * paired_param eps d c j
  = 0.
Proof.
rewrite /paired_param; case jd : (j < (d./2).*2)%N => /=; last first.
  by rewrite big1 // => c _; rewrite mulr0.
have jk : (j./2 < d./2)%N by rewrite ltn_half_double.
pose k0 : 'I_(d./2) := Ordinal jk.
pose a b := if odd j then pair_right eps b else pair_left eps b.
have e (c : (d./2).-tuple bool) :
    paired_cweight eps d c *
      (if odd j then pair_right eps (nth false c j./2)
       else pair_left eps (nth false c j./2)) =
    \prod_(k < d./2)
      (pair_weight eps (tnth c k) * (if k == k0 then a (tnth c k) else 1)).
  rewrite big_split /= -/(paired_cweight eps d c); congr (_ * _).
  rewrite (bigD1 k0) //= eqxx big1; first by move=> k /negPf ->.
  by rewrite mulr1 /a (tnth_nth false).
rewrite (eq_bigr _ (fun c _ => e c)).
rewrite (big_tuple_distr (fun k b =>
  pair_weight eps b * (if k == k0 then a b else 1))).
rewrite (bigD1 k0) //= eqxx.
have -> : \sum_(b : bool) pair_weight eps b * a b = 0.
  rewrite /a; case: (odd j) => /=.
    exact: pair_right_mean.
  exact: pair_left_mean.
by rewrite mul0r.
Qed.

(* 4. The components as indices: component c < paired_N d is the tuple of
   bits enum_val c. *)

Definition paired_N (d : nat) : nat := #|{: (d./2).-tuple bool}|.

Definition paired_comp (d c : nat) : (d./2).-tuple bool :=
  if (insub c : option 'I_(paired_N d)) is Some c' then enum_val c'
  else [tuple of nseq (d./2) false].

Lemma paired_compE d (c : 'I_(paired_N d)) : paired_comp d c = enum_val c.
Proof. by rewrite /paired_comp valK. Qed.

Lemma sum_paired_comp d (F : (d./2).-tuple bool -> R) :
  \sum_(c < paired_N d) F (paired_comp d c) = \sum_(t : (d./2).-tuple bool) F t.
Proof.
under eq_bigr do rewrite paired_compE.
by rewrite [RHS](reindex _ (onW_bij _ (enum_val_bij _))).
Qed.

(* The label of point i < n of a sample, read at its coordinates. *)
Lemma mixture_label_flat (N n d : nat) (s : n.-tuple 'I_N) (i : 'I_n) j :
  (j < d)%N -> mixture_label s ((i * d + j) %/ d) = tnth s i.
Proof.
move=> jd; have d0 : (0 < d)%N by apply: leq_ltn_trans jd.
rewrite divnMDl // divn_small // addn0.
by rewrite /mixture_label (nth_map (tnth s i)) ?size_tuple // -tnth_nth.
Qed.

(* 5. The paired law as a finite mixture of product laws. *)

Section paired_mixture.
Variables (eps : R) (mu : probability (measurableTypeR R) R).

(* The weight of component c and the law of coordinate j in it. *)
Definition paired_w (d c : nat) : R := paired_cweight eps d (paired_comp d c).

Definition paired_mu (d c j : nat) : probability (measurableTypeR R) R :=
  paired_law mu (paired_param eps d (paired_comp d c) j).

Hypothesis he : - 1 <= eps <= 7%:R / 3%:R.
Hypothesis hmu : paired_uniform_spec mu.

Lemma paired_w_ge0 d c : 0 <= paired_w d c.
Proof. exact: paired_cweight_ge0. Qed.

Lemma paired_w_sum d : \sum_(c < paired_N d) paired_w d c = 1.
Proof.
by rewrite /paired_w (sum_paired_comp d (paired_cweight eps d)) paired_cweight_sum.
Qed.

Lemma paired_mu_component d c j : mixture_component_law 3%:R (paired_mu d c j).
Proof. exact: (paired_law_component mu hmu _ (paired_param_range _ _ _ _ he)). Qed.

Lemma paired_mu_fourth d j :
  (\sum_(c < paired_N d)
     (paired_w d c)%:E * 'E_(paired_mu d c j)[universality_power 4])%E =
  (9%:R / 5%:R)%:E.
Proof.
have e (c : 'I_(paired_N d)) :
    ((paired_w d c)%:E * 'E_(paired_mu d c j)[universality_power 4])%E =
    (9%:R / 5%:R * paired_w d c +
     8%:R / 35%:R * (paired_w d c * paired_param eps d (paired_comp d c) j))%:E.
  rewrite /paired_mu (paired_law_fourth mu hmu _ (paired_param_range _ _ _ _ he)).
  by rewrite -EFinM; congr (_%:E); field.
rewrite (eq_bigr _ (fun c _ => e c)) sumEFin big_split /= -!mulr_sumr.
rewrite paired_w_sum /paired_w.
rewrite (sum_paired_comp d (fun t => paired_cweight eps d t * paired_param eps d t j)).
by rewrite paired_param_mean mulr1 mulr0 addr0.
Qed.

(* The kernel is a polynomial, hence measurable. *)
Lemma measurable_paired_kernel :
  measurable_fun setT (paired_kernel : measurableTypeR R -> measurableTypeR R).
Proof. exact: continuous_measurable_fun (continuous_legendre4 _). Qed.

(* The paired law of a sample is the mixture of the labelled laws. *)
Theorem paired_probability_mixture n d (E : set (paper_main_sample n d)) :
  measurable E ->
  paired_probability eps mu n d E =
  mixture_probability (paired_N d) (paired_w d) (paired_mu d) n d E.
Proof.
move=> mE.
pose a (s : n.-tuple 'I_(paired_N d)) (k : nat) :=
  paired_param eps d (paired_comp d (mixture_label s (k %/ d))) (k %% d).
have ha s k : - 1 <= a s k <= 7%:R / 3%:R by exact: paired_param_range.
pose W (s : n.-tuple 'I_(paired_N d)) := \prod_(i < n) paired_w d (tnth s i).
have W0 s : 0 <= W s by apply: prodr_ge0 => i _; exact: paired_w_ge0.
pose D (x : paper_main_sample n d) := \sum_(s : n.-tuple 'I_(paired_N d))
  W s * \prod_(k < n * d) (1 + a s k * paired_kernel (tnth x k)).
pose G s (x : paper_main_sample n d) :=
  \prod_(k < n * d) paired_density (a s k) (tnth x k).
have G0 s x : 0 <= G s x.
  by apply: prodr_ge0 => k _; exact: legendre_density_ge0.
(* the density of a sample, expanded *)
have hD x : paired_sample_density eps n d x = D x.
  have hp (i : 'I_n) :
      \prod_(k < d./2) paired_pair_density eps
        (List.nth (i * d + 2 * k) (tval x) 0)
        (List.nth (i * d + 2 * k + 1) (tval x) 0) =
      \sum_(c < paired_N d) paired_w d c *
        \prod_(j < d) (1 + paired_param eps d (paired_comp d c) j *
                          paired_kernel (List.nth (i * d + j) (tval x) 0)).
    under eq_bigr do rewrite -addnA.
    rewrite (paired_point_density eps d
      (fun j => List.nth (i * d + j) (tval x) 0)) /paired_w.
    by rewrite (sum_paired_comp d (fun t => paired_cweight eps d t *
      \prod_(j < d) (1 + paired_param eps d t j *
                        paired_kernel (List.nth (i * d + j) (tval x) 0)))).
  rewrite /paired_sample_density (eq_bigr _ (fun i _ => hp i)).
  rewrite -(big_tuple_distr (fun (i : 'I_n) (c : 'I_(paired_N d)) =>
    paired_w d c *
    \prod_(j < d) (1 + paired_param eps d (paired_comp d c) j *
                      paired_kernel (List.nth (i * d + j) (tval x) 0)))).
  apply: eq_bigr => s _; rewrite big_split /=; congr (_ * _).
  have -> : \prod_(k < n * d) (1 + a s k * paired_kernel (tnth x k)) =
      \prod_(k < n * d) (1 + a s k * paired_kernel (List.nth k (tval x) 0)).
    by apply: eq_bigr => k _; rewrite (tnth_nth 0) List_nthE.
  rewrite (prod_flat n d (fun k => 1 + a s k *
    paired_kernel (List.nth k (tval x) 0))).
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  by rewrite /a mixture_label_flat // modnMDl modn_small.
(* the coordinates lie in [-sqrt 3, sqrt 3] almost surely *)
pose B (k : 'I_(n * d)) :=
  [set x : paper_main_sample n d | Num.sqrt 3%:R < `|tnth x k|].
have mB0 : measurable [set y : RR | Num.sqrt 3%:R < `|y|].
  by rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr.
have mB k : measurable (B k).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_tnth k) measurableT _ mB0.
pose Nul := \big[setU/set0]_(k <- enum 'I_(n * d)) B k.
have mN : measurable Nul by apply: bigsetU_measurable => k _; exact: mB.
have PN : universality_sample_law (fun=> mu) n d Nul = 0%E.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  apply: le_trans (measure_bigsetU_le _ _ mB) _.
  rewrite big1 // => k _.
  transitivity (mu [set y | Num.sqrt 3%:R < `|y|]).
    exact: (@tuple_prod_tnth _ _ (fun=> mu) (n * d) k _ mB0).
  exact: paired_uniform_null.
have DS x : ~ Nul x -> D x = \sum_s W s * G s x.
  move=> nx; apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => k _.
  have xk : `|tnth x k| <= Num.sqrt 3%:R.
    rewrite leNgt; apply/negP => hk; apply: nx.
    by apply: (bigsetU_mem (mem_enum _ k)).
  by rewrite /paired_density /legendre_density xk.
(* measurability *)
have mtn k : measurable_fun setT (fun x : paper_main_sample n d =>
    paired_kernel (tnth x k) : RR).
  exact: measurableT_comp measurable_paired_kernel (measurable_tnth k).
have mD : measurable_fun setT (fun x => (D x)%:E).
  apply/measurable_EFinP; apply: measurable_sum => s.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_prod => k _; apply: measurable_funD; first exact: measurable_cst.
  by apply: measurable_funM; [exact: measurable_cst | exact: mtn].
have mG s : measurable_fun setT (fun x => (G s x)%:E).
  apply/measurable_EFinP; apply: measurable_prod => k _.
  exact: measurableT_comp (measurable_legendre_density _ _) (measurable_tnth k).
have mWG : measurable_fun setT (fun x => (\sum_s W s * G s x)%:E).
  apply/measurable_EFinP; apply: measurable_sum => s.
  apply: measurable_funM; first exact: measurable_cst.
  by apply/measurable_EFinP; exact: mG.
(* the integral *)
rewrite /paired_probability.
transitivity (\int[universality_sample_law (fun=> mu) n d]_(x in E)
    (D x)%:E)%E.
  by apply: eq_integral => x _; rewrite hD.
transitivity (\int[universality_sample_law (fun=> mu) n d]_(x in E)
    (\sum_s W s * G s x)%:E)%E.
  apply: ae_eq_integral => //.
  - exact: measurable_funS mD.
  - exact: measurable_funS mWG.
  - exists Nul; split => // x /= hx; apply: contrapT => nx; apply: hx => _.
    by rewrite DS.
under eq_integral do rewrite -sumEFin.
have mf s : measurable_fun E (fun x => (W s * G s x)%:E).
  apply: measurable_funTS; apply/measurable_EFinP.
  apply: measurable_funM; first exact: measurable_cst.
  by apply/measurable_EFinP; exact: mG.
have f0 s x : E x -> (0 <= (W s * G s x)%:E)%E.
  by move=> _; rewrite lee_fin mulr_ge0.
rewrite (ge0_integral_sum _ mE mf f0).
rewrite /mixture_probability; apply: eq_bigr => s _.
under eq_integral do rewrite EFinM.
have G0e x : E x -> (0 <= (G s x)%:E)%E by move=> _; rewrite lee_fin.
transitivity ((W s)%:E *
    \int[universality_sample_law (fun=> mu) n d]_(x in E) (G s x)%:E)%E.
  by apply: (ge0_integralZl_EFin _ mE G0e (measurable_funTS (mG s))); exact: W0.
congr (_ * _)%E.
rewrite /mixture_labelled_law /paired_mu /paired_law; symmetry.
exact: (tuple_prod_density (fun k _ => paired_prob_density mu hmu _ (ha s k)) mE).
Qed.

End paired_mixture.
