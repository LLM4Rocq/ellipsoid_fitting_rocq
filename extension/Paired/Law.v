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
      library/probability/mixture.v. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From GaussianAnalysis.probability Require Import mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

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
