From Stdlib Require Import Reals Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
Import GRing.Theory Num.Theory.
Local Open Scope R_scope.

(* Copying the Lmodule structure of U * V onto euclidean_product U V makes HB
   declare canonical projections that duplicate those of U * V. Rocq ignores
   the duplicates and warns once per projection; the warning is silenced in
   this file only. *)
Local Set Warnings "-redundant-canonical-projection".

(* The product of two normed modules with the Euclidean product norm.

   MathComp-Analysis puts the max norm on U * V. Coquelicot's
   prod_NormedModule has the norm sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2),
   and MatrixDefinitions nests that product, so that a matrix carries the
   Frobenius norm and a vector the Euclidean norm. To keep that norm,
   euclidean_product U V is a type copy of U * V. It takes the Zmodule and
   Lmodule structures of the product, which are componentwise, and receives
   its norm through the factory Lmodule_isNormed. Its topology and uniform
   structure are then the ones that the norm defines.

   Coquelicot's ball on a product is the conjunction of the two component
   balls, with norm_factor sqrt 2 times the larger factor of the components.
   The ball of euclidean_product U V is the norm ball
   ball x e y <-> `|x - y| < e. The uniform structure therefore differs from
   Coquelicot's, while the neighbourhood filters, hence the topology, are the
   same: euclidean_product_nbhsE below states that they coincide with the
   neighbourhoods of MathComp's product topology on U * V.

   A pair (a, b) written without a type annotation has type U * V. Where
   inference finds a norm for it, that norm is MathComp's max norm. Norm
   statements about pairs must name the type, as in
   `|(a, b) : euclidean_product U V|. *)

Definition euclidean_product (U V : normedModType R) : Type := (U * V)%type.

HB.instance Definition _ (U V : normedModType R) :=
  GRing.Lmodule.on (euclidean_product U V).

(* The same formula as Coquelicot's prod_norm, with Stdlib's sqrt and pow. *)
Definition euclidean_product_norm {U V : normedModType R}
    (x : euclidean_product U V) : R :=
  sqrt (`|x.1|%R ^ 2 + `|x.2|%R ^ 2).

(* The triangle inequality for the Euclidean norm of R^2, applied to the
   norms of the components. *)
Lemma euclidean_product_minkowski (a1 a2 b1 b2 c1 c2 : R) :
  0 <= a1 -> 0 <= a2 -> 0 <= b1 -> 0 <= b2 -> 0 <= c1 -> 0 <= c2 ->
  c1 <= a1 + b1 -> c2 <= a2 + b2 ->
  sqrt (c1 ^ 2 + c2 ^ 2) <= sqrt (a1 ^ 2 + a2 ^ 2) + sqrt (b1 ^ 2 + b2 ^ 2).
Proof.
  intros Ha1 Ha2 Hb1 Hb2 Hc1 Hc2 H1 H2.
  set (s := sqrt (a1 ^ 2 + a2 ^ 2)); set (t := sqrt (b1 ^ 2 + b2 ^ 2)).
  assert (Hs : 0 <= s) by apply sqrt_pos.
  assert (Ht : 0 <= t) by apply sqrt_pos.
  assert (Hs2 : s ^ 2 = a1 ^ 2 + a2 ^ 2) by (apply pow2_sqrt; nra).
  assert (Ht2 : t ^ 2 = b1 ^ 2 + b2 ^ 2) by (apply pow2_sqrt; nra).
  assert (Hcs : (a1 * b1 + a2 * b2) ^ 2 <= (s * t) ^ 2).
  { rewrite Rpow_mult_distr Hs2 Ht2.
    assert (0 <= (a1 * b2 - a2 * b1) ^ 2) by apply pow2_ge_0. nra. }
  assert (Hst : a1 * b1 + a2 * b2 <= s * t).
  { apply Rsqr_incr_0_var.
    - unfold Rsqr; nra.
    - nra. }
  assert (Hst0 : 0 <= s + t) by lra.
  rewrite -(sqrt_pow2 (s + t) Hst0).
  apply sqrt_le_1_alt; nra.
Qed.

Lemma euclidean_product_normD (U V : normedModType R)
    (x y : euclidean_product U V) :
  (euclidean_product_norm (x + y) <=
    euclidean_product_norm x + euclidean_product_norm y)%R.
Proof.
  apply/RleP; unfold euclidean_product_norm.
  apply euclidean_product_minkowski; try (apply/RleP; apply normr_ge0).
  - apply/RleP; apply ler_normD.
  - apply/RleP; apply ler_normD.
Qed.

Lemma euclidean_product_normZ (U V : normedModType R) (l : R)
    (x : euclidean_product U V) :
  euclidean_product_norm (l *: x)%R = (`|l| * euclidean_product_norm x)%R.
Proof.
  unfold euclidean_product_norm; simpl.
  rewrite !normrZ.
  change (sqrt ((Rabs l * `|x.1|%R) ^ 2 + (Rabs l * `|x.2|%R) ^ 2) =
    Rabs l * sqrt (`|x.1|%R ^ 2 + `|x.2|%R ^ 2)).
  rewrite !Rpow_mult_distr -Rmult_plus_distr_l.
  rewrite (sqrt_mult_alt _ _ (pow2_ge_0 _)).
  rewrite (sqrt_pow2 _ (Rabs_pos l)); reflexivity.
Qed.

Lemma euclidean_product_norm_eq0 (U V : normedModType R)
    (x : euclidean_product U V) :
  euclidean_product_norm x = 0%R -> x = 0%R.
Proof.
  unfold euclidean_product_norm; destruct x as [x1 x2]; simpl; intros H.
  assert (H1 : 0 <= `|x1|%R) by (apply/RleP; apply normr_ge0).
  assert (H2 : 0 <= `|x2|%R) by (apply/RleP; apply normr_ge0).
  apply sqrt_eq_0 in H; [|nra].
  assert (E1 : `|x1|%R = 0) by nra.
  assert (E2 : `|x2|%R = 0) by nra.
  apply normr0_eq0 in E1; apply normr0_eq0 in E2.
  rewrite E1 E2; reflexivity.
Qed.

HB.instance Definition _ (U V : normedModType R) :=
  Lmodule_isNormed.Build R (euclidean_product U V)
    (@euclidean_product_normD U V) (@euclidean_product_normZ U V)
    (@euclidean_product_norm_eq0 U V).

(* From here on, euclidean_product U V : normedModType R. *)

Section EuclideanProductFacts.
Context {U V : normedModType R}.
Implicit Types x y : euclidean_product U V.

Lemma euclidean_product_normE x :
  `|x|%R = sqrt (`|x.1|%R ^ 2 + `|x.2|%R ^ 2).
Proof. reflexivity. Qed.

Lemma euclidean_product_ballE x (e : R) y :
  ball x e y <-> (`|x - y| < e)%R.
Proof. reflexivity. Qed.

Lemma euclidean_product_norm_fst x : (`|x.1| <= `|x|)%R.
Proof.
  apply/RleP; rewrite euclidean_product_normE.
  assert (H1 : 0 <= `|x.1|%R) by (apply/RleP; apply normr_ge0).
  rewrite -{1}(sqrt_pow2 _ H1).
  apply sqrt_le_1_alt.
  assert (0 <= `|x.2|%R ^ 2) by apply pow2_ge_0. lra.
Qed.

Lemma euclidean_product_norm_snd x : (`|x.2| <= `|x|)%R.
Proof.
  apply/RleP; rewrite euclidean_product_normE.
  assert (H2 : 0 <= `|x.2|%R) by (apply/RleP; apply normr_ge0).
  rewrite -{1}(sqrt_pow2 _ H2).
  apply sqrt_le_1_alt.
  assert (0 <= `|x.1|%R ^ 2) by apply pow2_ge_0. lra.
Qed.

Lemma euclidean_product_norm_le x : (`|x| <= `|x.1| + `|x.2|)%R.
Proof.
  apply/RleP; rewrite euclidean_product_normE.
  assert (H1 : 0 <= `|x.1|%R) by (apply/RleP; apply normr_ge0).
  assert (H2 : 0 <= `|x.2|%R) by (apply/RleP; apply normr_ge0).
  assert (H : 0 <= `|x.1|%R + `|x.2|%R) by lra.
  change (sqrt (`|x.1|%R ^ 2 + `|x.2|%R ^ 2) <= `|x.1|%R + `|x.2|%R).
  rewrite -{1}(sqrt_pow2 _ H).
  apply sqrt_le_1_alt; nra.
Qed.

(* A norm ball gives the two component balls of the same radius, and
   component balls of radii e1 and e2 give a norm ball of radius e1 + e2.
   These replace Coquelicot's definition of the product ball. *)
Lemma euclidean_product_ball_components {x} {e : R} {y} :
  ball x e y -> ball x.1 e y.1 /\ ball x.2 e y.2.
Proof.
  rewrite -!ball_normE /= => H; split.
  - exact: (Order.POrderTheory.le_lt_trans (euclidean_product_norm_fst _) H).
  - exact: (Order.POrderTheory.le_lt_trans (euclidean_product_norm_snd _) H).
Qed.

Lemma euclidean_product_ball_add {x} {e1 e2 : R} {y} :
  ball x.1 e1 y.1 -> ball x.2 e2 y.2 -> ball x (e1 + e2)%R y.
Proof.
  rewrite -!ball_normE /= => H1 H2.
  apply: (Order.POrderTheory.le_lt_trans (euclidean_product_norm_le _)).
  exact: ltrD.
Qed.

(* The norm topology of euclidean_product U V is the product topology. *)
Lemma euclidean_product_nbhsE x :
  @nbhs _ (euclidean_product U V) x = @nbhs _ (U * V)%type x.
Proof.
  apply/funext => P; apply/propext; rewrite !nbhs_ballP; split.
  - move=> [e e0 HP]; exists (e / 2)%R.
    + by rewrite /= divr_gt0.
    + move=> y [/= Hy1 Hy2]; apply: HP.
      move: Hy1 Hy2; rewrite -!ball_normE /= => Hy1 Hy2.
      rewrite (splitr e).
      apply: (Order.POrderTheory.le_lt_trans (euclidean_product_norm_le _)).
      exact: ltrD.
  - move=> [e e0 HP]; exists e => // y /= Hy; apply: HP.
    split; rewrite /= -ball_normE /=.
    + exact: (Order.POrderTheory.le_lt_trans (euclidean_product_norm_fst _) Hy).
    + exact: (Order.POrderTheory.le_lt_trans (euclidean_product_norm_snd _) Hy).
Qed.

Lemma euclidean_product_fst_continuous :
  continuous (fun x : euclidean_product U V => x.1).
Proof.
  move=> x; rewrite /continuous_at (euclidean_product_nbhsE x).
  exact: cvg_fst.
Qed.

Lemma euclidean_product_snd_continuous :
  continuous (fun x : euclidean_product U V => x.2).
Proof.
  move=> x; rewrite /continuous_at (euclidean_product_nbhsE x).
  exact: cvg_snd.
Qed.

Lemma euclidean_product_pair_continuous {T : topologicalType}
    (f : T -> U) (g : T -> V) (t : T) :
  {for t, continuous f} -> {for t, continuous g} ->
  {for t, continuous (fun s => ((f s, g s) : euclidean_product U V))}.
Proof.
  move=> Hf Hg.
  change ((fun s => ((f s, g s) : euclidean_product U V)) @ t -->
    ((f t, g t) : euclidean_product U V))%classic.
  rewrite (euclidean_product_nbhsE (f t, g t)).
  exact: cvg_pair.
Qed.

End EuclideanProductFacts.
