(* The exact law of a projected standard Gaussian array, part 1.
   An N-by-M array X is the row-major list of its entries (entry (i, j) at
   position i * M + j, as in PaperMainGordonEscape). For a loading
   U : nat -> nat -> R whose first s rows are orthonormal in R^N,
     gaussian_covariance_entry N U a a' = [a = a']   (a, a' < s),
   the projected array U X (s by M) is the covariance image of X under the
   loading P_U (k, l) = U (k / M, l / M) [k mod M = l mod M]
   (paper_main_projected_loading), and P_U has orthonormal rows in R^(N M)
   (paper_main_projected_loading_orthonormal). The map
   paper_main_projected_map : (N M)-tuples -> (s M)-tuples is measurable.
   This file also proves the measure-theoretic reduction used for the exact
   law: boxes whose sides are ]a, b] or the whole line form a pi-system that
   contains setT and generates the tuple sigma-algebra, so two probability
   laws agreeing on these boxes agree on every measurable set
   (paper_main_projected_box_unique), and the scalar logistic factors that
   approximate the indicator of ]a, b] everywhere. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability numfun.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianCovarianceDefinitions GaussianCovarianceLinear
  GaussianCoordinateDefinitions GaussianCoordinatePolynomialContinuity GaussianFiniteSums
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  GaussianProbabilityProductMeasure PaperMainGordonProcessCovariance
  PaperMainGaussianPermutationLaw GaussianCoordinateDerivativeDefinitions
  GaussianCoordinateWeightDefinitions GaussianCovarianceDomains PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainGaussianCovarianceMarginals
  PaperMainGaussianOrthogonal PaperMainGaussianSmoothLaw
  PaperMainLossSmoothFactor PaperMainLossSmoothProduct GaussianCoordinateTopology.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* The loading of the projected array. *)

Definition paper_main_projected_loading (M : nat) (U : nat -> nat -> R) (k l : nat) : R :=
  U (k / M)%nat (l / M)%nat * (if Nat.eqb (k mod M) (l mod M) then 1 else 0).

Definition paper_main_projected_orthonormal (s N : nat) (U : nat -> nat -> R) : Prop :=
  forall a a', (a < s)%coq_nat -> (a' < s)%coq_nat ->
    gaussian_covariance_entry N U a a' = if Nat.eqb a a' then 1 else 0.

Lemma paper_main_projected_row (N M : nat) (U : nat -> nat -> R) (a j : nat)
    (xs : list R) :
  (j < M)%coq_nat ->
  gaussian_covariance_row (N * M) (paper_main_projected_loading M U) (a * M + j) xs =
  finite_sum (fun i => U a i * List.nth (i * M + j) xs 0) (List.seq 0 N).
Proof.
move=> Hj.
rewrite /gaussian_covariance_row paper_main_gordon_sum_rectangle.
apply: finite_sum_ext => i _.
rewrite -(finite_sum_delta M j (U a i * List.nth (i * M + j) xs 0) Hj).
apply: finite_sum_ext => j' Hj'.
have Hj'M : (j' < M)%coq_nat by have := in_seq_lt _ _ Hj'; lia.
rewrite /paper_main_projected_loading.
rewrite !paper_main_gordon_row_major_div // !paper_main_gordon_row_major_mod //.
case: (Nat.eqb_spec j j') => [<-|Hne].
  by rewrite Nat.eqb_refl Rmult_1_r.
have -> : Nat.eqb j' j = false by apply/Nat.eqb_neq => H; apply: Hne.
ring.
Qed.

Lemma paper_main_projected_delta_dot (M j j' : nat) :
  (j < M)%coq_nat -> (j' < M)%coq_nat ->
  paper_main_gordon_dot M (fun t => if Nat.eqb j t then 1 else 0)
    (fun t => if Nat.eqb j' t then 1 else 0) = if Nat.eqb j j' then 1 else 0.
Proof.
move=> Hj Hj'; rewrite /paper_main_gordon_dot.
rewrite -(finite_sum_delta M j (if Nat.eqb j j' then 1 else 0) Hj).
apply: finite_sum_ext => t _.
case: (Nat.eqb_spec j t) => [<-|Hne].
  by rewrite Nat.eqb_refl Rmult_1_l Nat.eqb_sym.
have -> : Nat.eqb t j = false by apply/Nat.eqb_neq => H; apply: Hne.
by rewrite Rmult_0_l.
Qed.

(* The projected loading has orthonormal rows. *)

Theorem paper_main_projected_loading_orthonormal s N M (U : nat -> nat -> R) :
  paper_main_projected_orthonormal s N U ->
  forall k k', (k < s * M)%coq_nat -> (k' < s * M)%coq_nat ->
    gaussian_covariance_entry (N * M) (paper_main_projected_loading M U) k k' =
    if Nat.eqb k k' then 1 else 0.
Proof.
move=> HU k k' Hk Hk'.
have Hk2 : (k < Nat.mul s M)%coq_nat := Hk.
have Hk2' : (k' < Nat.mul s M)%coq_nat := Hk'.
have HM : (0 < M)%coq_nat by nia.
have Ha : (k / M < s)%coq_nat by apply: Nat.Div0.div_lt_upper_bound; lia.
have Ha' : (k' / M < s)%coq_nat by apply: Nat.Div0.div_lt_upper_bound; lia.
have Hj : (k mod M < M)%coq_nat by apply: Nat.mod_upper_bound; lia.
have Hj' : (k' mod M < M)%coq_nat by apply: Nat.mod_upper_bound; lia.
have T := paper_main_gordon_tensor_dot N M (U (k / M)%nat) (U (k' / M)%nat)
  (fun t => if Nat.eqb (k mod M) t then 1 else 0)
  (fun t => if Nat.eqb (k' mod M) t then 1 else 0).
transitivity (paper_main_gordon_dot N (U (k / M)%nat) (U (k' / M)%nat) *
  paper_main_gordon_dot M (fun t => if Nat.eqb (k mod M) t then 1 else 0)
    (fun t => if Nat.eqb (k' mod M) t then 1 else 0)).
  by rewrite -T.
rewrite paper_main_projected_delta_dot //.
have -> : paper_main_gordon_dot N (U (k / M)%nat) (U (k' / M)%nat) =
    gaussian_covariance_entry N U (k / M)%nat (k' / M)%nat by [].
rewrite HU //.
have Hk_eq := Nat.div_mod k M ltac:(lia).
have Hk'_eq := Nat.div_mod k' M ltac:(lia).
case: (Nat.eqb_spec (k / M) (k' / M)) => Hd;
  case: (Nat.eqb_spec (k mod M) (k' mod M)) => Hm;
  case: (Nat.eqb_spec k k') => Hkk; try ring; exfalso.
- by apply: Hkk; rewrite Hk_eq Hk'_eq Hd Hm.
- by apply: Hm; rewrite Hkk.
- by apply: Hd; rewrite Hkk.
- by apply: Hd; rewrite Hkk.
Qed.

(* The projected array as a map of tuples. *)

Definition paper_main_projected_image (s N M : nat) (U : nat -> nat -> R) (xs : list R) :
    list R :=
  gaussian_covariance_image (s * M) (N * M) (paper_main_projected_loading M U) xs.

Lemma paper_main_projected_image_size s N M U xs :
  size (paper_main_projected_image s N M U xs) == (s * M)%N.
Proof.
apply/eqP; rewrite /paper_main_projected_image /gaussian_covariance_image.
exact: length_map_seq.
Qed.

Definition paper_main_projected_map (s N M : nat) (U : nat -> nat -> R)
    (x : (N * M).-tuple T) : (s * M).-tuple T :=
  @Tuple (s * M) T (paper_main_projected_image s N M U (tval x))
    (paper_main_projected_image_size s N M U (tval x)).

Lemma paper_main_projected_map_val s N M U (x : (N * M).-tuple T) :
  tval (paper_main_projected_map s N M U x) = paper_main_projected_image s N M U (tval x).
Proof. by []. Qed.

Lemma paper_main_projected_row_continuous p (P : nat -> nat -> R) a :
  finite_joint_continuous p (gaussian_covariance_row p P a).
Proof.
rewrite /gaussian_covariance_row.
apply: (finite_joint_continuous_sum p (List.seq 0 p) (fun k xs => P a k * List.nth k xs 0)).
move=> k Hk; apply: finite_joint_continuous_scale.
by apply: finite_joint_continuous_nth; have := in_seq_lt _ _ Hk; lia.
Qed.

Lemma paper_main_projected_map_measurable s N M U :
  measurable_fun [set: (N * M).-tuple T] (paper_main_projected_map s N M U).
Proof.
apply/measurable_fun_tnthP => i.
have -> : (@tnth (s * M) T ^~ i \o paper_main_projected_map s N M U) =
    (fun x : (N * M).-tuple T =>
      gaussian_covariance_row (N * M) (paper_main_projected_loading M U) i (tval x)).
  apply: funext => x /=.
  rewrite (tnth_nth 0%R) /= /paper_main_projected_image /gaussian_covariance_image.
  rewrite -gpp_nthE.
  have Hi : (i < s * M)%coq_nat by apply/ssrnat.ltP; exact: ltn_ord.
  by rewrite (nth_map_seq _ (s * M) i Hi).
exact: (gpp_joint_measurable (N * M) _ (paper_main_projected_row_continuous _ _ _)).
Qed.

HB.instance Definition _ s N M U := isMeasurableFun.Build _ _ _ _
  (paper_main_projected_map s N M U) (paper_main_projected_map_measurable s N M U).

(* Boxes with sides ]a, b] or the whole line. *)

Definition paper_main_projected_interval (a b : R) : set T := [set z : T | a < z /\ z <= b].

Definition paper_main_projected_side (A : set T) : Prop :=
  A = setT \/ exists a b : R, A = paper_main_projected_interval a b.

Definition paper_main_projected_boxes (K : nat) : set (set (K.-tuple T)) :=
  [set B | exists A : 'I_K -> set T, (forall i, paper_main_projected_side (A i)) /\
    B = paper_main_permute_box A].

Lemma paper_main_projected_interval_itv (a b : R) :
  paper_main_projected_interval a b = `]a, b]%classic.
Proof.
apply/seteqP; split => z /=; rewrite /paper_main_projected_interval /= in_itv /=.
  by move=> [/RltP H1 /RleP H2]; rewrite H1 H2.
by move=> /andP [/RltP H1 /RleP H2]; split.
Qed.

Lemma paper_main_projected_interval_measurable (a b : R) :
  measurable (paper_main_projected_interval a b).
Proof. by rewrite paper_main_projected_interval_itv; exact: measurable_itv. Qed.

Lemma paper_main_projected_side_measurable (A : set T) :
  paper_main_projected_side A -> measurable A.
Proof.
case=> [->|[a [b ->]]]; first exact: measurableT.
exact: paper_main_projected_interval_measurable.
Qed.

Lemma paper_main_projected_boxes_measurable K :
  paper_main_projected_boxes K `<=` measurable.
Proof.
move=> _ [A [HA ->]]; apply: paper_main_permute_box_measurable => i.
exact: paper_main_projected_side_measurable.
Qed.

Lemma paper_main_projected_side_setI (A B : set T) :
  paper_main_projected_side A -> paper_main_projected_side B ->
  paper_main_projected_side (A `&` B).
Proof.
case=> [->|[a [b ->]]]; first by rewrite setTI.
case=> [->|[c [d ->]]]; first by rewrite setIT; right; exists a, b.
right; exists (Rmax a c), (Rmin b d).
apply/seteqP; split => z /=; rewrite /paper_main_projected_interval /=.
  move=> [[H1 H2] [H3 H4]]; split.
    by apply: Rmax_lub_lt.
  by apply: Rmin_glb.
move=> [H1 H2].
have := Rmax_l a c; have := Rmax_r a c; have := Rmin_l b d; have := Rmin_r b d.
move=> H5 H6 H7 H8; split; split; lra.
Qed.

Lemma paper_main_projected_boxes_setI K : setI_closed (paper_main_projected_boxes K).
Proof.
move=> _ _ [A [HA ->]] [B [HB ->]].
exists (fun i => A i `&` B i); split.
  by move=> i; apply: paper_main_projected_side_setI.
by apply/seteqP; split=> x; [move=> [H1 H2] i; split | move=> H; split=> i; case: (H i)].
Qed.

Lemma paper_main_projected_boxes_setT K : paper_main_projected_boxes K [set: K.-tuple T].
Proof.
exists (fun _ => setT); split; first by move=> i; left.
by apply/seteqP; split.
Qed.

(* These boxes generate the tuple sigma-algebra. *)

Lemma paper_main_projected_ocitv_preimage K (i : 'I_K) :
  (R.-ocitv.-measurable : set (set T)) `<=`
    image_set_system setT (@tnth K T ^~ i) <<s paper_main_projected_boxes K >>.
Proof.
move=> _ [[a b] _ <-].
rewrite /image_set_system /=.
apply: sub_sigma_algebra.
exists (fun j => if j == i then paper_main_projected_interval a b else setT); split.
  by move=> j; case: ifP => _; [right; exists a, b | left].
apply/seteqP; split => x /=.
  move=> [_ Hx] j; case: ifP => [/eqP ->|_] //.
  by rewrite paper_main_projected_interval_itv.
move=> H; split => //.
by have := H i; rewrite eqxx paper_main_projected_interval_itv.
Qed.

Lemma paper_main_projected_boxes_generate K (E : set (K.-tuple T)) :
  measurable E -> <<s paper_main_projected_boxes K >> E.
Proof.
move=> mE.
have Hsub : forall (i : 'I_K) (A : set T), measurable A ->
    <<s paper_main_projected_boxes K >> (setT `&` (@tnth K T ^~ i) @^-1` A).
  move=> i A mA.
  have HS : sigma_algebra setT (image_set_system setT (@tnth K T ^~ i)
      <<s paper_main_projected_boxes K >>).
    apply: sigma_algebra_image; exact: smallest_sigma_algebra.
  exact: (smallest_sub HS (paper_main_projected_ocitv_preimage K i) mA).
move: mE; rewrite /measurable /= /g_sigma_preimage.
apply: smallest_sub; first exact: smallest_sigma_algebra.
clear E.
case: K Hsub => [|K] Hsub; first by rewrite big_ord0.
rewrite -bigcup_mkord_ord => _ [i Ii [A mA <-]].
exact: (Hsub (inord i) A mA).
Qed.

(* Two probability laws on tuples that agree on the boxes agree on every
   measurable set. *)

Theorem paper_main_projected_box_unique K (mu : probability (K.-tuple T) R)
    (E : set (K.-tuple T)) :
  (forall B, paper_main_projected_boxes K B -> mu B = gaussian_product_law K B) ->
  measurable E -> mu E = gaussian_product_law K E.
Proof.
move=> Hagree mE.
have Hfin : forall k : nat, (mu [set: K.-tuple T] < +oo)%E.
  by move=> _; rewrite probability_setT ltry.
have H := @g_sigma_algebra_measure_unique _ _ _ (paper_main_projected_boxes K)
  (paper_main_projected_boxes_measurable K) (fun _ => setT)
  (fun _ => paper_main_projected_boxes_setT K) (bigcup_const _ _)
  mu (gaussian_product_law K) (paper_main_projected_boxes_setI K) Hagree
  Hfin E (paper_main_projected_boxes_generate K E mE).
exact: H.
Qed.

(* Dominated convergence to the probability of an event. *)

Lemma paper_main_projected_dominated_limit {dX : measure_display} {X : measurableType dX}
    (P : probability X R) (f_ : nat -> X -> R) (B : set X) :
  measurable B ->
  (forall n, measurable_fun [set: X] (f_ n : X -> T)) ->
  (forall n x, Rabs (f_ n x) <= 1) ->
  (forall x, (fun n => f_ n x) @ \oo --> ((\1_B x)%R : R)) ->
  (fun n => \int[P]_x (f_ n x)%:E)%E @ \oo --> P B.
Proof.
move=> mB mf Hb Hc.
have Hmf : forall n, measurable_fun [set: X] (fun x => (f_ n x)%:E).
  by move=> n; apply/measurable_EFinP; exact: mf.
have Hmi : measurable_fun [set: X] (fun x => ((\1_B x)%R : R)%:E).
  apply/measurable_EFinP; exact: measurable_indic.
have Hcv : \forall x \ae P, [set: X] x ->
    (fun n => (f_ n x)%:E) @ \oo --> (((\1_B x)%R : R)%:E).
  apply: aeW => x _.
  apply: cvg_EFin; first by apply: nearW => n.
  exact: Hc.
have Hg : P.-integrable [set: X] (fun _ => 1%:E).
  exact: finite_measure_integrable_cst.
have Hdom : \forall x \ae P, forall n, [set: X] x -> (`|(f_ n x)%:E| <= 1%:E)%E.
  apply: aeW => x n _; rewrite lee_fin -RabsE; apply/RleP; exact: Hb.
have [_ _ H] := dominated_convergence measurableT Hmf Hmi Hcv Hg Hdom.
rewrite (integral_indic P measurableT mB) setIT in H.
exact: H.
Qed.

(* The scalar factor approximating the indicator of ]a, b]. With
   S (c, p, y) = e / (1 + e), e = exp (c (y - p)), the factor is
   phi (c, p, q, y) = S (c, p, y) (1 - S (c, q, y)). *)

Definition paper_main_projected_S (c p y : R) : R :=
  exp (c * (y - p)) / (1 + exp (c * (y - p))).

Definition paper_main_projected_phi (c p q y : R) : R :=
  exp (c * (y - p)) / ((1 + exp (c * (y - p))) * (1 + exp (c * (y - q)))).

Definition paper_main_projected_phi1 (c p q y : R) : R :=
  c * paper_main_projected_phi c p q y *
  (1 - paper_main_projected_S c p y - paper_main_projected_S c q y).

Definition paper_main_projected_phi2 (c p q y : R) : R :=
  c ^ 2 * paper_main_projected_phi c p q y *
  ((1 - paper_main_projected_S c p y - paper_main_projected_S c q y) ^ 2 -
   paper_main_projected_S c p y * (1 - paper_main_projected_S c p y) -
   paper_main_projected_S c q y * (1 - paper_main_projected_S c q y)).

Lemma paper_main_projected_phi_S c p q y :
  paper_main_projected_phi c p q y =
  paper_main_projected_S c p y * (1 - paper_main_projected_S c q y).
Proof.
rewrite /paper_main_projected_phi /paper_main_projected_S.
have H1 := exp_pos (c * (y - p)); have H2 := exp_pos (c * (y - q)).
field; lra.
Qed.

Lemma paper_main_projected_S_bounds c p y :
  0 < paper_main_projected_S c p y < 1.
Proof.
rewrite /paper_main_projected_S.
have H := exp_pos (c * (y - p)).
split; first by apply: Rdiv_lt_0_compat; lra.
apply: (Rmult_lt_reg_r (1 + exp (c * (y - p)))); first lra.
rewrite /Rdiv Rmult_assoc Rinv_l; lra.
Qed.

Lemma paper_main_projected_phi_derive c p q y :
  @is_derive R R^o R^o y 1 (paper_main_projected_phi c p q)
    (paper_main_projected_phi1 c p q y).
Proof.
have H1 := exp_pos (c * (y - p)); have H2 := exp_pos (c * (y - q)).
rewrite /paper_main_projected_phi1 /paper_main_projected_phi /paper_main_projected_S.
auto_derive.
  by apply: Rmult_integral_contrapositive; split; lra.
field; split; lra.
Qed.

Lemma paper_main_projected_phi1_derive c p q y :
  @is_derive R R^o R^o y 1 (paper_main_projected_phi1 c p q)
    (paper_main_projected_phi2 c p q y).
Proof.
have H1 := exp_pos (c * (y - p)); have H2 := exp_pos (c * (y - q)).
rewrite /paper_main_projected_phi2 /paper_main_projected_phi1 /paper_main_projected_phi
  /paper_main_projected_S.
auto_derive.
- by apply: Rmult_integral_contrapositive; split; lra.
- lra.
- lra.
- field; split; lra.
Qed.

Lemma paper_main_projected_phi2_continuous c p q y :
  {for y, continuous (paper_main_projected_phi2 c p q)}.
Proof.
apply: ex_derive_continuous.
have H1 := exp_pos (c * (y - p)); have H2 := exp_pos (c * (y - q)).
rewrite /paper_main_projected_phi2 /paper_main_projected_phi /paper_main_projected_S.
auto_derive.
all: try (apply: Rmult_integral_contrapositive; split); lra.
Qed.

Lemma paper_main_projected_phi_bounds c p q y : 0 <= c ->
  0 <= paper_main_projected_phi c p q y <= 1 /\
  Rabs (paper_main_projected_phi c p q y) <= 2 * (1 + c) ^ 2 /\
  Rabs (paper_main_projected_phi1 c p q y) <= 2 * (1 + c) ^ 2 /\
  Rabs (paper_main_projected_phi2 c p q y) <= 2 * (1 + c) ^ 2.
Proof.
move=> Hc.
have [Hp0 Hp1] := paper_main_projected_S_bounds c p y.
have [Hq0 Hq1] := paper_main_projected_S_bounds c q y.
set Sp := paper_main_projected_S c p y in Hp0 Hp1 *.
set Sq := paper_main_projected_S c q y in Hq0 Hq1 *.
have Hphi0 : 0 <= Sp * (1 - Sq) by nra.
have Hphi1 : Sp * (1 - Sq) <= 1 by nra.
have HC1 : 1 <= 2 * (1 + c) ^ 2 by nra.
rewrite /paper_main_projected_phi1 /paper_main_projected_phi2 paper_main_projected_phi_S -/Sp -/Sq.
split; first by split.
split; first by rewrite Rabs_pos_eq //; lra.
split.
  rewrite Rabs_mult Rabs_mult (Rabs_pos_eq c Hc) (Rabs_pos_eq _ Hphi0).
  have Hw : Rabs (1 - Sp - Sq) <= 1 by apply: Rabs_le; lra.
  have Hw0 := Rabs_pos (1 - Sp - Sq).
  have H3 : c * (Sp * (1 - Sq)) <= c * 1 by apply: Rmult_le_compat_l.
  have H4 : 0 <= c * (Sp * (1 - Sq)) by apply: Rmult_le_pos.
  have H5 : c * (Sp * (1 - Sq)) * Rabs (1 - Sp - Sq) <= c * 1 * 1.
    by apply: Rmult_le_compat.
  nra.
have Hc2 : 0 <= c ^ 2 by nra.
rewrite Rabs_mult Rabs_mult (Rabs_pos_eq _ Hc2) (Rabs_pos_eq _ Hphi0).
have Hw : Rabs ((1 - Sp - Sq) ^ 2 - Sp * (1 - Sp) - Sq * (1 - Sq)) <= 2.
  apply: Rabs_le; split; nra.
have Hw0 := Rabs_pos ((1 - Sp - Sq) ^ 2 - Sp * (1 - Sp) - Sq * (1 - Sq)).
have H3 : c ^ 2 * (Sp * (1 - Sq)) <= c ^ 2 * 1 by apply: Rmult_le_compat_l.
have H4 : 0 <= c ^ 2 * (Sp * (1 - Sq)) by apply: Rmult_le_pos.
have H5 : c ^ 2 * (Sp * (1 - Sq)) *
    Rabs ((1 - Sp - Sq) ^ 2 - Sp * (1 - Sp) - Sq * (1 - Sq)) <= c ^ 2 * 1 * 2.
  by apply: Rmult_le_compat.
nra.
Qed.

(* Pointwise convergence to the indicator of ]a, b]. *)

Lemma paper_main_projected_un_cv_cvg (u : nat -> R) (l : R) :
  Un_cv u l -> u @ \oo --> l.
Proof.
move=> Hu; apply/(cvgrPdist_lt (V := R^o)) => e /RltP e0.
have [N HN] := Hu e e0.
apply: filterS (nbhs_infty_ge N) => n /ssrnat.leP Hn.
have H := HN n Hn; rewrite /R_dist Rabs_minus_sym in H.
apply/RltP; rewrite -RabsE; exact: H.
Qed.

Lemma paper_main_projected_exp_le (u v : R) : u <= v -> exp u <= exp v.
Proof.
move=> Huv; case: (Rle_lt_or_eq_dec _ _ Huv) => H; last by rewrite H; lra.
by apply: Rlt_le; apply: exp_increasing.
Qed.

Lemma paper_main_projected_cvg_bound (u : nat -> R) (l : R) (N0 : nat) :
  (forall n, (N0 <= n)%coq_nat -> Rabs (u n - l) <= 2 * exp (- (INR n + 1))) ->
  u @ \oo --> l.
Proof.
move=> Hb; apply: paper_main_projected_un_cv_cvg => eps Heps.
have [N1 HN1] := INR_unbounded (2 / eps).
exists (Nat.max N0 N1) => n Hn.
rewrite /R_dist.
have Hn0 : (N0 <= n)%coq_nat by lia.
have Hn1 : INR N1 <= INR n by apply: le_INR; lia.
have Hpos := pos_INR n.
have He : 1 + (INR n + 1) < exp (INR n + 1) by apply: exp_ineq1; lra.
have Hinv : exp (- (INR n + 1)) * exp (INR n + 1) = 1.
  by rewrite -exp_plus Rplus_opp_l exp_0.
have Hexp0 := exp_pos (- (INR n + 1)).
have H2 : 2 * exp (- (INR n + 1)) < eps.
  have Hk : 2 / eps < INR n + 2 by lra.
  have Hk' : 2 < eps * (INR n + 2).
    have := Rmult_lt_compat_l eps _ _ Heps Hk.
    by rewrite /Rdiv -Rmult_assoc (Rmult_comm eps 2) Rmult_assoc Rinv_r; lra.
  nra.
have := Hb n Hn0; lra.
Qed.

Definition paper_main_projected_rate (n : nat) : R := (INR n + 1) ^ 2.

Definition paper_main_projected_factor (n : nat) (a b y : R) : R :=
  paper_main_projected_phi (paper_main_projected_rate n)
    (a + / (INR n + 1)) (b + / (INR n + 1)) y.

Lemma paper_main_projected_S_le c p y :
  paper_main_projected_S c p y <= exp (c * (y - p)).
Proof.
rewrite /paper_main_projected_S.
have H := exp_pos (c * (y - p)).
apply: (Rmult_le_reg_r (1 + exp (c * (y - p)))); first lra.
rewrite /Rdiv Rmult_assoc Rinv_l; nra.
Qed.

Lemma paper_main_projected_S_ge c p y :
  1 - paper_main_projected_S c p y <= exp (- (c * (y - p))).
Proof.
rewrite /paper_main_projected_S.
have H := exp_pos (c * (y - p)).
have Hi : exp (- (c * (y - p))) * exp (c * (y - p)) = 1.
  by rewrite -exp_plus Rplus_opp_l exp_0.
have Hi0 := exp_pos (- (c * (y - p))).
have -> : 1 - exp (c * (y - p)) / (1 + exp (c * (y - p))) =
  1 / (1 + exp (c * (y - p))) by field; lra.
apply: (Rmult_le_reg_r (1 + exp (c * (y - p)))); first lra.
rewrite /Rdiv Rmult_assoc Rinv_l; nra.
Qed.

Lemma paper_main_projected_exponent n a y :
  paper_main_projected_rate n * (y - (a + / (INR n + 1))) =
  (INR n + 1) * ((INR n + 1) * (y - a) - 1).
Proof.
rewrite /paper_main_projected_rate.
have := pos_INR n => H.
field; lra.
Qed.

Lemma paper_main_projected_factor_cvg (a b y : R) :
  (fun n => paper_main_projected_factor n a b y) @ \oo -->
    ((\1_(paper_main_projected_interval a b) y)%R : R).
Proof.
rewrite /numfun.indic.
have HE : forall n : nat, 0 < exp (- (INR n + 1)) by move=> n; exact: exp_pos.
have Hgen : forall n p, paper_main_projected_rate n * (y - p) <= - (INR n + 1) ->
    paper_main_projected_S (paper_main_projected_rate n) p y <= exp (- (INR n + 1)).
  move=> n p Hp; apply: Rle_trans (paper_main_projected_S_le _ _ _) _.
  exact: paper_main_projected_exp_le.
have Hgen' : forall n p, INR n + 1 <= paper_main_projected_rate n * (y - p) ->
    1 - paper_main_projected_S (paper_main_projected_rate n) p y <= exp (- (INR n + 1)).
  move=> n p Hp; apply: Rle_trans (paper_main_projected_S_ge _ _ _) _.
  apply: paper_main_projected_exp_le; lra.
case: (boolP (y \in paper_main_projected_interval a b)) => Hin.
  move: (Hin); rewrite inE => -[Hya Hyb].
  have -> : ((true%:R)%R : R) = 1 by [].
  have [N0 HN0] := INR_unbounded (2 / (y - a)).
  apply: (paper_main_projected_cvg_bound _ _ N0) => n Hn.
  have HnN : INR N0 <= INR n by apply: le_INR.
  have Hpos := pos_INR n.
  have H2 : 2 <= (INR n + 1) * (y - a).
    have : 2 / (y - a) < INR n + 1 by lra.
    move=> H; have := Rmult_lt_compat_r (y - a) _ _ ltac:(lra) H.
    rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  have Hp := Hgen' n (a + / (INR n + 1)).
  rewrite paper_main_projected_exponent in Hp.
  have Hp' := Hp ltac:(nra).
  have Hq := Hgen n (b + / (INR n + 1)).
  rewrite paper_main_projected_exponent in Hq.
  have Hq' := Hq ltac:(nra).
  rewrite /paper_main_projected_factor paper_main_projected_phi_S.
  have [Hp0 Hp1] :=
    paper_main_projected_S_bounds (paper_main_projected_rate n) (a + / (INR n + 1)) y.
  have [Hq0 Hq1] :=
    paper_main_projected_S_bounds (paper_main_projected_rate n) (b + / (INR n + 1)) y.
  move: Hp' Hq' Hp0 Hp1 Hq0 Hq1.
  set Sp := paper_main_projected_S _ (a + / (INR n + 1)) y.
  set Sq := paper_main_projected_S _ (b + / (INR n + 1)) y.
  move=> Hp' Hq' Hp0 Hp1 Hq0 Hq1.
  rewrite Rabs_left1; last by nra.
  nra.
have -> : ((false%:R)%R : R) = 0 by [].
have Hout : y <= a \/ b < y.
  case: (Rle_lt_dec y a) => H; first by left.
  case: (Rle_lt_dec y b) => H'; last by right.
  exfalso; move/negP: Hin; apply; rewrite inE; split => //.
case: Hout => Hy.
  apply: (paper_main_projected_cvg_bound _ _ 0) => n _.
  have Hpos := pos_INR n.
  have Hp := Hgen n (a + / (INR n + 1)).
  rewrite paper_main_projected_exponent in Hp.
  have Hp' := Hp ltac:(nra).
  rewrite /paper_main_projected_factor paper_main_projected_phi_S.
  have [Hp0 Hp1] :=
    paper_main_projected_S_bounds (paper_main_projected_rate n) (a + / (INR n + 1)) y.
  have [Hq0 Hq1] :=
    paper_main_projected_S_bounds (paper_main_projected_rate n) (b + / (INR n + 1)) y.
  move: Hp' Hp0 Hp1 Hq0 Hq1.
  set Sp := paper_main_projected_S _ (a + / (INR n + 1)) y.
  set Sq := paper_main_projected_S _ (b + / (INR n + 1)) y.
  move=> Hp' Hp0 Hp1 Hq0 Hq1.
  have HE0 := HE n.
  rewrite Rminus_0_r Rabs_pos_eq; nra.
have [N0 HN0] := INR_unbounded (2 / (y - b)).
apply: (paper_main_projected_cvg_bound _ _ N0) => n Hn.
have HnN : INR N0 <= INR n by apply: le_INR.
have Hpos := pos_INR n.
have H2 : 2 <= (INR n + 1) * (y - b).
  have : 2 / (y - b) < INR n + 1 by lra.
  move=> H; have := Rmult_lt_compat_r (y - b) _ _ ltac:(lra) H.
  rewrite /Rdiv Rmult_assoc Rinv_l; lra.
have Hq := Hgen' n (b + / (INR n + 1)).
rewrite paper_main_projected_exponent in Hq.
have Hq' := Hq ltac:(nra).
rewrite /paper_main_projected_factor paper_main_projected_phi_S.
have [Hp0 Hp1] :=
  paper_main_projected_S_bounds (paper_main_projected_rate n) (a + / (INR n + 1)) y.
have [Hq0 Hq1] :=
  paper_main_projected_S_bounds (paper_main_projected_rate n) (b + / (INR n + 1)) y.
move: Hq' Hp0 Hp1 Hq0 Hq1.
set Sp := paper_main_projected_S _ (a + / (INR n + 1)) y.
set Sq := paper_main_projected_S _ (b + / (INR n + 1)) y.
move=> Hq' Hp0 Hp1 Hq0 Hq1.
have HE0 := HE n.
rewrite Rminus_0_r Rabs_pos_eq; nra.
Qed.

(* The side factors and the box tests. A box is described by data
   sd : nat -> option (R * R): side k is the whole line for None and
   ]a, b] for Some (a, b). *)

Definition paper_main_projected_side_set (o : option (R * R)) : set T :=
  match o with None => setT | Some (a, b) => paper_main_projected_interval a b end.

Definition paper_main_projected_side_factor (n : nat) (o : option (R * R)) (y : R) : R :=
  match o with None => 1 | Some (a, b) => paper_main_projected_factor n a b y end.

Definition paper_main_projected_side_factor1 (n : nat) (o : option (R * R)) (y : R) : R :=
  match o with
  | None => 0
  | Some (a, b) => paper_main_projected_phi1 (paper_main_projected_rate n)
      (a + / (INR n + 1)) (b + / (INR n + 1)) y
  end.

Definition paper_main_projected_side_factor2 (n : nat) (o : option (R * R)) (y : R) : R :=
  match o with
  | None => 0
  | Some (a, b) => paper_main_projected_phi2 (paper_main_projected_rate n)
      (a + / (INR n + 1)) (b + / (INR n + 1)) y
  end.

Definition paper_main_projected_side_constant (n : nat) : R :=
  2 * (1 + paper_main_projected_rate n) ^ 2.

Lemma paper_main_projected_rate_ge0 n : 0 <= paper_main_projected_rate n.
Proof. by rewrite /paper_main_projected_rate; apply: pow2_ge_0. Qed.

Lemma paper_main_projected_side_smooth d k n o : (k < d)%coq_nat ->
  paper_main_gaussian_smooth_test d
    (paper_main_loss_coordinate (paper_main_projected_side_factor n o) k)
    (paper_main_loss_coordinate1 (paper_main_projected_side_factor1 n o) k)
    (paper_main_loss_coordinate2 (paper_main_projected_side_factor2 n o) k)
    (paper_main_projected_side_constant n) 0.
Proof.
move=> Hk.
have Hc := paper_main_projected_rate_ge0 n.
have HC1 : 1 <= paper_main_projected_side_constant n.
  rewrite /paper_main_projected_side_constant; nra.
apply: paper_main_loss_coordinate_smooth => //; first lra.
- case: o => [[a b]|] t /=; first exact: paper_main_projected_phi_derive.
  exact: is_derive_const.
- case: o => [[a b]|] t /=; first exact: paper_main_projected_phi1_derive.
  exact: is_derive_const.
- case: o => [[a b]|] t /=; first exact: paper_main_projected_phi2_continuous.
  exact: cst_continuous.
- case: o => [[a b]|] t /=.
    have [_ [H1 [H2 H3]]] := paper_main_projected_phi_bounds (paper_main_projected_rate n)
      (a + / (INR n + 1)) (b + / (INR n + 1)) t Hc.
    by rewrite /paper_main_projected_factor.
  rewrite Rabs_R1 Rabs_R0; split; [lra | split; lra].
Qed.

Fixpoint paper_main_projected_box_test (n : nat) (sd : nat -> option (R * R)) (m : nat) :
    list R -> R :=
  match m with
  | 0 => fun _ => 1
  | m'.+1 => fun xs => paper_main_projected_box_test n sd m' xs *
      paper_main_loss_coordinate (paper_main_projected_side_factor n (sd m')) m' xs
  end.

Fixpoint paper_main_projected_box_test1 (n : nat) (sd : nat -> option (R * R)) (m : nat) :
    nat -> list R -> R :=
  match m with
  | 0 => fun _ _ => 0
  | m'.+1 => paper_main_loss_product_first (paper_main_projected_box_test n sd m')
      (paper_main_loss_coordinate (paper_main_projected_side_factor n (sd m')) m')
      (paper_main_projected_box_test1 n sd m')
      (paper_main_loss_coordinate1 (paper_main_projected_side_factor1 n (sd m')) m')
  end.

Fixpoint paper_main_projected_box_test2 (n : nat) (sd : nat -> option (R * R)) (m : nat) :
    nat -> nat -> list R -> R :=
  match m with
  | 0 => fun _ _ _ => 0
  | m'.+1 => paper_main_loss_product_second (paper_main_projected_box_test n sd m')
      (paper_main_loss_coordinate (paper_main_projected_side_factor n (sd m')) m')
      (paper_main_projected_box_test1 n sd m')
      (paper_main_loss_coordinate1 (paper_main_projected_side_factor1 n (sd m')) m')
      (paper_main_projected_box_test2 n sd m')
      (paper_main_loss_coordinate2 (paper_main_projected_side_factor2 n (sd m')) m')
  end.

Fixpoint paper_main_projected_box_constant (n m : nat) : R :=
  match m with
  | 0 => 1
  | m'.+1 => 4 * paper_main_projected_box_constant n m' * paper_main_projected_side_constant n
  end.

Lemma paper_main_projected_constant_smooth d :
  paper_main_gaussian_smooth_test d (fun _ => 1) (fun _ _ => 0) (fun _ _ _ => 0) 1 0.
Proof.
constructor.
- exact: finite_joint_continuous_constant.
- by move=> a _; exact: paper_main_coordinate_derivative_const.
- by move=> a _; exact: finite_joint_continuous_constant.
- by move=> a b _ _; exact: paper_main_coordinate_derivative_const.
- by move=> a b _ _; exact: finite_joint_continuous_constant.
- by apply/paper_main_polynomial_zero_bound; split; [lra | move=> xs _; rewrite Rabs_R1; lra].
- move=> a _; apply/paper_main_polynomial_zero_bound; split; first lra.
  by move=> xs _; rewrite Rabs_R0; lra.
- move=> a b _ _; apply/paper_main_polynomial_zero_bound; split; first lra.
  by move=> xs _; rewrite Rabs_R0; lra.
Qed.

Lemma paper_main_projected_box_smooth d n sd m : (m <= d)%coq_nat ->
  paper_main_gaussian_smooth_test d (paper_main_projected_box_test n sd m)
    (paper_main_projected_box_test1 n sd m) (paper_main_projected_box_test2 n sd m)
    (paper_main_projected_box_constant n m) 0.
Proof.
elim: m => [|m IH] Hm /=; first exact: paper_main_projected_constant_smooth.
apply: (paper_main_loss_smooth_multiply d _ _ _ _ _ _ _ _ (IH ltac:(lia))).
apply: paper_main_projected_side_smooth; lia.
Qed.

(* Limits and bounds of the box tests. *)

Fixpoint paper_main_projected_box_indicator (sd : nat -> option (R * R)) (m : nat)
    (xs : list R) : R :=
  match m with
  | 0 => 1
  | m'.+1 => paper_main_projected_box_indicator sd m' xs *
      ((\1_(paper_main_projected_side_set (sd m')) (List.nth m' xs 0))%R : R)
  end.

Lemma paper_main_projected_box_test_cvg sd m xs :
  (fun n => paper_main_projected_box_test n sd m xs) @ \oo -->
    paper_main_projected_box_indicator sd m xs.
Proof.
elim: m => [|m IH] /=; first exact: cvg_cst.
have Hc : (fun n => paper_main_loss_coordinate (paper_main_projected_side_factor n (sd m)) m xs)
    @ \oo --> ((\1_(paper_main_projected_side_set (sd m)) (List.nth m xs 0))%R : R).
  rewrite /paper_main_loss_coordinate.
  case: (sd m) => [[a b]|] /=; first exact: paper_main_projected_factor_cvg.
  rewrite /numfun.indic in_setT /=.
  exact: cvg_cst.
exact: (cvgM IH Hc).
Qed.

Lemma paper_main_projected_side_factor_bounds n o y :
  0 <= paper_main_projected_side_factor n o y <= 1.
Proof.
case: o => [[a b]|] /=; last lra.
have [H _] := paper_main_projected_phi_bounds (paper_main_projected_rate n)
  (a + / (INR n + 1)) (b + / (INR n + 1)) y (paper_main_projected_rate_ge0 n).
exact: H.
Qed.

Lemma paper_main_projected_box_test_bounds n sd m xs :
  0 <= paper_main_projected_box_test n sd m xs <= 1.
Proof.
elim: m => [|m IH] /=; first lra.
have := paper_main_projected_side_factor_bounds n (sd m) (List.nth m xs 0).
rewrite /paper_main_loss_coordinate; nra.
Qed.

Lemma paper_main_projected_box_indicator_cond sd m xs :
  paper_main_projected_box_indicator sd m xs =
  if pselect (forall k, (k < m)%N -> paper_main_projected_side_set (sd k) (List.nth k xs 0))
  then 1 else 0.
Proof.
elim: m => [|m IH] /=.
  by case: pselect => // H; exfalso; apply: H => k.
rewrite IH /numfun.indic.
case: pselect => H1; case: pselect => H2 /=.
- have Hm : paper_main_projected_side_set (sd m) (List.nth m xs 0) by apply: H2.
  have -> : (List.nth m xs 0 \in paper_main_projected_side_set (sd m)) = true.
    by apply/mem_set.
  by rewrite Rmult_1_l.
- case: (boolP (_ \in _)) => H3 /=; last by rewrite Rmult_0_r.
  exfalso; apply: H2 => k Hk.
  case: (ltnP k m) => Hkm; first exact: H1.
  have -> : k = m by apply/eqP; rewrite eqn_leq Hkm -ltnS Hk.
  by move: H3; rewrite inE.
- exfalso; apply: H1 => k Hk; apply: H2; exact: ltnW.
- by rewrite Rmult_0_l.
Qed.

Definition paper_main_projected_data_box (K : nat) (sd : nat -> option (R * R)) :
    set (K.-tuple T) :=
  paper_main_permute_box (fun i : 'I_K => paper_main_projected_side_set (sd i)).

Lemma paper_main_projected_box_indicator_box K sd (y : K.-tuple T) :
  paper_main_projected_box_indicator sd K (tval y) =
  ((\1_(paper_main_projected_data_box K sd) y)%R : R).
Proof.
rewrite paper_main_projected_box_indicator_cond /numfun.indic.
case: pselect => H; case: (boolP (y \in _)) => Hy //=; exfalso.
- move/negP: Hy; apply; apply/mem_set => i.
  rewrite (tnth_nth 0%R) -gpp_nthE; exact: H.
- move: Hy; rewrite inE => Hy; apply: H => k Hk.
  have := Hy (Ordinal Hk); rewrite (tnth_nth 0%R) -gpp_nthE.
  by [].
Qed.

Lemma paper_main_projected_data_box_measurable K sd :
  measurable (paper_main_projected_data_box K sd).
Proof.
apply: paper_main_permute_box_measurable => i.
case: (sd i) => [[a b]|] /=; last exact: measurableT.
exact: paper_main_projected_interval_measurable.
Qed.

(* The exact law on a box. *)

Theorem paper_main_projected_data_box_law s N M (U : nat -> nat -> R)
    (sd : nat -> option (R * R)) :
  paper_main_projected_orthonormal s N U ->
  gaussian_product_law (N * M)
    (paper_main_projected_map s N M U @^-1` paper_main_projected_data_box (s * M) sd) =
  gaussian_product_law (s * M) (paper_main_projected_data_box (s * M) sd).
Proof.
move=> HU.
set K := (s * M)%N.
set B := paper_main_projected_data_box K sd.
set P := paper_main_projected_loading M U.
set Phi := paper_main_projected_map s N M U.
have mB : measurable B by exact: paper_main_projected_data_box_measurable.
have mPhi : measurable_fun [set: (N * M).-tuple T] Phi.
  exact: paper_main_projected_map_measurable.
have mPB : measurable (Phi @^-1` B).
  by have := mPhi measurableT _ mB; rewrite setTI.
have HS : forall n, paper_main_gaussian_smooth_test K (paper_main_projected_box_test n sd K)
    (paper_main_projected_box_test1 n sd K) (paper_main_projected_box_test2 n sd K)
    (paper_main_projected_box_constant n K) 0.
  by move=> n; apply: paper_main_projected_box_smooth.
have Hcov : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_entry (N * M) P a b = paper_main_gaussian_identity b a.
  move=> a b Ha Hb.
  by rewrite /P (paper_main_projected_loading_orthonormal s N M U HU a b Ha Hb).
have [M0 [HM0 HP0]] := finite_matrix_bound P K (N * M).
(* Smooth-test invariance and transport: the integrals agree for every n. *)
have Heq : forall n,
    (\int[gaussian_product_law (N * M)]_x
      (paper_main_projected_box_test n sd K (tval (Phi x)))%:E)%E =
    (\int[gaussian_product_law K]_y (paper_main_projected_box_test n sd K (tval y))%:E)%E.
  move=> n.
  have [Hc HD HDc HD2 HD2c Hb HDb HD2b] := HS n.
  have Hinv := paper_main_gaussian_standard_covariance_expectation K
    (paper_main_projected_box_test n sd K) (paper_main_projected_box_test1 n sd K)
    (paper_main_projected_box_test2 n sd K) (paper_main_projected_box_constant n K) 0
    Hc HD HDc HD2 HD2c Hb HDb HD2b (N * M) P Hcov.
  have [_ HT1] := paper_main_gaussian_law_transport K _ _ _ Hc Hb.
  have [Hc' Hb'] := gaussian_covariance_image_regular K (N * M) P M0 _ _ 0 HM0 HP0 Hc Hb.
  have [_ HT2] := paper_main_gaussian_law_transport (N * M) _ _ _ Hc' Hb'.
  rewrite HT1 -Hinv -HT2.
  by [].
(* Dominated convergence on both sides. *)
have mF : forall n, measurable_fun [set: K.-tuple T]
    ((fun y => paper_main_projected_box_test n sd K (tval y)) : _ -> T).
  by move=> n; exact: (gpp_joint_measurable K _ (pmgs_continuous _ _ _ _ _ _ (HS n))).
have Hbd : forall n (xs : list R), Rabs (paper_main_projected_box_test n sd K xs) <= 1.
  move=> n xs; have [H0 H1] := paper_main_projected_box_test_bounds n sd K xs.
  by rewrite Rabs_pos_eq.
have Hlim1 := paper_main_projected_dominated_limit (gaussian_product_law K)
  (fun n y => paper_main_projected_box_test n sd K (tval y)) B mB mF
  (fun n y => Hbd n (tval y))
  (fun y => eq_ind _ (fun l => _ @ \oo --> l) (paper_main_projected_box_test_cvg sd K (tval y))
     _ (paper_main_projected_box_indicator_box K sd y)).
have mF2 : forall n, measurable_fun [set: (N * M).-tuple T]
    ((fun x => paper_main_projected_box_test n sd K (tval (Phi x))) : _ -> T).
  by move=> n; exact: (measurableT_comp (mF n) mPhi).
have Hcv2 : forall x, (fun n => paper_main_projected_box_test n sd K (tval (Phi x))) @ \oo -->
    ((\1_(Phi @^-1` B) x)%R : R).
  move=> x.
  have -> : ((\1_(Phi @^-1` B) x)%R : R) = ((\1_B (Phi x))%R : R).
    rewrite /numfun.indic; case: (boolP (x \in _)) => H1; case: (boolP (Phi x \in _)) => H2 //;
      exfalso.
      by move/negP: H2; apply; apply/mem_set; exact: (set_mem H1).
    by move/negP: H1; apply; apply/mem_set; exact: (set_mem H2).
  rewrite -paper_main_projected_box_indicator_box.
  exact: paper_main_projected_box_test_cvg.
have Hlim2 := paper_main_projected_dominated_limit (gaussian_product_law (N * M))
  (fun n x => paper_main_projected_box_test n sd K (tval (Phi x))) (Phi @^-1` B) mPB mF2
  (fun n x => Hbd n (tval (Phi x))) Hcv2.
have Hlim2' : (fun n => (\int[gaussian_product_law K]_y
    (paper_main_projected_box_test n sd K (tval y))%:E)%E) @ \oo -->
    gaussian_product_law (N * M) (Phi @^-1` B).
  have -> : (fun n => (\int[gaussian_product_law K]_y
      (paper_main_projected_box_test n sd K (tval y))%:E)%E) =
    (fun n => (\int[gaussian_product_law (N * M)]_x
      (paper_main_projected_box_test n sd K (tval (Phi x)))%:E)%E).
    by apply: funext => n; rewrite Heq.
  exact: Hlim2.
exact: (cvg_unique _ Hlim2' Hlim1).
Qed.

(* The exact law of the projected array: for every measurable event E of
   s-by-M arrays, P_(N M)(U X in E) = P_(s M)(E). *)

Theorem paper_main_projected_law s N M (U : nat -> nat -> R)
    (E : set ((s * M).-tuple T)) :
  paper_main_projected_orthonormal s N U -> measurable E ->
  gaussian_product_law (N * M) (paper_main_projected_map s N M U @^-1` E) =
  gaussian_product_law (s * M) E.
Proof.
move=> HU mE.
pose mu := distribution (gaussian_product_law (N * M)) (paper_main_projected_map s N M U).
have Hagree : forall B, paper_main_projected_boxes (s * M) B ->
    mu B = gaussian_product_law (s * M) B.
  move=> _ [A [HA ->]].
  have Hch : forall k : nat, exists o : option (R * R),
      forall Hk : (k < s * M)%N, A (Ordinal Hk) = paper_main_projected_side_set o.
    move=> k.
    case: (Nat.lt_ge_cases k (s * M)) => Hk; last first.
      by exists None => Hk'; exfalso; move/ssrnat.ltP: Hk'; lia.
    have Hk2 : (k < s * M)%N by apply/ssrnat.ltP.
    case: (HA (Ordinal Hk2)) => [HT|[a [b Hab]]].
      exists None => Hk' /=.
      by have -> : Ordinal Hk' = Ordinal Hk2 by apply: val_inj.
    exists (Some (a, b)) => Hk' /=.
    by have -> : Ordinal Hk' = Ordinal Hk2 by apply: val_inj.
  have [sd Hsd] := choice Hch.
  have -> : paper_main_permute_box A = paper_main_projected_data_box (s * M) sd.
    rewrite /paper_main_projected_data_box; congr paper_main_permute_box.
    apply: funext => i; rewrite -(Hsd i (ltn_ord i)).
    by congr A; apply: val_inj.
  rewrite /mu /distribution /pushforward.
  exact: paper_main_projected_data_box_law.
have H := paper_main_projected_box_unique (s * M) mu E Hagree mE.
by rewrite -H.
Qed.
