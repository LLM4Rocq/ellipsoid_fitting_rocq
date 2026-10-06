(* Measurability of paper_main_balanced_pd_event, the first conjunct of the
   third clause of paper_main_results.

   The event {x | exists y with sum y = 0 and sum_i y_i x_i x_i^T positive
   definite} is the union over rational weights r with sum 0 and over k of
   the sets {x | for every rational vector w, |w|^2 / (k + 1) <= w^T M(r, x)
   w}, each a countable intersection of measurable sets. Positive
   definiteness of a symmetric matrix is equivalent to such a uniform bound
   for some k (pm_pd_uniform, by a cluster point of normalised vectors in
   the unit box), the bound transfers from rational to real vectors by
   continuity (pm_qf_rat_transfer), rational weights with sum zero
   approximate real ones (pm_rat_zero_sum_approx, by subtracting the mean),
   and the perturbation of M(y, x) by the weights is controlled entrywise. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean interval matrix rat.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Coordinates
  Measurability.Box Measurability.Compact Measurability.Countable
  Measurability.Fit Measurability.Conditioned.

Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* A sequence of row vectors converging entrywise to p has the cluster
   property at p used by Measurability.Compact. *)
Lemma pm_cluster_of_cvg (N : nat) (u : nat -> 'rV[R]_N) (p : 'rV[R]_N) :
  (forall k j, `|p ord0 j - u k ord0 j| < k.+1%:R^-1) ->
  forall B : set 'rV[R]_N, nbhs p B -> forall k0 : nat, exists k, (k0 <= k)%nat /\ B (u k).
Proof.
move=> H B /nbhs_ballP[e e0 eB] k0.
have e0' : 0 < e := e0.
have [k1 k1e] := pm_inv_small e e0'.
exists (maxn k0 k1); split; first exact: leq_maxl.
apply: eB; split => // i j; rewrite (ord1 i) /ball/=.
apply: lt_trans (H _ j) _; apply: le_lt_trans _ k1e; exact: pm_inv_mono _ _ (leq_maxr k0 k1).
Qed.

(* Rational weights with sum zero within eps of real weights with sum zero:
   approximate each weight, then subtract the mean. *)
Lemma pm_rat_zero_sum_approx (n : nat) (y : 'I_n -> R) (eps : R) :
  0 < eps -> \sum_(i < n) y i = 0 ->
  exists r : {ffun 'I_n -> rat},
    \sum_(i < n) ratr (r i) = 0 :> R /\ forall i, `|y i - ratr (r i)| < eps.
Proof.
case: n y => [|n] y eps0 y0.
  exists [ffun _ => 0]; split; first by rewrite big_ord0.
  by move=> [m lt0]; have := lt0; rewrite ltn0.
have two0 := pm_two_gt0.
have d0 : 0 < eps / 2%:R by apply: divr_gt0.
have /choice[r0 Hr0] : forall i : 'I_n.+1, exists q : rat, `|y i - ratr q| < eps / 2%:R.
  by move=> i; exact: pm_rat_approx (y i) _ d0.
pose S : rat := \sum_(i < n.+1) r0 i.
pose r : {ffun 'I_n.+1 -> rat} := [ffun i => r0 i - S / n.+1%:R].
have rE : forall i, ratr (r i) = ratr (r0 i) - (\sum_(j < n.+1) ratr (r0 j)) / n.+1%:R :> R.
  by move=> i; rewrite ffunE rmorphB fmorph_div rmorph_nat rmorph_sum.
have n0 : (n.+1%:R : R) != 0 by rewrite pnatr_eq0.
have Sbound : `|\sum_(j < n.+1) ratr (r0 j)| <= n.+1%:R * (eps / 2%:R) :> R.
  have -> : \sum_(j < n.+1) ratr (r0 j) = \sum_(j < n.+1) (ratr (r0 j) - y j) :> R.
    by rewrite sumrB y0 subr0.
  apply: le_trans (ler_norm_sum _ _ _) _.
  have -> : n.+1%:R * (eps / 2%:R) = \sum_(j < n.+1) (eps / 2%:R) :> R.
    by rewrite sumr_const card_ord mulr_natl.
  by apply: ler_sum => j _; rewrite distrC; exact: (ltW (Hr0 j)).
exists r; split.
  under eq_bigr => i _ do rewrite rE.
  rewrite sumrB sumr_const card_ord -[X in _ - X]mulr_natr.
  by rewrite (divfK n0) subrr.
move=> i; rewrite rE opprB addrCA.
apply: le_lt_trans (ler_normD _ _) _.
rewrite -[eps](divfK (lt0r_neq0 two0)) mulr_natr mulr2n; apply: ler_ltD; last exact: Hr0.
rewrite normrM normfV normr_nat ler_pdivrMr ?ltr0n// mulrC.
exact: Sbound.
Qed.

Section balanced_event.
Variables (n d : nat).
Local Notation T := (paper_main_sample n d).

(* Countable intersections, scaling, and vectors. *)
Lemma pm_bigcap_measurable_count (U : countType) (F : U -> set T) :
  (forall i, measurable (F i)) -> measurable (\bigcap_i F i).
Proof.
move=> mF; rewrite -[X in measurable X]setCK setC_bigcap; apply: measurableC.
by apply: pm_bigcup_measurable => i; exact: measurableC.
Qed.

Lemma pm_sqnorm_scale (c : R) (v : 'cV[R]_d) : pm_sqnorm d (c *: v) = c * c * pm_sqnorm d v.
Proof. by rewrite /pm_sqnorm mulr_sumr; apply: eq_bigr => a _; rewrite !mxE mulrACA. Qed.

Lemma pm_qf_scale (c : R) (A : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form A (c *: v) = c * c * paper_main_quadratic_form A v.
Proof.
rewrite /paper_main_quadratic_form mulr_sumr; apply: eq_bigr => a _.
rewrite mulr_sumr; apply: eq_bigr => b _; rewrite !mxE.
by rewrite mulrACA [c * _ * c]mulrAC -mulrA [v a 0 * (A a b * v b 0)]mulrA.
Qed.

Lemma pm_qf0 (A : 'M[R]_d) : paper_main_quadratic_form A 0 = 0.
Proof.
by rewrite /paper_main_quadratic_form big1// => a _; rewrite big1// => b _; rewrite mxE mul0r mul0r.
Qed.

Lemma pm_sqnorm0 : pm_sqnorm d 0 = 0.
Proof. by rewrite /pm_sqnorm big1// => a _; rewrite mxE mul0r. Qed.

Lemma pm_col_neq0 (v : 'cV[R]_d) : v != 0 -> exists a, v a 0 != 0.
Proof.
move=> v0; apply: contrapT => h; move/negP: v0; apply; apply/eqP/matrixP => a b.
rewrite mxE (ord1 b); apply/eqP; apply: contrapT => ha; apply: h; exists a; exact/negP.
Qed.

Lemma pm_sqnorm_gt0 (v : 'cV[R]_d) : v != 0 -> 0 < pm_sqnorm d v.
Proof.
move=> v0; have [a va] := pm_col_neq0 v v0.
by apply: lt_le_trans (pm_sq_le_sqnorm d v a); rewrite -expr2 lt0r sqr_ge0 andbT sqrf_eq0.
Qed.

Lemma pm_sqrt_inv_sq (s : R) : 0 < s -> (Num.sqrt s)^-1 * (Num.sqrt s)^-1 * s = 1.
Proof. by move=> s0; rewrite -invfM -expr2 sqr_sqrtr ?(ltW s0)// mulVf// gt_eqF. Qed.

Lemma pm_sqr_le1 (x : R) : x * x <= 1 -> `|x| <= 1.
Proof.
move=> h; rewrite leNgt; apply/negP => h1.
have h0 : 0 <= x * x by rewrite -expr2 sqr_ge0.
have := ltr_pM ler01 ler01 h1 h1; rewrite mul1r -normrM (ger0_norm h0) => h2.
by have := lt_le_trans h2 h; rewrite ltxx.
Qed.

Lemma pm_double_inv (k : nat) : (2 * k + 1).+1%:R^-1 = k.+1%:R^-1 / 2%:R :> R.
Proof.
have e : (2 * k + 1).+1 = (k.+1 * 2)%N by rewrite [(k.+1 * 2)%N]mulnC mulnSr addn2 addn1.
by rewrite e natrM invfM.
Qed.

Lemma pm_double_inv_add (k : nat) :
  (2 * k + 1).+1%:R^-1 + (2 * k + 1).+1%:R^-1 = k.+1%:R^-1 :> R.
Proof.
by rewrite pm_double_inv -mulrDr -mulr2n -(mulr_natr 2%:R^-1 2) mulVf ?mulr1// pnatr_eq0.
Qed.

(* Continuity of the quadratic form and of the squared norm in the vector,
   as functions of a row vector. *)
Lemma pm_continuous_trcoord (a : 'I_d) (p : 'rV[R]_d) :
  {for p, continuous (fun r : 'rV[R]_d => (r^T) a 0)}.
Proof.
have -> : (fun r : 'rV[R]_d => (r^T) a 0) = (fun r : 'rV[R]_d => r ord0 a).
  by apply/funext => r; rewrite mxE.
exact: pm_continuous_coord.
Qed.

Lemma pm_qf_tr_continuous (A : 'M[R]_d) (p : 'rV[R]_d) :
  {for p, continuous (fun r : 'rV[R]_d => paper_main_quadratic_form A r^T)}.
Proof.
rewrite /paper_main_quadratic_form.
refine (pm_continuous_sum _ _ (index_enum _)
  (fun (a : 'I_d) (r : 'rV[R]_d) => \sum_(b < d) (r^T) a 0 * A a b * (r^T) b 0) p _) => a.
refine (pm_continuous_sum _ _ (index_enum _)
  (fun (b : 'I_d) (r : 'rV[R]_d) => (r^T) a 0 * A a b * (r^T) b 0) p _) => b.
refine (pm_continuous_mul _ (fun r : 'rV[R]_d => (r^T) a 0 * A a b) (fun r : 'rV[R]_d => (r^T) b 0)
  p _ (pm_continuous_trcoord b p)).
exact: (pm_continuous_mul _ (fun r : 'rV[R]_d => (r^T) a 0) (fun _ => A a b) p
  (pm_continuous_trcoord a p) (pm_continuous_cst _ _ p)).
Qed.

Lemma pm_sqnorm_tr_continuous (p : 'rV[R]_d) :
  {for p, continuous (fun r : 'rV[R]_d => pm_sqnorm d r^T)}.
Proof.
rewrite /pm_sqnorm.
refine (pm_continuous_sum _ _ (index_enum _)
  (fun (a : 'I_d) (r : 'rV[R]_d) => (r^T) a 0 * (r^T) a 0) p _) => a.
exact: (pm_continuous_mul _ (fun r : 'rV[R]_d => (r^T) a 0) (fun r : 'rV[R]_d => (r^T) a 0) p
  (pm_continuous_trcoord a p) (pm_continuous_trcoord a p)).
Qed.

(* A lower bound of a quadratic form by c |v|^2 on rational vectors holds on
   all vectors. *)
Lemma pm_rat_col_approx (v : 'cV[R]_d) (eps : R) :
  0 < eps -> exists w : 'cV[rat]_d, forall a, `|v a 0 - ratr (w a 0)| < eps.
Proof.
move=> eps0; exists (\col_a sval (cid (pm_rat_approx (v a 0) eps eps0))) => a.
by rewrite mxE; case: cid.
Qed.

Lemma pm_qf_rat_transfer (A : 'M[R]_d) (c : R) :
  (forall w : 'cV[rat]_d,
    c * pm_sqnorm d (map_mx ratr w) <= paper_main_quadratic_form A (map_mx ratr w)) ->
  forall v : 'cV[R]_d, c * pm_sqnorm d v <= paper_main_quadratic_form A v.
Proof.
move=> H v.
have /choice[w Hw] : forall k : nat, exists w : 'cV[rat]_d,
    forall a, `|v a 0 - ratr (w a 0)| < k.+1%:R^-1.
  by move=> k; exact: (pm_rat_col_approx v _ (pm_inv_gt0 k)).
pose u : nat -> 'rV[R]_d := fun k => (map_mx ratr (w k))^T.
have clu : forall B : set 'rV[R]_d, nbhs (v^T) B -> forall k0 : nat,
    exists k, (k0 <= k)%nat /\ B (u k).
  by apply: pm_cluster_of_cvg => k j; rewrite /u !mxE; exact: Hw.
pose g := fun r : 'rV[R]_d => paper_main_quadratic_form A r^T - c * pm_sqnorm d r^T.
have gc : {for v^T, continuous g}.
  exact: (pm_continuous_sub _ (fun r : 'rV[R]_d => paper_main_quadratic_form A r^T)
    (fun r : 'rV[R]_d => c * pm_sqnorm d r^T) (v^T) (pm_qf_tr_continuous A (v^T))
    (pm_continuous_mul _ (fun _ => c) (fun r : 'rV[R]_d => pm_sqnorm d r^T) (v^T)
      (pm_continuous_cst _ _ _) (pm_sqnorm_tr_continuous (v^T)))).
have g0 : 0 <= g (v^T).
  apply: (pm_cluster_value_ge _ u (v^T) g 0 0 gc (lexx 0) clu) => k.
  by rewrite mul0r subr0 /g /u trmxK subr_ge0; exact: H.
by move: g0; rewrite /g trmxK subr_ge0.
Qed.

(* A positive definite matrix is uniformly positive: v^T M v >= |v|^2/(k+1)
   for some k. *)
Lemma pm_pd_uniform (M : 'M[R]_d) : paper_main_pd M ->
  exists k : nat, forall v : 'cV[R]_d,
    k.+1%:R^-1 * pm_sqnorm d v <= paper_main_quadratic_form M v.
Proof.
move=> [Msym Mpd]; apply: contrapT => hno.
have hk : forall k : nat, exists v : 'cV[R]_d,
    paper_main_quadratic_form M v < k.+1%:R^-1 * pm_sqnorm d v.
  move=> k; apply: contrapT => hv; apply: hno; exists k => v.
  by rewrite leNgt; apply/negP => hlt; apply: hv; exists v.
have /choice[v Hv] := hk.
have v0 : forall k, v k != 0.
  move=> k; apply/eqP => vk0; have := Hv k.
  by rewrite vk0 pm_qf0 pm_sqnorm0 mulr0 ltxx.
have spos : forall k, 0 < pm_sqnorm d (v k).
  move=> k; have := lt_trans (Mpd _ (v0 k)) (Hv k).
  by rewrite pmulr_rgt0// pm_inv_gt0.
pose c := fun k => (Num.sqrt (pm_sqnorm d (v k)))^-1.
have cc : forall k, c k * c k * pm_sqnorm d (v k) = 1.
  by move=> k; exact: pm_sqrt_inv_sq (spos k).
have cc0 : forall k, 0 < c k * c k.
  by move=> k; apply: mulr_gt0; rewrite /c invr_gt0 sqrtr_gt0.
pose w := fun k => c k *: v k.
have wnorm : forall k, pm_sqnorm d (w k) = 1 by move=> k; rewrite /w pm_sqnorm_scale cc.
have wqf : forall k, paper_main_quadratic_form M (w k) < k.+1%:R^-1.
  move=> k; rewrite /w pm_qf_scale; have := Hv k.
  by rewrite -(ltr_pM2l (cc0 k)) mulrCA (cc k) mulr1.
pose u : nat -> 'rV[R]_d := fun k => (w k)^T.
have ubox : forall k, pm_box d 1 (u k).
  move=> k a; rewrite /u /pm_seg/= mxE -ler_norml; apply: pm_sqr_le1.
  by rewrite -(wnorm k); exact: pm_sq_le_sqnorm.
have [p [_ clp]] := pm_box_cluster d u 1 ubox.
have pn : pm_sqnorm d p^T = 1.
  apply: (pm_cluster_value_eq _ u p (fun r : 'rV[R]_d => pm_sqnorm d r^T) 1
    (pm_sqnorm_tr_continuous p) clp) => k.
  by rewrite /u trmxK wnorm.
have pq : paper_main_quadratic_form M p^T <= 0.
  apply: (pm_cluster_value_le _ u p (fun r : 'rV[R]_d => paper_main_quadratic_form M r^T) 0 1
    (pm_qf_tr_continuous M p) ler01 clp) => k.
  by rewrite add0r mul1r /u trmxK; exact: (ltW (wqf k)).
have pT0 : p^T != 0.
  by apply/eqP => p0; move: pn; rewrite p0 pm_sqnorm0 => /eqP; rewrite eq_sym oner_eq0.
by have := lt_le_trans (Mpd _ pT0) pq; rewrite ltxx.
Qed.

(* The balanced matrix and its symmetry. *)
Definition pm_bal_weight (r : {ffun 'I_n -> rat}) : 'I_n -> R := fun i => ratr (r i).

Definition pm_bal_mx (r : {ffun 'I_n -> rat}) (x : T) : 'M[R]_d :=
  pm_balanced_matrix n d (pm_bal_weight r) x.

Lemma pm_balanced_matrix_sym (y : 'I_n -> R) (x : T) :
  paper_main_symmetric (pm_balanced_matrix n d y x).
Proof.
move=> a b; rewrite !pm_balanced_matrix_entry; apply: eq_bigr => i _.
by rewrite [paper_main_point x i a 0 * _]mulrC.
Qed.

(* The countable index: rational weights r with sum zero, and k; the set
   asks the uniform bound on every rational vector. *)
Definition pm_bal_pos (r : {ffun 'I_n -> rat}) (k : nat) : set T :=
  \bigcap_(w : 'cV[rat]_d) [set x : T |
    k.+1%:R^-1 * pm_sqnorm d (map_mx ratr w)
    <= paper_main_quadratic_form (pm_bal_mx r x) (map_mx ratr w)].

Definition pm_bal_set (r : {ffun 'I_n -> rat}) (k : nat) : set T :=
  [set x : T | (\sum_(i < n) pm_bal_weight r i = 0) /\ pm_bal_pos r k x].

Lemma pm_bal_pos_measurable (r : {ffun 'I_n -> rat}) (k : nat) : measurable (pm_bal_pos r k).
Proof.
apply: pm_bigcap_measurable_count => w.
exact: (pm_measurable_le n d (fun _ => k.+1%:R^-1 * pm_sqnorm d (map_mx ratr w))
  (fun x => paper_main_quadratic_form (pm_bal_mx r x) (map_mx ratr w))
  (pm_measurable_cst n d _) (pm_balanced_quadratic_form_measurable n d _ _)).
Qed.

Lemma pm_bal_set_measurable (r : {ffun 'I_n -> rat}) (k : nat) : measurable (pm_bal_set r k).
Proof. exact: (pm_measurable_guard n d _ _ (pm_bal_pos_measurable r k)). Qed.

(* The union of the index sets is contained in the event. *)
Lemma pm_bal_event_sup :
  \bigcup_(r : {ffun 'I_n -> rat}) \bigcup_(k : nat) pm_bal_set r k
  `<=` paper_main_balanced_pd_event n d.
Proof.
move=> x [r _ [k _ [r0 Hpos]]].
exists (pm_bal_weight r); split; first exact: r0.
split; first exact: pm_balanced_matrix_sym.
move=> v v0.
have hall : forall w : 'cV[R]_d,
    k.+1%:R^-1 * pm_sqnorm d w <= paper_main_quadratic_form (pm_bal_mx r x) w.
  by apply: pm_qf_rat_transfer => w; exact: (Hpos w Logic.I).
by apply: lt_le_trans (hall v); apply: mulr_gt0 (pm_inv_gt0 k) _; exact: pm_sqnorm_gt0.
Qed.

(* The event is contained in the union of the index sets. *)
Lemma pm_bal_event_sub :
  paper_main_balanced_pd_event n d
  `<=` \bigcup_(r : {ffun 'I_n -> rat}) \bigcup_(k : nat) pm_bal_set r k.
Proof.
move=> x [y [y0 ypd]].
have [k Hk] := pm_pd_uniform _ ypd.
pose X := 1 + \sum_(i < n) \sum_(a < d) `|paper_main_point x i a 0|.
have X0 : 0 <= \sum_(i < n) \sum_(a < d) `|paper_main_point x i a 0|.
  by apply: sumr_ge0 => i _; apply: sumr_ge0 => a _; exact: normr_ge0.
have X1 : 1 <= X by rewrite /X lerDl.
have sumX : \sum_(i < n) \sum_(a < d) `|paper_main_point x i a 0| <= X.
  by rewrite /X lerDr ler01.
have rowX : forall i : 'I_n, \sum_(a < d) `|paper_main_point x i a 0| <= X.
  move=> i; apply: le_trans _ sumX; rewrite [Y in _ <= Y](bigD1 i)//= lerDl.
  by apply: sumr_ge0 => j _; apply: sumr_ge0 => a _; exact: normr_ge0.
have Xa : forall (i : 'I_n) (a : 'I_d), `|paper_main_point x i a 0| <= X.
  move=> i a; apply: le_trans _ (rowX i).
  by rewrite [Y in _ <= Y](bigD1 a)//= lerDl; apply: sumr_ge0 => b _; exact: normr_ge0.
have XX0 : 0 <= X * X by apply: mulr_ge0; exact: le_trans ler01 X1.
pose L := n%:R * (X * X) * (2 * (d%:R * d%:R)) + 1.
have dd0 : 0 <= (2%:R : R) * (d%:R * d%:R).
  by apply: mulr_ge0; [exact: ler0n | apply: mulr_ge0; exact: ler0n].
have L1 : 1 <= L.
  by rewrite /L lerDr; apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ler0n.
have L0 : 0 < L := lt_le_trans ltr01 L1.
have hL : n%:R * (X * X) * (2 * (d%:R * d%:R)) <= L by rewrite /L lerDl ler01.
pose delta := k.+1%:R^-1 / 2%:R / L.
have delta0 : 0 < delta.
  rewrite /delta; apply: divr_gt0; last exact: L0.
  by apply: divr_gt0; [exact: pm_inv_gt0 | exact: pm_two_gt0].
have deltaL : delta * L = k.+1%:R^-1 / 2%:R by rewrite /delta (divfK (lt0r_neq0 L0)).
have [r [r0 Hr]] := pm_rat_zero_sum_approx n y delta delta0 y0.
pose D : 'M[R]_d := pm_bal_mx r x - pm_balanced_matrix n d y x.
have DE : forall a b, D a b
    = \sum_(i < n) (ratr (r i) - y i) * (paper_main_point x i a 0 * paper_main_point x i b 0).
  move=> a b; rewrite /D !mxE /pm_bal_mx !pm_balanced_matrix_entry -sumrB.
  by apply: eq_bigr => i _; rewrite mulrBl.
pose eta := n%:R * (delta * (X * X)).
have eta0 : 0 <= eta.
  by apply: mulr_ge0; [exact: ler0n | apply: mulr_ge0 => //; exact: (ltW delta0)].
have Deta : forall a b, `|D a b| <= eta.
  move=> a b; rewrite DE; apply: le_trans (ler_norm_sum _ _ _) _.
  have -> : eta = \sum_(i < n) (delta * (X * X)).
    by rewrite /eta sumr_const card_ord mulr_natl.
  apply: ler_sum => i _; rewrite normrM; apply: ler_pM; first exact: normr_ge0.
  - exact: normr_ge0.
  - by rewrite distrC; exact: (ltW (Hr i)).
  - by rewrite normrM; exact: (ler_pM (normr_ge0 _) (normr_ge0 _) (Xa i a) (Xa i b)).
have etad : eta * (2 * (d%:R * d%:R)) <= (2 * k + 1).+1%:R^-1.
  rewrite pm_double_inv /eta [n%:R * (delta * _)]mulrCA -mulrA -deltaL.
  exact: (ler_wpM2l (ltW delta0) hL).
have qD : forall v, paper_main_quadratic_form (pm_bal_mx r x) v
    = paper_main_quadratic_form (pm_balanced_matrix n d y x) v
      + paper_main_quadratic_form D v.
  by move=> v; rewrite -pm_qf_add /D addrCA subrr addr0.
exists r; first by [].
exists (2 * k + 1)%N; first by [].
split; first exact: r0.
move=> w _.
have [h1 _] := pm_qf_diff_bound d D (map_mx ratr w) eta (2 * k + 1) eta0 Deta etad.
suff h : (2 * k + 1).+1%:R^-1 * pm_sqnorm d (map_mx ratr w)
    <= paper_main_quadratic_form (pm_bal_mx r x) (map_mx ratr w) by exact: h.
rewrite qD; apply: le_trans _ (lerD (Hk (map_mx ratr w)) h1).
by rewrite lerBrDr -mulrDl pm_double_inv_add lexx.
Qed.

Lemma pm_bal_event_eq :
  paper_main_balanced_pd_event n d
  = \bigcup_(r : {ffun 'I_n -> rat}) \bigcup_(k : nat) pm_bal_set r k.
Proof.
by rewrite eqEsubset; split; [exact: pm_bal_event_sub | exact: pm_bal_event_sup].
Qed.

(* The balanced positive definite event is measurable, for every n and d. *)
Theorem pm_balanced_pd_event_measurable : measurable (paper_main_balanced_pd_event n d).
Proof.
rewrite pm_bal_event_eq; apply: pm_bigcup_measurable => r.
by apply: pm_bigcup_measurable => k; exact: pm_bal_set_measurable.
Qed.

End balanced_event.
