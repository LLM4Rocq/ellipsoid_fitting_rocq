(* Measurability of paper_main_conditioned_event, the first conjunct of the
   second clause of paper_main_results, for arbitrary real bounds lm and lp.

   The route is that of Measurability.Fit: the event is the union
   over m of the levels bigcap_k bigcup_q {x | index m k q /\ residual
   (ratr q) x < 1/(k+1)}, where the index now also asks that the trace of
   ratr q is within 1/(k+1) of d and that the two Loewner conditions hold
   with tolerance |v|^2/(k+1). The fit part of both inclusions is
   pm_fit_witness and pm_fit_cluster of that module; the trace and the
   Loewner conditions are read from the tolerances with the same cluster
   point. *)
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
  Measurability.Fit.

Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section conditioned_event.
Variables (n d : nat) (lm lp : R).
Local Notation T := (paper_main_sample n d).
Local Notation V := 'rV[R]_(d * d).

(* Scalar matrices, symmetry, and the quadratic form and trace as functions
   of the matrix. *)
Lemma pm_scalar_sym (c : R) : paper_main_symmetric (c *: 1%:M : 'M[R]_d).
Proof. by move=> a b; rewrite !mxE (eq_sym a b). Qed.

Lemma pm_sym_sub (A B : 'M[R]_d) :
  paper_main_symmetric A -> paper_main_symmetric B -> paper_main_symmetric (A - B).
Proof. by move=> As Bs a b; rewrite !mxE As Bs. Qed.

Lemma pm_qf_sub (A B : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form (A - B) v
  = paper_main_quadratic_form A v - paper_main_quadratic_form B v.
Proof. by apply/eqP; rewrite eq_sym subr_eq -pm_qf_add subrK eqxx. Qed.

Lemma pm_qf_scalar (c : R) (v : 'cV[R]_d) :
  paper_main_quadratic_form (c *: 1%:M) v = c * pm_sqnorm d v.
Proof.
rewrite /paper_main_quadratic_form /pm_sqnorm mulr_sumr; apply: eq_bigr => a _.
have h0 : forall b : 'I_d, b != a -> v a 0 * (c *: 1%:M : 'M[R]_d) a b * v b 0 = 0.
  by move=> b ba; rewrite !mxE eq_sym (negbTE ba) mulr0n mulr0 mulr0 mul0r.
rewrite (bigD1 a)//= (big1 _ _ _ h0) addr0 !mxE eqxx mulr1n mulr1.
by rewrite mulrAC mulrC.
Qed.

Lemma pm_trace_add (A B : 'M[R]_d) :
  paper_main_trace (A + B) = paper_main_trace A + paper_main_trace B.
Proof. by rewrite /paper_main_trace -big_split; apply: eq_bigr => a _; rewrite mxE. Qed.

Lemma pm_trace_bound (D : 'M[R]_d) (eta : R) :
  (forall i j, `|D i j| <= eta) -> `|paper_main_trace D| <= eta * d%:R.
Proof.
move=> Deta; rewrite /paper_main_trace; apply: le_trans (ler_norm_sum _ _ _) _.
have -> : eta * d%:R = \sum_(a < d) eta by rewrite sumr_const card_ord (mulr_natr eta d).
by apply: ler_sum => a _; exact: Deta.
Qed.

(* The quadratic form of a matrix with entries at most eta is within
   |v|^2 / (k + 1) of zero when eta * 2 d^2 <= 1 / (k + 1). *)
Lemma pm_qf_diff_bound (D : 'M[R]_d) (v : 'cV[R]_d) (eta : R) (k : nat) :
  0 <= eta -> (forall i j, `|D i j| <= eta) ->
  eta * (2 * (d%:R * d%:R)) <= k.+1%:R^-1 ->
  - (k.+1%:R^-1 * pm_sqnorm d v) <= paper_main_quadratic_form D v /\
  paper_main_quadratic_form D v <= k.+1%:R^-1 * pm_sqnorm d v.
Proof.
move=> eta0 Deta etad.
have hb : eta * (2 * pm_sqnorm d v) * (d%:R * d%:R) <= k.+1%:R^-1 * pm_sqnorm d v.
  by rewrite -mulrA [2 * _ * _]mulrAC mulrA; exact: (ler_wpM2r (pm_sqnorm_ge0 d v) etad).
have := pm_qf_small d D v eta eta0 Deta; rewrite ler_norml => /andP[h1 h2].
by split; [apply: le_trans _ h1; rewrite lerN2; exact: hb | exact: le_trans h2 hb].
Qed.

(* The countable index: the fit index, the trace within 1 / (k + 1) of d,
   and the two Loewner conditions with tolerance |v|^2 / (k + 1). *)
Definition pm_cond_index (m k : nat) (q : 'M[rat]_d) : Prop :=
  pm_fit_index d m k q /\
  `|paper_main_trace (pm_rmx d q) - d%:R| <= k.+1%:R^-1 /\
  (forall v : 'cV[R]_d,
    - (k.+1%:R^-1 * pm_sqnorm d v)
    <= paper_main_quadratic_form (pm_rmx d q) v - lm * pm_sqnorm d v) /\
  (forall v : 'cV[R]_d,
    paper_main_quadratic_form (pm_rmx d q) v - lp * pm_sqnorm d v
    <= k.+1%:R^-1 * pm_sqnorm d v).

Definition pm_cond_approx (m k : nat) : set T :=
  \bigcup_(q : 'M[rat]_d)
    [set x : T | pm_cond_index m k q /\ pm_fit_residual n d (pm_rmx d q) x < k.+1%:R^-1].

Definition pm_cond_level (m : nat) : set T := \bigcap_(k : nat) pm_cond_approx m k.

Lemma pm_cond_approx_measurable (m k : nat) : measurable (pm_cond_approx m k).
Proof.
apply: pm_bigcup_measurable => q; apply: pm_measurable_guard.
exact: (pm_measurable_lt n d (fun x => pm_fit_residual n d (pm_rmx d q) x)
  (fun _ => k.+1%:R^-1) (pm_fit_residual_measurable n d _) (pm_measurable_cst n d _)).
Qed.

Lemma pm_cond_level_measurable (m : nat) : measurable (pm_cond_level m).
Proof. by apply: pm_bigcap_measurable => k; exact: pm_cond_approx_measurable. Qed.

(* The conditioned event is contained in the union of the levels. *)
Lemma pm_cond_event_sub :
  paper_main_conditioned_event n d lm lp `<=` \bigcup_(m : nat) pm_cond_level m.
Proof.
move=> x [S [Spsd [Sfit [Str [Slm Slp]]]]].
have Slm2 : forall v, lm * pm_sqnorm d v <= paper_main_quadratic_form S v.
  by move=> v; have := Slm.2 v; rewrite pm_qf_sub pm_qf_scalar subr_ge0.
have Slp2 : forall v, paper_main_quadratic_form S v <= lp * pm_sqnorm d v.
  by move=> v; have := Slp.2 v; rewrite pm_qf_sub pm_qf_scalar subr_ge0.
have [m SM] := pm_entry_bound d S.
exists m; first by [].
move=> k _.
have k0 := pm_inv_gt0 k.
have dd0 : 0 <= (2%:R : R) * (d%:R * d%:R).
  by apply: mulr_ge0; [exact: ler0n | apply: mulr_ge0; exact: ler0n].
pose C := \sum_(i < n) (2 * pm_sqnorm d (paper_main_point x i) * (d%:R * d%:R)) ^+ 2.
have C0 : 0 <= C by apply: sumr_ge0 => i _; exact: sqr_ge0.
pose K := 2 * (d%:R * d%:R) + d%:R + C + 1.
have K1 : 1 <= K.
  by rewrite /K lerDr; apply: addr_ge0 => //; apply: addr_ge0 => //; exact: ler0n.
have K0 : 0 < K := lt_le_trans ltr01 K1.
have CK : C <= K.
  rewrite /K addrAC lerDr; apply: addr_ge0; last exact: ler01.
  by apply: addr_ge0 => //; exact: ler0n.
have ddK : 2 * (d%:R * d%:R) <= K.
  rewrite /K -!addrA lerDl; apply: addr_ge0; first exact: ler0n.
  by apply: addr_ge0 => //; exact: ler01.
have dK : d%:R <= K.
  rewrite /K -!addrA addrCA lerDl; apply: addr_ge0 => //.
  by apply: addr_ge0 => //; exact: ler01.
pose eta := k.+1%:R^-1 / 2 / K.
have eta0 : 0 < eta.
  by rewrite /eta; apply: divr_gt0 => //; apply: divr_gt0 => //; exact: pm_two_gt0.
have etaK : eta * K = k.+1%:R^-1 / 2 by rewrite /eta (divfK (lt0r_neq0 K0)).
have eta1 : eta <= 1.
  rewrite /eta ler_pdivrMr// mul1r; apply: le_trans _ K1.
  rewrite ler_pdivrMr ?pm_two_gt0// mul1r; apply: le_trans (pm_inv_le1 k) _.
  by rewrite ler1n.
have etad : eta * (2 * (d%:R * d%:R)) <= k.+1%:R^-1.
  apply: le_trans _ (ltW (pm_half_lt k)); rewrite -etaK.
  exact: (ler_wpM2l (ltW eta0) ddK).
have etaC : eta * C < k.+1%:R^-1.
  apply: le_lt_trans (ler_wpM2l (ltW eta0) CK) _; rewrite etaK; exact: pm_half_lt.
have etadk : eta * d%:R <= k.+1%:R^-1.
  apply: le_trans _ (ltW (pm_half_lt k)); rewrite -etaK.
  exact: (ler_wpM2l (ltW eta0) dK).
have [q [qsym qS]] := pm_rat_sym_approx _ S eta eta0 Spsd.1.
have [idx res] := pm_fit_witness n d S x m k eta q Spsd Sfit SM eta0 eta1 etad etaC qsym qS.
pose D : 'M[R]_d := pm_rmx d q - S.
have Deta : forall i j, `|D i j| <= eta.
  by move=> i j; rewrite /D !mxE distrC; apply/ltW; exact: qS.
have qD : forall v, paper_main_quadratic_form (pm_rmx d q) v
    = paper_main_quadratic_form S v + paper_main_quadratic_form D v.
  by move=> v; rewrite -pm_qf_add /D addrCA subrr addr0.
have trD : paper_main_trace (pm_rmx d q) = paper_main_trace S + paper_main_trace D.
  by rewrite -pm_trace_add /D addrCA subrr addr0.
exists q; first by [].
split; last exact: res.
split; first exact: idx.
split.
  rewrite trD Str addrAC subrr add0r.
  exact: le_trans (pm_trace_bound D eta Deta) etadk.
split.
- move=> v; have [h1 _] := pm_qf_diff_bound D v eta k (ltW eta0) Deta etad.
  rewrite qD addrAC; apply: le_trans h1 _.
  by rewrite lerDr subr_ge0; exact: Slm2.
- move=> v; have [_ h2] := pm_qf_diff_bound D v eta k (ltW eta0) Deta etad.
  rewrite qD addrAC; apply: le_trans _ h2.
  by rewrite -[X in _ <= X]add0r lerD2r subr_le0; exact: Slp2.
Qed.

(* The union of the levels is contained in the conditioned event. *)
Lemma pm_cond_event_sup :
  \bigcup_(m : nat) pm_cond_level m `<=` paper_main_conditioned_event n d lm lp.
Proof.
move=> x [m _ Hm].
have /choice[q Hq] : forall k : nat, exists q : 'M[rat]_d,
    pm_cond_index m k q /\ pm_fit_residual n d (pm_rmx d q) x < k.+1%:R^-1.
  by move=> k; have [q _ Hq] := Hm k Logic.I; exists q.
have Hfit : forall k, pm_fit_index d m k (q k) /\
    pm_fit_residual n d (pm_rmx d (q k)) x < k.+1%:R^-1.
  by move=> k; have [[i1 _] r] := Hq k; split.
have [p [clp [Spsd Sfit]]] := pm_fit_cluster n d x m q Hfit.
pose u : nat -> V := fun k => mxvec (pm_rmx d (q k)).
have uk : forall k, vec_mx (u k) = pm_rmx d (q k) by move=> k; rewrite /u mxvecK.
have clu : forall B : set V, nbhs p B -> forall k0 : nat,
    exists k, (k0 <= k)%nat /\ B (u k).
  exact: clp.
have Str : paper_main_trace (vec_mx p) = d%:R.
  have htr : {for p, continuous (fun w : V => paper_main_trace (vec_mx w))}.
    rewrite /paper_main_trace.
    refine (pm_continuous_sum _ _ (index_enum _)
      (fun (a : 'I_d) (w : V) => vec_mx w a a) p _) => a.
    exact: pm_continuous_vec_entry.
  pose g := fun w : V => paper_main_trace (vec_mx w) - d%:R.
  have gc : {for p, continuous g}.
    exact: (pm_continuous_sub _ (fun w : V => paper_main_trace (vec_mx w)) (fun _ => d%:R) p
      htr (pm_continuous_cst _ _ p)).
  have g0 : g p = 0.
    apply: (pm_cluster_value_zero _ u p g 1 gc ler01 clu) => k.
    have [[_ [tr _]] _] := Hq k.
    by rewrite mul1r /g uk.
  by move: g0; rewrite /g; move/eqP; rewrite subr_eq0 => /eqP.
have Slm2 : forall v : 'cV[R]_d,
    lm * pm_sqnorm d v <= paper_main_quadratic_form (vec_mx p) v.
  move=> v.
  pose g := fun w : V => pm_qf_vec d v w - lm * pm_sqnorm d v.
  have gc : {for p, continuous g}.
    exact: (pm_continuous_sub _ (pm_qf_vec d v) (fun _ => lm * pm_sqnorm d v) p
      (pm_qf_vec_continuous d v p) (pm_continuous_cst _ _ p)).
  have g0 : 0 <= g p.
    apply: (pm_cluster_value_ge _ u p g 0 (pm_sqnorm d v) gc (pm_sqnorm_ge0 d v) clu) => k.
    have [[_ [_ [lo _]]] _] := Hq k.
    by rewrite sub0r mulrC /g /pm_qf_vec uk; exact: lo.
  by move: g0; rewrite /g /pm_qf_vec subr_ge0.
have Slp2 : forall v : 'cV[R]_d,
    paper_main_quadratic_form (vec_mx p) v <= lp * pm_sqnorm d v.
  move=> v.
  pose g := fun w : V => pm_qf_vec d v w - lp * pm_sqnorm d v.
  have gc : {for p, continuous g}.
    exact: (pm_continuous_sub _ (pm_qf_vec d v) (fun _ => lp * pm_sqnorm d v) p
      (pm_qf_vec_continuous d v p) (pm_continuous_cst _ _ p)).
  have g0 : g p <= 0.
    apply: (pm_cluster_value_le _ u p g 0 (pm_sqnorm d v) gc (pm_sqnorm_ge0 d v) clu) => k.
    have [[_ [_ [_ hi]]] _] := Hq k.
    by rewrite add0r mulrC /g /pm_qf_vec uk; exact: hi.
  by move: g0; rewrite /g /pm_qf_vec subr_le0.
exists (vec_mx p); split; [exact: Spsd | split; [exact: Sfit | split; [exact: Str | split]]].
- split; first exact: (pm_sym_sub _ _ Spsd.1 (pm_scalar_sym lm)).
  by move=> v; rewrite pm_qf_sub pm_qf_scalar subr_ge0; exact: Slm2.
- split; first exact: (pm_sym_sub _ _ (pm_scalar_sym lp) Spsd.1).
  by move=> v; rewrite pm_qf_sub pm_qf_scalar subr_ge0; exact: Slp2.
Qed.

Lemma pm_cond_event_eq :
  paper_main_conditioned_event n d lm lp = \bigcup_(m : nat) pm_cond_level m.
Proof.
by rewrite eqEsubset; split; [exact: pm_cond_event_sub | exact: pm_cond_event_sup].
Qed.

(* The conditioned event is measurable, for every n, d, lm and lp. *)
Theorem pm_conditioned_event_measurable :
  measurable (paper_main_conditioned_event n d lm lp).
Proof.
by rewrite pm_cond_event_eq; apply: pm_bigcup_measurable => m; exact: pm_cond_level_measurable.
Qed.

End conditioned_event.
