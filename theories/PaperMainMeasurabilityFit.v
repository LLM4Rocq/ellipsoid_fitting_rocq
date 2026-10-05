(* Measurability of paper_main_fit_event, the first conjunct of the first
   clause of paper_main_results. Internal proof module of the
   MathComp-Analysis port, written on 30 September 2026 by a Claude Code
   session (Fable 5.1). Nothing here is reviewed or accepted; the statement
   and the glossary are not edited.

   The fit event {x | exists S >= 0 with x_i^T S x_i = d for all i} is the
   union over m of the levels

     F_m = bigcap_(k) bigcup_(q rational, symmetric, |q| <= m, q + I/(k+1) >= 0)
             {x | residual (ratr q) x < 1/(k+1)},

   where residual S x = sum_i (x_i^T S x_i - d)^2. The conditions on q are
   conditions on the countable index, not on the sample, so each level is
   measurable by the coordinate polynomials (PaperMainMeasurabilityCoordinates)
   and the countable unions (PaperMainMeasurabilityCountable). The equality
   of sets: a fit S is approximated by symmetric rational matrices
   (pm_rat_sym_approx), whose residual is small by an entrywise estimate;
   conversely a sequence of rational witnesses lies in a box, has a cluster
   point (PaperMainMeasurabilityBox, PaperMainMeasurabilityCompact), and the
   cluster point is a fit by continuity of the residual, of the entries and
   of the quadratic form in the matrix. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean interval matrix rat.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions.
From EllipsoidFitting Require Import PaperMainMeasurabilityCoordinates PaperMainMeasurabilityBox
  PaperMainMeasurabilityCompact PaperMainMeasurabilityCountable.

Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section fit_event.
Variables (n d : nat).
Local Notation T := (paper_main_sample n d).
Local Notation RT := (measurableTypeR R).
Local Notation V := 'rV[R]_(d * d).

(* The real matrix of a rational matrix. *)
Definition pm_rmx (q : 'M[rat]_d) : 'M[R]_d := map_mx ratr q.

Lemma pm_rmxE (q : 'M[rat]_d) (a b : 'I_d) : pm_rmx q a b = ratr (q a b).
Proof. by rewrite mxE. Qed.

Lemma pm_rmx_sym (q : 'M[rat]_d) :
  (forall i j, q i j = q j i) -> paper_main_symmetric (pm_rmx q).
Proof. by move=> qs i j; rewrite !pm_rmxE qs. Qed.

(* The squared norm of a column vector. *)
Definition pm_sqnorm (v : 'cV[R]_d) : R := \sum_(i < d) v i 0 * v i 0.

Lemma pm_sqnorm_ge0 (v : 'cV[R]_d) : 0 <= pm_sqnorm v.
Proof. by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0. Qed.

Lemma pm_sq_le_sqnorm (v : 'cV[R]_d) (a : 'I_d) : v a 0 * v a 0 <= pm_sqnorm v.
Proof.
rewrite /pm_sqnorm (bigD1 a)//= lerDl; apply: sumr_ge0 => i _.
by rewrite -expr2 sqr_ge0.
Qed.

Lemma pm_absmul_le (a b : R) : `|a| * `|b| <= a * a + b * b.
Proof.
have aa : `|a| * `|a| = a * a by rewrite -normrM ger0_norm// -expr2 sqr_ge0.
have bb : `|b| * `|b| = b * b by rewrite -normrM ger0_norm// -expr2 sqr_ge0.
have [ab|ba] := leP `|a| `|b|.
- rewrite -[b * b]bb; apply: le_trans (ler_wpM2r (normr_ge0 b) ab) _.
  by rewrite lerDr -expr2 sqr_ge0.
- rewrite -[a * a]aa; apply: le_trans (ler_wpM2l (normr_ge0 a) (ltW ba)) _.
  by rewrite lerDl -expr2 sqr_ge0.
Qed.

Lemma pm_sqr_le (a b : R) : `|a| <= b -> a ^+ 2 <= b ^+ 2.
Proof.
move=> ab; have aa : `|a| * `|a| = a * a by rewrite -normrM ger0_norm// -expr2 sqr_ge0.
by rewrite !expr2 -aa; exact: (ler_pM (normr_ge0 _) (normr_ge0 _) ab ab).
Qed.

(* The quadratic form of a matrix with small entries is small. *)
Lemma pm_qf_small (A : 'M[R]_d) (v : 'cV[R]_d) (eta : R) :
  0 <= eta -> (forall i j, `|A i j| <= eta) ->
  `|paper_main_quadratic_form A v| <= eta * (2 * pm_sqnorm v) * (d%:R * d%:R).
Proof.
move=> eta0 HA; rewrite /paper_main_quadratic_form.
set c := eta * (2 * pm_sqnorm v).
have hterm : forall a b : 'I_d, `|v a 0 * A a b * v b 0| <= c.
  move=> a b; rewrite !normrM.
  have h1 : `|v a 0| * `|A a b| * `|v b 0| <= eta * (`|v a 0| * `|v b 0|).
    rewrite mulrAC [eta * _]mulrC.
    exact: (ler_wpM2l (mulr_ge0 (normr_ge0 _) (normr_ge0 _)) (HA a b)).
  apply: (le_trans h1); rewrite /c; apply: (ler_wpM2l eta0).
  apply: (le_trans (pm_absmul_le _ _)).
  by rewrite mulr_natl mulr2n; apply: lerD; apply: pm_sq_le_sqnorm.
have hrow : forall a : 'I_d, `|\sum_(b < d) v a 0 * A a b * v b 0| <= c * d%:R.
  move=> a; apply: (le_trans (ler_norm_sum _ _ _)).
  have -> : c * d%:R = \sum_(b < d) c by rewrite sumr_const card_ord mulr_natr.
  by apply: ler_sum => b _; exact: hterm.
apply: (le_trans (ler_norm_sum _ _ _)).
have -> : c * (d%:R * d%:R) = \sum_(a < d) (c * d%:R).
  by rewrite sumr_const card_ord mulrA (mulr_natr (c * d%:R) d).
by apply: ler_sum => a _; exact: hrow.
Qed.

(* The quadratic form is additive in the matrix. *)
Lemma pm_qf_add (A B : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form (A + B) v
  = paper_main_quadratic_form A v + paper_main_quadratic_form B v.
Proof.
rewrite /paper_main_quadratic_form -big_split; apply: eq_bigr => a _.
rewrite -big_split; apply: eq_bigr => b _.
by rewrite mxE mulrDr mulrDl.
Qed.

Lemma pm_fit_residual_ge0 (S : 'M[R]_d) (x : T) : 0 <= pm_fit_residual n d S x.
Proof. by apply: sumr_ge0 => i _; exact: sqr_ge0. Qed.

(* Numerical facts about the tolerances 1 / (k + 1). The casts pin the
   carrier without opening Stdlib's R_scope on a numeral: a cast (t : R)
   elaborates t in R_scope, where 2 is IZR 2 and + is Rplus, on which the
   MathComp rewrite rules do not fire. *)
Lemma pm_two_gt0 : 0 < (2%:R : R).
Proof. by rewrite ltr0n. Qed.

Lemma pm_inv_gt0 (k : nat) : 0 < (k.+1%:R^-1 : R).
Proof. by rewrite invr_gt0 ltr0n. Qed.

Lemma pm_inv_le1 (k : nat) : (k.+1%:R^-1 : R) <= 1.
Proof. by rewrite invf_le1 ?ltr0n// ler1n. Qed.

Lemma pm_half_lt (k : nat) : (k.+1%:R^-1 : R) / 2%:R < k.+1%:R^-1.
Proof. by rewrite ltr_pdivrMr ?ltr0n// mulr_natr mulr2n ltrDr pm_inv_gt0. Qed.

(* The countable index: a symmetric rational matrix with entries bounded by
   m whose quadratic form is bounded below by - |v|^2 / (k + 1). *)
Definition pm_fit_index (m k : nat) (q : 'M[rat]_d) : Prop :=
  paper_main_symmetric (pm_rmx q) /\
  (forall i j, `|pm_rmx q i j| <= m%:R) /\
  (forall v : 'cV[R]_d,
    - (k.+1%:R^-1 * pm_sqnorm v) <= paper_main_quadratic_form (pm_rmx q) v).

Definition pm_fit_approx (m k : nat) : set T :=
  \bigcup_(q : 'M[rat]_d)
    [set x : T | pm_fit_index m k q /\ pm_fit_residual n d (pm_rmx q) x < k.+1%:R^-1].

Definition pm_fit_level (m : nat) : set T := \bigcap_(k : nat) pm_fit_approx m k.

Lemma pm_fit_approx_measurable (m k : nat) : measurable (pm_fit_approx m k).
Proof.
apply: pm_bigcup_measurable => q; apply: pm_measurable_guard.
exact: (pm_measurable_lt n d (fun x => pm_fit_residual n d (pm_rmx q) x)
  (fun _ => k.+1%:R^-1) (pm_fit_residual_measurable n d _) (pm_measurable_cst n d _)).
Qed.

Lemma pm_fit_level_measurable (m : nat) : measurable (pm_fit_level m).
Proof. by apply: pm_bigcap_measurable => k; exact: pm_fit_approx_measurable. Qed.

(* Every real matrix has entries bounded by a natural number, with room 1. *)
Lemma pm_entry_bound (S : 'M[R]_d) : exists m : nat, forall a b, `|S a b| + 1 <= m%:R.
Proof.
pose M := \sum_(i < d) \sum_(j < d) `|S i j|.
have M0 : 0 <= M by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _; exact: normr_ge0.
have rowM : forall a, \sum_(j < d) `|S a j| <= M.
  move=> a; rewrite /M [X in _ <= X](bigD1 a)//= lerDl.
  by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _; exact: normr_ge0.
have SM : forall a b, `|S a b| <= M.
  move=> a b; apply: le_trans _ (rowM a).
  by rewrite [X in _ <= X](bigD1 b)//= lerDl; apply: sumr_ge0 => j _; exact: normr_ge0.
exists (Num.bound M).+1 => a b; rewrite -natr1 lerD2r; apply: le_trans (SM a b) _.
by apply: ltW; exact: archi_boundP.
Qed.

(* The fit part of the witness. A symmetric rational q entrywise within eta
   of a fit S satisfies the fit index and has a small residual, provided eta
   is small against the dimension and against the sample (the constant C
   below). The choice of eta is left to the caller, so that the conditioned
   event can add its own requirements. *)
Lemma pm_fit_witness (S : 'M[R]_d) (x : T) (m k : nat) (eta : R) (q : 'M[rat]_d) :
  paper_main_psd S ->
  (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R) ->
  (forall a b, `|S a b| + 1 <= m%:R) ->
  0 < eta -> eta <= 1 ->
  eta * (2 * (d%:R * d%:R)) <= k.+1%:R^-1 ->
  eta * (\sum_(i < n) (2 * pm_sqnorm (paper_main_point x i) * (d%:R * d%:R)) ^+ 2)
    < k.+1%:R^-1 ->
  (forall i j, q i j = q j i) -> (forall i j, `|S i j - ratr (q i j)| < eta) ->
  pm_fit_index m k q /\ pm_fit_residual n d (pm_rmx q) x < k.+1%:R^-1.
Proof.
move=> [Ssym Spsd] Sfit SM eta0 eta1 etad etaC qsym qS.
pose D : 'M[R]_d := pm_rmx q - S.
have Deta : forall i j, `|D i j| <= eta.
  by move=> i j; rewrite /D !mxE distrC; apply/ltW; exact: qS.
have qD : forall v, paper_main_quadratic_form (pm_rmx q) v
    = paper_main_quadratic_form S v + paper_main_quadratic_form D v.
  by move=> v; rewrite -pm_qf_add /D addrCA subrr addr0.
split.
  split; first exact: pm_rmx_sym.
  split.
  - move=> i j; apply: le_trans _ (SM i j).
    rewrite pm_rmxE -[ratr (q i j)](addrNK (S i j)).
    apply: le_trans (ler_normD _ _) _.
    rewrite [X in X <= _]addrC; apply: lerD (lexx _) _.
    by rewrite distrC; apply: le_trans _ eta1; apply/ltW; exact: qS.
  - move=> v; rewrite qD.
    apply: le_trans _ (lerD (Spsd v) (lexx (paper_main_quadratic_form D v))).
    rewrite add0r.
    have := pm_qf_small D v eta (ltW eta0) Deta; rewrite ler_norml => /andP[hs1 _].
    apply: le_trans _ hs1; rewrite lerN2 -mulrA [2 * _ * _]mulrAC mulrA.
    exact: (ler_wpM2r (pm_sqnorm_ge0 v) etad).
apply: le_lt_trans _ etaC.
rewrite mulr_sumr /pm_fit_residual; apply: ler_sum => i _.
have -> : paper_main_quadratic_form (pm_rmx q) (paper_main_point x i) - d%:R
    = paper_main_quadratic_form D (paper_main_point x i).
  by rewrite qD Sfit addrAC subrr add0r.
apply: le_trans (pm_sqr_le _ _ (pm_qf_small D (paper_main_point x i) eta (ltW eta0) Deta)) _.
rewrite -mulrA exprMn; apply: (ler_wpM2r (sqr_ge0 _)).
by rewrite expr2; exact: (ler_piMr (ltW eta0) eta1).
Qed.

(* The fit event is contained in the union of the levels. *)
Lemma pm_fit_event_sub : paper_main_fit_event n d `<=` \bigcup_(m : nat) pm_fit_level m.
Proof.
move=> x [S [Spsd Sfit]].
have [m SM] := pm_entry_bound S.
exists m; first by [].
move=> k _.
have k0 := pm_inv_gt0 k.
have dd0 : 0 <= (2%:R : R) * (d%:R * d%:R).
  by apply: mulr_ge0; [exact: ler0n | apply: mulr_ge0; exact: ler0n].
pose C := \sum_(i < n) (2 * pm_sqnorm (paper_main_point x i) * (d%:R * d%:R)) ^+ 2.
have C0 : 0 <= C by apply: sumr_ge0 => i _; exact: sqr_ge0.
pose K := 2 * (d%:R * d%:R) + C + 1.
have K1 : 1 <= K by rewrite /K lerDr; apply: addr_ge0.
have K0 : 0 < K := lt_le_trans ltr01 K1.
have CK : C <= K by rewrite /K addrAC lerDr; apply: addr_ge0 => //; exact: ler01.
have ddK : 2 * (d%:R * d%:R) <= K.
  by rewrite /K -addrA lerDl; apply: addr_ge0 => //; exact: ler01.
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
have [q [qsym qS]] := pm_rat_sym_approx _ S eta eta0 Spsd.1.
have [idx res] := pm_fit_witness S x m k eta q Spsd Sfit SM eta0 eta1 etad etaC qsym qS.
exists q; first by [].
by split.
Qed.

(* Continuity in the vectorised matrix of the entries, of the quadratic form
   and of the residual. *)
Lemma pm_continuous_vec_entry (a b : 'I_d) (p : V) :
  {for p, continuous (fun w : V => vec_mx w a b)}.
Proof.
have -> : (fun w : V => vec_mx w a b) = (fun w : V => w ord0 (mxvec_index a b)).
  by apply/funext => w; rewrite mxE.
exact: pm_continuous_coord.
Qed.

Definition pm_qf_vec (v : 'cV[R]_d) (w : V) : R := paper_main_quadratic_form (vec_mx w) v.

Lemma pm_qf_vec_continuous (v : 'cV[R]_d) (p : V) : {for p, continuous (pm_qf_vec v)}.
Proof.
rewrite /pm_qf_vec /paper_main_quadratic_form.
refine (pm_continuous_sum _ _ (index_enum _)
  (fun a w => \sum_(b < d) v a 0 * vec_mx w a b * v b 0) p _) => a.
refine (pm_continuous_sum _ _ (index_enum _)
  (fun b w => v a 0 * vec_mx w a b * v b 0) p _) => b.
refine (pm_continuous_mul _ (fun w => v a 0 * vec_mx w a b) (fun _ => v b 0) p _
  (pm_continuous_cst _ _ p)).
exact: (pm_continuous_mul _ (fun _ => v a 0) (fun w => vec_mx w a b) p
  (pm_continuous_cst _ _ p) (pm_continuous_vec_entry a b p)).
Qed.

Definition pm_res_vec (x : T) (w : V) : R := pm_fit_residual n d (vec_mx w) x.

Lemma pm_res_vec_continuous (x : T) (p : V) : {for p, continuous (pm_res_vec x)}.
Proof.
have -> : pm_res_vec x = fun w : V => \sum_(i < n)
    ((pm_qf_vec (paper_main_point x i) w - d%:R) * (pm_qf_vec (paper_main_point x i) w - d%:R)).
  by apply/funext => w; rewrite /pm_res_vec /pm_fit_residual; apply: eq_bigr => i _; rewrite expr2.
refine (pm_continuous_sum _ _ (index_enum _) (fun (i : 'I_n) (w : V) =>
  (pm_qf_vec (paper_main_point x i) w - d%:R) * (pm_qf_vec (paper_main_point x i) w - d%:R)) p _) => i.
have hc : {for p, continuous (fun w : V => pm_qf_vec (paper_main_point x i) w - d%:R)}.
  exact: (pm_continuous_sub _ (pm_qf_vec (paper_main_point x i)) (fun _ => d%:R) p
    (pm_qf_vec_continuous _ p) (pm_continuous_cst _ _ p)).
exact: (pm_continuous_mul _ _ _ p hc hc).
Qed.

(* A sequence of rational witnesses of the fit index, with residuals
   vanishing, has a cluster point p (as a vectorised matrix) such that
   vec_mx p is a fit. The cluster property of p is returned, so that the
   conditioned event can read further properties of vec_mx p from further
   tolerances on the sequence. *)
Lemma pm_fit_cluster (x : T) (m : nat) (q : nat -> 'M[rat]_d) :
  (forall k, pm_fit_index m k (q k) /\ pm_fit_residual n d (pm_rmx (q k)) x < k.+1%:R^-1) ->
  exists p : V,
    (forall B : set V, nbhs p B -> forall k0 : nat,
       exists k, (k0 <= k)%nat /\ B (mxvec (pm_rmx (q k)))) /\
    paper_main_psd (vec_mx p) /\
    forall i : 'I_n, paper_main_quadratic_form (vec_mx p) (paper_main_point x i) = d%:R.
Proof.
move=> Hq.
pose u : nat -> V := fun k => mxvec (pm_rmx (q k)).
have ubox : forall k, pm_box (d * d)%N m%:R (u k).
  move=> k j; have [[_ [qb _]] _] := Hq k.
  case/mxvec_indexP: j => a b; rewrite /u /pm_seg/= mxvecE.
  by move: (qb a b); rewrite ler_norml.
have [p [_ clp]] := pm_box_cluster (d * d)%N u m%:R ubox.
pose S : 'M[R]_d := vec_mx p.
have uk : forall k, vec_mx (u k) = pm_rmx (q k) by move=> k; rewrite /u mxvecK.
have Ssym : paper_main_symmetric S.
  move=> a b.
  pose g := fun w : V => vec_mx w a b - vec_mx w b a.
  have gc : {for p, continuous g}.
    exact: (pm_continuous_sub _ (fun w : V => vec_mx w a b) (fun w : V => vec_mx w b a) p
      (pm_continuous_vec_entry a b p) (pm_continuous_vec_entry b a p)).
  have g0 : g p = 0.
    apply: (pm_cluster_value_eq _ u p g 0 gc clp) => k.
    have [[qs _] _] := Hq k.
    by rewrite /g uk qs subrr.
  by move: g0; rewrite /g /S; move/eqP; rewrite subr_eq0 => /eqP.
have Spsd : forall v : 'cV[R]_d, 0 <= paper_main_quadratic_form S v.
  move=> v.
  have g0 : 0 <= pm_qf_vec v p.
    apply: (pm_cluster_value_ge _ u p (pm_qf_vec v) 0 (pm_sqnorm v)
      (pm_qf_vec_continuous v p) (pm_sqnorm_ge0 v) clp) => k.
    have [[_ [_ qp]] _] := Hq k.
    by rewrite sub0r mulrC /pm_qf_vec uk; exact: qp.
  by move: g0; rewrite /pm_qf_vec /S.
have res0 : pm_fit_residual n d S x = 0.
  have g0 : pm_res_vec x p = 0.
    apply: (pm_cluster_value_zero _ u p (pm_res_vec x) 1
      (pm_res_vec_continuous x p) ler01 clp) => k.
    have [_ rk] := Hq k.
    by rewrite mul1r /pm_res_vec uk (ger0_norm (pm_fit_residual_ge0 _ _)); exact: (ltW rk).
  by move: g0; rewrite /pm_res_vec /S.
have Sfit : forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R.
  move=> i; move: res0; rewrite /pm_fit_residual => res0.
  have Fge0 : forall i : 'I_n, true ->
      0 <= (paper_main_quadratic_form S (paper_main_point x i) - d%:R) ^+ 2.
    by move=> j _; exact: sqr_ge0.
  have := psumr_eq0P Fge0 res0 (i := i) isT.
  by move/eqP; rewrite sqrf_eq0 subr_eq0 => /eqP.
by exists p; split; [exact: clp | split; [split; [exact: Ssym | exact: Spsd] | exact: Sfit]].
Qed.

(* The union of the levels is contained in the fit event. *)
Lemma pm_fit_event_sup : \bigcup_(m : nat) pm_fit_level m `<=` paper_main_fit_event n d.
Proof.
move=> x [m _ Hm].
have /choice[q Hq] : forall k : nat, exists q : 'M[rat]_d,
    pm_fit_index m k q /\ pm_fit_residual n d (pm_rmx q) x < k.+1%:R^-1.
  by move=> k; have [q _ Hq] := Hm k Logic.I; exists q.
have [p [_ [Spsd Sfit]]] := pm_fit_cluster x m q Hq.
by exists (vec_mx p); split.
Qed.

Lemma pm_fit_event_eq : paper_main_fit_event n d = \bigcup_(m : nat) pm_fit_level m.
Proof.
by rewrite eqEsubset; split; [exact: pm_fit_event_sub | exact: pm_fit_event_sup].
Qed.

(* The fit event is measurable, for every n and d. *)
Theorem pm_fit_event_measurable : measurable (paper_main_fit_event n d).
Proof.
by rewrite pm_fit_event_eq; apply: pm_bigcup_measurable => m; exact: pm_fit_level_measurable.
Qed.

End fit_event.
