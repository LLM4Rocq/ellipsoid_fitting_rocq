(* The fitting-error upper bound for arbitrary deterministic Gaussian
   shifts. Orthogonal conjugation preserves the complete trace-normalized
   optimization problem, including its nonnegative fitted level. After
   rotation, ignoring the first coordinate costs only the factor (1+p)/p.
   No bound on the shift and no restriction relative to alpha=1/4 is used. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear interval boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.convex Require Import ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Limit Representation.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Shifted Require Import GaussianRows GaussianExports
  GaussianExistence Translations ResidualRestriction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma fitting_error_rotation_witness n d (U : 'M[R]_d)
    (x y : paper_main_sample n d) (S : 'M[R]_d) (r : R) :
  U \is orthogonalmx ->
  (forall i : 'I_n, paper_main_point y i = U *m paper_main_point x i) ->
  paper_main_psd S -> paper_main_trace S = d%:R ->
  [ /\ paper_main_psd (U^T *m S *m U),
       paper_main_trace (U^T *m S *m U) = d%:R &
       restriction_objective x (U^T *m S *m U) r = restriction_objective y S r].
Proof.
move=> Uo hxy [Ss Sp] St.
have ST : S^T = S by apply/matrixP => i j; rewrite mxE Ss.
split.
- split.
  + have ht : (U^T *m S *m U)^T = U^T *m S *m U.
      by rewrite !trmx_mul trmxK ST mulmxA.
    move=> i j; have h := congr1 (fun A : 'M[R]_d => A j i) ht.
    by rewrite mxE in h.
  + by move=> v; rewrite gaussian_quadratic_rotation; exact: Sp.
- rewrite !paper_traceE mxtrace_mulC mulmxA.
  have UU : U *m U^T = 1%:M by apply/orthogonalmxP.
  by rewrite UU mul1mx -paper_traceE.
- rewrite /restriction_objective; congr (_ / _).
  by apply: eq_bigr => i _; rewrite gaussian_quadratic_rotation -hxy.
Qed.

Theorem fitting_error_rotation_points n d (U : 'M[R]_d)
    (x y : paper_main_sample n d) :
  U \is orthogonalmx ->
  (forall i : 'I_n, paper_main_point y i = U *m paper_main_point x i) ->
  universality_fitting_error n d x = universality_fitting_error n d y.
Proof.
move=> Uo hxy.
have UTo : U^T \is orthogonalmx by rewrite trmx_orthogonal.
have hyx (i : 'I_n) : paper_main_point x i = U^T *m paper_main_point y i.
  by rewrite hxy mulmxA orthogonalmxT // mul1mx.
rewrite /universality_fitting_error; congr (inf _).
apply/funext => z; apply/propext; split; move=> [S [r [Sp [St [r0 hr]]]]].
- have [Tp Tt Te] := fitting_error_rotation_witness r UTo hyx Sp St.
  exists (U *m S *m U^T), r; rewrite trmxK in Tp Tt Te.
  split => //; split => //; split => //.
  by rewrite -/(restriction_objective y _ _) Te.
- have [Tp Tt Te] := fitting_error_rotation_witness r Uo hxy Sp St.
  exists (U^T *m S *m U), r.
  split => //; split => //; split => //.
  by rewrite -/(restriction_objective x _ _) Te.
Qed.

Lemma measurable_gaussian_shift_error n d (m : 'cV[R]_d) :
  measurable_fun [set: paper_main_sample n d]
    (fun x => universality_fitting_error n d (sample_translate m x) : RR).
Proof.
apply: measurableT_comp; first exact: measurable_fitting_error.
exact: measurable_sample_translate.
Qed.

Lemma measurable_gaussian_shift_error_upper n d (m : 'cV[R]_d) (t : R) :
  measurable [set x : paper_main_sample n d |
    t < universality_fitting_error n d (sample_translate m x)].
Proof.
apply: measurable_set_lt.
exact: measurable_gaussian_shift_error.
Qed.

Lemma gaussian_error_rotation_probability n d (U : 'M[R]_d)
    (m v : 'cV[R]_d) (t : R) :
  U \is orthogonalmx -> U *m m = v ->
  gaussian_product_law (n*d) [set x : paper_main_sample n d |
    t < universality_fitting_error n d (sample_translate m x)] =
  gaussian_product_law (n*d) [set x : paper_main_sample n d |
    t < universality_fitting_error n d (sample_translate v x)].
Proof.
move=> Uo Um.
pose A : set (paper_main_sample n d) := [set x |
  t < universality_fitting_error n d (sample_translate v x)].
have mA : measurable A := measurable_gaussian_shift_error_upper _ _.
have UUT : (U^T)^T *m U^T = 1%:M.
  by rewrite trmxK; apply/orthogonalmxP.
rewrite -(@gaussian_flat_right_isometry_law n d d U^T A UUT mA).
congr (gaussian_product_law _ _); apply/funext => x.
have hxy (i : 'I_n) :
    paper_main_point (sample_translate v (sample_right_isometry U^T x)) i =
      U *m paper_main_point (sample_translate m x) i.
  by rewrite !sample_translate_point sample_right_rotation_point mulmxDr Um.
by rewrite /preimage /A /= (fitting_error_rotation_points Uo hxy).
Qed.

Lemma gaussian_error_axis_probability n p (m : 'cV[R]_(1+p)) (t : R) :
  gaussian_product_law (n*(1+p)) [set x : paper_main_sample n (1+p) |
    t < universality_fitting_error n (1+p) (sample_translate m x)] =
  gaussian_product_law (n*(1+p)) [set x : paper_main_sample n (1+p) |
    t < universality_fitting_error n (1+p)
      (sample_translate (gaussian_axis_shift p (frobenius m)) x)].
Proof.
pose v := gaussian_axis_shift p (frobenius m).
apply: (@gaussian_error_rotation_probability n (1+p)
  (householder (m-v)) m v t); first exact: householder_orthogonal.
apply: householder_swap.
by rewrite /v gaussian_axis_shift_dot frobenius_sqr.
Qed.

Lemma gaussian_axis_error_restriction n p (a : R)
    (x : paper_main_sample n (1+p)) : (0 < p)%N ->
  universality_fitting_error n (1+p)
      (sample_translate (gaussian_axis_shift p a) x) <=
    ((1+p)%:R / p%:R) * universality_fitting_error n p (gaussian_rest x).
Proof.
move=> p0; apply: fitting_error_restriction p0 _ => i.
by rewrite gaussian_axis_shift_point col_mxKd.
Qed.

Lemma gaussian_error_restriction_scalar (p q e eps : RR) :
  1 <= p -> 0 < eps -> `|q-e| <= eps/4%:R ->
  `|e|/p <= eps/4%:R -> ((1+p)/p)*q <= e+eps.
Proof.
move=> p1 e0 qe ep.
have p0 : 0 < p := lt_le_trans ltr01 p1.
have pn : p != 0 by rewrite gt_eqF.
have i0 : 0 <= p^-1 by rewrite invr_ge0 ltW.
have i1 : p^-1 <= 1 by rewrite invf_le1.
have r0 : 0 <= 1+p^-1 by lra.
have r2 : 1+p^-1 <= 2 by lra.
have qle : q <= e+eps/4%:R.
  have h := le_trans (ler_norm (q-e)) qe; clear -h; lra.
have hq := @ler_wpM2l RR (1+p^-1) r0 _ _ qle.
have he := @ler_wpM2r RR p^-1 i0 _ _ (ler_norm e).
have heq : (1+p)/p = 1+p^-1 by field.
rewrite heq; clear -hq he ep r2 e0; nra.
Qed.

Theorem gaussian_shift_error_upper_succ (alpha : R) (N : nat -> nat)
    (m : forall p, 'cV[R]_(1+p)) :
  0 < alpha -> universality_density_tends_to N alpha ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun p => gaussian_product_law (N p*(1+p))
    [set x : paper_main_sample (N p) (1+p) |
      universality_e_star alpha 3%:R + eps <
        universality_fitting_error (N p) (1+p) (sample_translate (m p) x)]) 0%R.
Proof.
move=> a0 hN eps e0.
pose e := universality_e_star alpha 3%:R.
have e40 : 0 < eps/4%:R by rewrite divr_gt0.
have [_ hconv] := gaussian_fitting_error_holds alpha a0.
have hc := hconv N hN _ e40.
move=> delta dl0; have [D hD] := hc delta dl0.
pose b := 4%:R * `|e|/eps.
exists (maxn 1 (maxn D (archimedean.Num.truncn b).+1)) => p.
rewrite !geq_max => /andP[p1 /andP[pD pb]].
have p0 : (0 < p)%N := p1.
have pr0 : (0 : RR) < p%:R by rewrite ltr0n.
have pr1 : (1 : RR) <= p%:R by rewrite -[1]/(1%:R) ler_nat.
have ep : `|e|/p%:R <= eps/4%:R.
  have bp : b < p%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  move: bp; rewrite /b ltr_pdivrMr // => bp.
  rewrite ler_pdivrMr //; clear -bp; nra.
rewrite gaussian_error_axis_probability.
pose E := universality_error_event (N p) p e (eps/4%:R).
pose A : set (paper_main_sample (N p) (1+p)) := [set x |
  e+eps < universality_fitting_error (N p) (1+p)
    (sample_translate (gaussian_axis_shift p (frobenius (m p))) x)].
have mE : measurable E := measurable_error_event _ _ _ _.
have mA : measurable A := measurable_gaussian_shift_error_upper _ _.
have mB : measurable ((@gaussian_rest (N p) p) @^-1` E).
  rewrite -[X in measurable X]setTI.
  exact: measurable_gaussian_rest mE.
have AB : A `<=` (@gaussian_rest (N p) p) @^-1` E.
  move=> x hx; apply: contrapT => nx.
  have qle : `|universality_fitting_error (N p) p (gaussian_rest x)-e| <= eps/4%:R.
    by rewrite leNgt; apply/negP; exact: nx.
  have hr := gaussian_axis_error_restriction (frobenius (m p)) x p0.
  rewrite natrD /= in hr.
  have h := le_trans hr (gaussian_error_restriction_scalar pr1 e0 qle ep).
  by move: hx; rewrite /A /= ltNge h.
have PB : (gaussian_product_law (N p*(1+p))
    ((@gaussian_rest (N p) p) @^-1` E) < delta%:E)%E.
  rewrite (@gaussian_rest_law (N p) p E mE).
  have h := hD p pD; move: h.
  by rewrite sube0 gee0_abs ?measure_ge0.
rewrite sube0 gee0_abs ?measure_ge0 //.
apply: le_lt_trans (le_measure (gaussian_product_law (N p*(1+p))) _ _ AB) PB.
- by rewrite inE.
- by rewrite inE.
Qed.

Theorem gaussian_shift_error_upper (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) :
  0 < alpha -> universality_density_tends_to N alpha ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => gaussian_product_law (N d*d)
    [set x : paper_main_sample (N d) d |
      universality_e_star alpha 3%:R + eps <
        universality_fitting_error (N d) d (sample_translate (m d) x)]) 0%R.
Proof.
move=> a0 hN eps e0.
have hs := @gaussian_shift_error_upper_succ alpha (fun p => N (1+p)%N)
  (fun p => m (1+p)%N) a0 (gaussian_density_successor hN) eps e0.
move=> delta dl0; have [D hD] := hs delta dl0.
exists D.+1 => d; case: d => [|p] //= pD.
exact: hD p pD.
Qed.

Lemma measurable_gaussian_shift_error_atleast n d (m : 'cV[R]_d) (t : R) :
  measurable [set x : paper_main_sample n d |
    t <= universality_fitting_error n d (sample_translate m x)].
Proof.
have := (@measurable_gaussian_shift_error n d m) measurableT _
  (measurable_itv `[(t : RR), +oo[).
rewrite setTI; congr measurable; apply/seteqP.
by split => x /=; rewrite in_itv /= andbT.
Qed.

Corollary gaussian_shift_error_atleast (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (t : R) :
  0 < alpha -> universality_density_tends_to N alpha ->
  universality_e_star alpha 3%:R < t ->
  paper_main_tends_to (fun d => gaussian_product_law (N d*d)
    [set x : paper_main_sample (N d) d |
      t <= universality_fitting_error (N d) d (sample_translate (m d) x)]) 0%R.
Proof.
move=> a0 hN et.
pose e := universality_e_star alpha 3%:R.
have eps0 : 0 < (t-e)/2 by rewrite divr_gt0 // subr_gt0.
have hc := @gaussian_shift_error_upper alpha N m a0 hN ((t-e)/2) eps0.
move=> delta dl0; have [D hD] := hc delta dl0.
exists D => d dD.
pose A : set (paper_main_sample (N d) d) := [set x |
  t <= universality_fitting_error (N d) d (sample_translate (m d) x)].
pose B : set (paper_main_sample (N d) d) := [set x |
  e+(t-e)/2 < universality_fitting_error (N d) d (sample_translate (m d) x)].
have mA : measurable A := measurable_gaussian_shift_error_atleast _ _.
have mB : measurable B := measurable_gaussian_shift_error_upper _ _.
have AB : A `<=` B.
  move=> x hx; apply: lt_le_trans hx.
  change (is_true (e+(t-e)/(2 : RR) < t)).
  change (is_true (e < t)) in et; clear -et; lra.
rewrite sube0 gee0_abs ?measure_ge0 //.
apply: le_lt_trans (le_measure (gaussian_product_law (N d*d)) _ _ AB) _.
- by rewrite inE.
- by rewrite inE.
have h := hD d dD; move: h.
by rewrite sube0 gee0_abs ?measure_ge0.
Qed.
