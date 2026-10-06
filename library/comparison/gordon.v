From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.gaussian Require Import partial_derivative.
From GaussianAnalysis.comparison Require Import gauss_smoothing slepian.

(**md**************************************************************************)
(* # Gordon's min-max inequality                                              *)
(*                                                                            *)
(* Let x have law gauss n and y have law gauss m. For                         *)
(* A : 'M[R]_(n, p.+1 * q.+1), X = vec_mx (x *m A) is a centered Gaussian     *)
(* matrix of size (p + 1) x (q + 1), whose entry X u t is the coordinate      *)
(* mxvec_index u t of x *m A; let Y = vec_mx (y *m B). Assume that each       *)
(* increment X u t - X u s within a row has a variance at most that of        *)
(* Y u t - Y u s, and that each increment X u t - X v s across two distinct   *)
(* rows has a variance at least that of Y u t - Y v s. Then                   *)
(* E[minmax X] <= E[minmax Y], where minmax Z is the smallest over the rows   *)
(* of the largest entry of the row (gordon). With one row, this is the        *)
(* Sudakov-Fernique inequality. gordon_cov states the case of equal variances *)
(* with covariances.                                                          *)
(*                                                                            *)
(* The proof applies Kahane's comparison inequality (gauss_comparison) to the *)
(* soft min-max smm b. Its Hessian has zero row and column sums               *)
(* (smm_D2_rowsum, smm_D2_colsum), so its pairing with a matrix M only        *)
(* depends on the increments M i i + M j j - 2 * M i j (pairing_zero_sums).   *)
(* The Hessian is nonpositive inside a row and nonnegative across rows, which *)
(* gives the sign (smm_hessian_sign). Since                                   *)
(* minmax Z - ln (p + 1) / b <= smm b z <= minmax Z + ln (q + 1) / b for      *)
(* Z = vec_mx z (le_smm, smm_le), letting b grow concludes.                   *)
(*                                                                            *)
(* ```                                                                        *)
(*           minmax Z == min_u max_t Z u t, for Z : 'M[R]_(p.+1, q.+1)        *)
(*         gsum b z u == \sum_t expR (b * z 0 (mxvec_index u t))              *)
(*           gtot b z == \sum_u (gsum b z u)^-1                               *)
(*            smm b z == - b^-1 * ln (gtot b z), the soft min-max of vec_mx z *)
(*           gq b z u == (gsum b z u)^-1 / gtot b z, weights of the soft min  *)
(*         gp b z u t == expR (b * z 0 (mxvec_index u t)) / gsum b z u,       *)
(*                       weights of the soft max of the row u                 *)
(*      smm_D b z u t == gq b z u * gp b z u t, the partial derivative of     *)
(*                       smm b along mxvec_index u t                          *)
(* smm_D2 b z u t v s == the partial derivative of z |-> smm_D b z u t        *)
(*                       along mxvec_index v s                                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section mxvec_index.
Context {m n : nat}.

Lemma mxvec_index_eq (i i' : 'I_m) (j j' : 'I_n) :
  (mxvec_index i j == mxvec_index i' j') = (i == i') && (j == j').
Proof.
apply/eqP/andP => [|[/eqP-> /eqP->]//].
move=> /(congr1 (fun k => enum_val (cast_ord (esym (mxvec_cast m n)) k))).
by rewrite /mxvec_index !cast_ordK !enum_rankK => -[-> ->].
Qed.

Lemma sum_mxvec_index (V : nmodType) (f : 'I_(m * n) -> V) :
  \sum_k f k = \sum_i \sum_j f (mxvec_index i j).
Proof.
rewrite pair_bigA /= (reindex (uncurry (@mxvec_index m n))) /=.
  exact: curry_mxvec_bij.
by apply: eq_bigr => -[i j] _.
Qed.

End mxvec_index.

Section minmax.
Context {R : realType} {p q : nat}.
Implicit Types Z : 'M[R]_(p.+1, q.+1).

(* The smallest of the largest entries of the rows of Z. *)
Definition minmax Z : R := - rmax (\row_u (- rmax (row u Z))).

Lemma minmax_le Z u : minmax Z <= rmax (row u Z).
Proof.
rewrite /minmax lerNl.
by have := le_rmax (\row_u (- rmax (row u Z))) u; rewrite mxE.
Qed.

Lemma le_minmax Z c : (forall u, c <= rmax (row u Z)) -> c <= minmax Z.
Proof.
by move=> h; rewrite /minmax lerNr; apply: rmax_le => u; rewrite mxE lerN2.
Qed.

Lemma rmax_leD k (z z' : 'rV[R]_k.+1) d :
  (forall j, z 0 j <= z' 0 j + d) -> rmax z <= rmax z' + d.
Proof. by move=> h; apply: rmax_le => j; rewrite (le_trans (h j))// lerD2r le_rmax. Qed.

Lemma minmax_leD Z Z' d :
  (forall u t, Z u t <= Z' u t + d) -> minmax Z <= minmax Z' + d.
Proof.
move=> h.
have h1 u : rmax (row u Z) <= rmax (row u Z') + d.
  by apply: rmax_leD => t; rewrite !mxE.
have h2 : rmax (\row_u (- rmax (row u Z'))) <=
          rmax (\row_u (- rmax (row u Z))) + d.
  by apply: rmax_leD => u; rewrite !mxE; have := h1 u; lra.
by rewrite /minmax; lra.
Qed.

Lemma minmax_lipschitz Z Z' : `|minmax Z - minmax Z'| <= `|Z - Z'|.
Proof.
have h (A B : 'M[R]_(p.+1, q.+1)) : minmax A <= minmax B + `|A - B|.
  apply: minmax_leD => u t.
  have : A u t - B u t <= `|A - B|.
    have -> : A u t - B u t = (A - B) u t by rewrite !mxE.
    exact: le_trans (ler_norm _) (mx_norm_entry_le _ _ _).
  lra.
rewrite ler_norml; have := h Z Z'; have := h Z' Z; rewrite distrC; lra.
Qed.

Lemma continuous_minmax : continuous minmax.
Proof.
move=> Z A /nbhs_ballP [d d0 dA]; apply/nbhs_ballP; exists d => // Z'.
rewrite /= -ball_normE /= => ZZ; apply: dA; rewrite -ball_normE /=.
exact: le_lt_trans (minmax_lipschitz _ _) ZZ.
Qed.

Lemma minmax_norm Z : `|minmax Z| <= `|Z|.
Proof.
have := minmax_lipschitz Z 0; rewrite !subr0.
suff -> : minmax (0 : 'M[R]_(p.+1, q.+1)) = 0 by rewrite subr0.
have r0 k : rmax (0 : 'rV[R]_k.+1) = 0.
  by have [j ->] := rmax_eq (0 : 'rV[R]_k.+1); rewrite mxE.
rewrite /minmax (_ : \row_u _ = 0) ?r0 ?oppr0//.
by apply/rowP => u; rewrite !mxE (_ : row u 0 = 0) ?r0 ?oppr0// linear0.
Qed.

Lemma norm_vec_mx_le (z : 'rV[R]_(p.+1 * q.+1)) : `|vec_mx z| <= `|z|.
Proof.
rewrite [leLHS]mx_normrE; apply: bigmax_le => //= -[u t] _.
by rewrite mxE; exact: mx_norm_entry_le.
Qed.

End minmax.

Section continuity_helpers.
Context {R : realType} {n : nat}.
Implicit Types f g : 'rV[R]_n -> R.

Local Lemma contM f g : continuous f -> continuous g ->
  continuous (fun z => f z * g z).
Proof.
move=> cf cg z; apply: (@cvgM _ _ _ _ f g); [apply: nbhs_filter|exact: cf|exact: cg].
Qed.

Local Lemma contD f g : continuous f -> continuous g ->
  continuous (fun z => f z + g z).
Proof.
move=> cf cg z; apply: (@cvgD _ _ _ _ _ f g); [apply: nbhs_filter|exact: cf|exact: cg].
Qed.

Local Lemma contB f g : continuous f -> continuous g ->
  continuous (fun z => f z - g z).
Proof.
move=> cf cg z; apply: (@cvgB _ _ _ _ _ f g); [apply: nbhs_filter|exact: cf|exact: cg].
Qed.

Local Lemma contC (c : R) : continuous (fun _ : 'rV[R]_n => c).
Proof. exact: cst_continuous. Qed.

Local Lemma contV f : (forall z, f z != 0) -> continuous f ->
  continuous (fun z => (f z)^-1).
Proof. by move=> f0 cf z; exact: (cvgV (f0 z) (cf z)). Qed.

End continuity_helpers.

Section soft_minmax.
Context {R : realType} {p q : nat}.
Variable b : R.
Local Notation N := (p.+1 * q.+1)%N.
Local Notation idx := (@mxvec_index p.+1 q.+1).
Implicit Types z : 'rV[R]_N.

(* The sum of the expR (b * z_(u, t)) over the block u. *)
Definition gsum z u : R := \sum_t expR (b * z 0 (idx u t)).

Definition gtot z : R := \sum_u (gsum z u)^-1.

(* The soft min-max of z: - b^-1 * ln (\sum_u (gsum z u)^-1). *)
Definition smm z : R := - (b^-1 * ln (gtot z)).

(* The weights of the soft minimum over the blocks, and of the soft
   maxima within each block. *)
Definition gq z u : R := (gsum z u)^-1 / gtot z.

Definition gp z u t : R := expR (b * z 0 (idx u t)) / gsum z u.

(* The first and second partial derivatives of smm. *)
Definition smm_D z u t : R := gq z u * gp z u t.

Definition smm_D2 z u t v s : R :=
  b * ((u == v)%:R * (t == s)%:R * smm_D z u t
       - 2 * (u == v)%:R * smm_D z u t * gp z v s + smm_D z u t * smm_D z v s).

Lemma gsum_gt0 z u : 0 < gsum z u.
Proof. by rewrite /gsum (bigD1 ord0)//= ltr_pwDl ?expR_gt0// sumr_ge0. Qed.

Lemma gtot_gt0 z : 0 < gtot z.
Proof.
rewrite /gtot (bigD1 ord0)//= ltr_pwDl ?invr_gt0 ?gsum_gt0// sumr_ge0// => u _.
by rewrite invr_ge0 ltW// gsum_gt0.
Qed.

Lemma gq_ge0 z u : 0 <= gq z u.
Proof.
have h1 := gsum_gt0 z u; have h2 := gtot_gt0 z.
by rewrite /gq divr_ge0 ?invr_ge0 ?(ltW h1) ?(ltW h2).
Qed.

Lemma gp_ge0 z u t : 0 <= gp z u t.
Proof. by rewrite /gp divr_ge0 ?expR_ge0// (ltW (gsum_gt0 z u)). Qed.

Lemma gq_sum z : \sum_u gq z u = 1.
Proof. by rewrite /gq -mulr_suml mulfV// gt_eqF// gtot_gt0. Qed.

Lemma gp_sum z u : \sum_t gp z u t = 1.
Proof. by rewrite /gp -mulr_suml mulfV// gt_eqF// gsum_gt0. Qed.

Lemma gq_le1 z u : gq z u <= 1.
Proof.
rewrite -(gq_sum z) (bigD1 u)//= lerDl sumr_ge0// => v _; exact: gq_ge0.
Qed.

Lemma gp_le1 z u t : gp z u t <= 1.
Proof.
rewrite -(gp_sum z u) (bigD1 t)//= lerDl sumr_ge0// => s _; exact: gp_ge0.
Qed.

Lemma smm_D_ge0 z u t : 0 <= smm_D z u t.
Proof. by rewrite /smm_D mulr_ge0 ?gq_ge0 ?gp_ge0. Qed.

Lemma smm_D_le1 z u t : smm_D z u t <= 1.
Proof.
by rewrite /smm_D -[1]mulr1 ler_pM ?gq_ge0 ?gp_ge0 ?gq_le1 ?gp_le1.
Qed.

Lemma smm_D_sum z : \sum_u \sum_t smm_D z u t = 1.
Proof.
rewrite -(gq_sum z); apply: eq_bigr => u _.
by rewrite /smm_D -mulr_sumr gp_sum mulr1.
Qed.

Lemma is_derive_gsum z u v s :
  is_derive z (delta_mx 0 (idx v s)) (gsum ^~ u)
    ((u == v)%:R * (b * expR (b * z 0 (idx v s)))).
Proof.
have h := is_derive_sum (fun t => is_derive_expR_coord b z (idx u t) (idx v s)).
have -> : gsum ^~ u = \sum_t (fun z => expR (b * z 0 (idx u t))).
  by apply/funext => w; rewrite fct_sumE.
apply: (is_derive_eq h).
under eq_bigr do rewrite mxvec_index_eq.
have [<-|nuv] := eqVneq u v.
  rewrite (bigD1 s)//= big1.
    by move=> t /negPf ->; rewrite mulr0 mul0r.
  by rewrite eqxx mulr1 mul1r addr0.
by rewrite big1 ?mul0r// => t _; rewrite mulr0 mul0r.
Qed.

Lemma is_derive_gtot z v s :
  is_derive z (delta_mx 0 (idx v s)) gtot
    (- ((gsum z v) ^- 2 * (b * expR (b * z 0 (idx v s))))).
Proof.
have hu u := is_derive_lift (is_derive_gsum z u v s)
  (is_deriveV (lt0r_neq0 (gsum_gt0 z u)) (is_derive_id (gsum z u) 1)).
have h := is_derive_sum hu.
have -> : gtot = \sum_u ((fun x : R => (id x)^-1) \o gsum ^~ u).
  by apply/funext => w; rewrite fct_sumE.
apply: (is_derive_eq h).
rewrite (bigD1 v)//= big1.
  by move=> u /negPf ->; rewrite mul0r mulr0.
by rewrite eqxx mul1r addr0 -[(- _)%:A]/(_ * 1) mulr1 mulNr.
Qed.

(* The derivative of the inverse of gsum z u along the direction (v, s). *)
Lemma is_derive_gsumV z u v s :
  is_derive z (delta_mx 0 (idx v s)) ((fun x : R => (id x)^-1) \o gsum ^~ u)
    ((- (gsum z u) ^- 2)%:A * ((u == v)%:R * (b * expR (b * z 0 (idx v s))))).
Proof.
exact: is_derive_lift (is_derive_gsum z u v s)
  (is_deriveV (lt0r_neq0 (gsum_gt0 z u)) (is_derive_id (gsum z u) 1)).
Qed.

Lemma is_derive_smm_D z u t v s :
  is_derive z (delta_mx 0 (idx v s)) ((fun z => smm_D z u t)) (smm_D2 z u t v s).
Proof.
have hT := is_derive_lift (is_derive_gtot z v s)
  (is_deriveV (lt0r_neq0 (gtot_gt0 z)) (is_derive_id (gtot z) 1)).
have he := is_derive_expR_coord b z (idx u t) (idx v s).
have h := is_deriveM (is_deriveM (is_derive_gsumV z u v s) hT)
  (is_deriveM he (is_derive_gsumV z u v s)).
have -> : (fun z => smm_D z u t) =
    ((fun x : R => (id x)^-1) \o gsum ^~ u) * ((fun x : R => (id x)^-1) \o gtot) *
    ((fun z => expR (b * z 0 (idx u t))) * ((fun x : R => (id x)^-1) \o gsum ^~ u)).
  by apply/funext => w; rewrite /smm_D /gq /gp !fctE.
apply: (is_derive_eq h).
have S0 := lt0r_neq0 (gsum_gt0 z u); have S1 := lt0r_neq0 (gsum_gt0 z v).
have T0 := lt0r_neq0 (gtot_gt0 z).
rewrite mxvec_index_eq /smm_D2 /smm_D /gq /gp !fctE /GRing.scale /=.
have [<-|nuv] := eqVneq u v; rewrite ?eqxx ?(negPf nuv) /=.
  by field.
by field.
Qed.

Lemma continuous_gsum u : continuous (gsum ^~ u).
Proof. by move=> z; apply: continuous_sum => t; exact: continuous_expR_coord. Qed.

Lemma continuous_gtot : continuous gtot.
Proof.
move=> z; apply: continuous_sum => u.
exact: (contV (fun w => lt0r_neq0 (gsum_gt0 w u)) (@continuous_gsum u)).
Qed.

Lemma continuous_gq u : continuous (gq ^~ u).
Proof.
rewrite /gq; apply: (contM (f := fun z => (gsum z u)^-1) (g := fun z => (gtot z)^-1)).
  by apply: contV => [z|]; [exact: lt0r_neq0 (gsum_gt0 z u)|exact: continuous_gsum].
by apply: contV => [z|]; [exact: lt0r_neq0 (gtot_gt0 z)|exact: continuous_gtot].
Qed.

Lemma continuous_gp u t : continuous ((fun z => gp z u t)).
Proof.
rewrite /gp; apply: (contM (f := fun z => expR (b * z 0 (idx u t)))
  (g := fun z => (gsum z u)^-1)); first exact: continuous_expR_coord.
by apply: contV => [z|]; [exact: lt0r_neq0 (gsum_gt0 z u)|exact: continuous_gsum].
Qed.

Lemma continuous_smm_D u t : continuous ((fun z => smm_D z u t)).
Proof.
rewrite /smm_D; apply: (contM (f := gq ^~ u) (g := (fun z => gp z u t))).
  exact: continuous_gq.
exact: continuous_gp.
Qed.

Lemma continuous_smm_D2 u t v s : continuous ((fun z => smm_D2 z u t v s)).
Proof.
rewrite /smm_D2; apply: (contM (f := fun _ => b)); first exact: contC.
apply: contD; last by apply: contM; exact: continuous_smm_D.
apply: contB.
  apply: (contM (f := fun _ => (u == v)%:R * (t == s)%:R)); first exact: contC.
  exact: continuous_smm_D.
apply: contM; last exact: continuous_gp.
apply: (contM (f := fun _ => 2 * (u == v)%:R)); first exact: contC.
exact: continuous_smm_D.
Qed.

Lemma smm_D_differentiable u t z :
  differentiable ((fun z => smm_D z u t) : 'rV[R]_N -> R^o) z.
Proof.
apply: (@differentiable_partials R N ((fun z => smm_D z u t))
  (fun j => 'D_(delta_mx 0 j) ((fun z => smm_D z u t)))).
  move=> j w; case/mxvec_indexP: j => v s.
  by have h := is_derive_smm_D w u t v s; rewrite derive_val.
move=> j; case/mxvec_indexP: j => v s.
have -> : 'D_(delta_mx 0 (idx v s)) ((fun z => smm_D z u t)) = (fun z => smm_D2 z u t v s).
  by apply/funext => w; have h := is_derive_smm_D w u t v s; rewrite derive_val.
exact: continuous_smm_D2.
Qed.

Local Lemma sum_delta (I : finType) (i : I) (F : I -> R) :
  \sum_j (i == j)%:R * F j = F i.
Proof.
rewrite (bigD1 i)//= eqxx mul1r big1 ?addr0// => j ji.
by rewrite eq_sym (negPf ji) mul0r.
Qed.

Lemma smm_D2_rowsum z u t : \sum_v \sum_s smm_D2 z u t v s = 0.
Proof.
rewrite /smm_D2; under eq_bigr do rewrite -mulr_sumr.
rewrite -mulr_sumr; apply/eqP; rewrite mulf_eq0; apply/orP; right; apply/eqP.
have hA v : \sum_s (u == v)%:R * (t == s)%:R * smm_D z u t =
    (u == v)%:R * smm_D z u t.
  rewrite (bigD1 t)//= eqxx mulr1 big1 ?addr0// => s st.
  by rewrite [t == s]eq_sym (negPf st) mulr0 mul0r.
have hB v : \sum_s 2 * (u == v)%:R * smm_D z u t * gp z v s =
    2 * (u == v)%:R * smm_D z u t.
  by rewrite -mulr_sumr gp_sum mulr1.
have hC v : \sum_s smm_D z u t * smm_D z v s = smm_D z u t * gq z v.
  by rewrite -mulr_sumr /smm_D -mulr_sumr gp_sum mulr1.
under eq_bigr do rewrite big_split sumrB /= hA hB hC.
rewrite big_split sumrB /= sum_delta -mulr_sumr gq_sum.
have -> : \sum_(i < p.+1) 2 * (u == i)%:R * smm_D z u t =
    \sum_(i < p.+1) (u == i)%:R * (2 * smm_D z u t).
  by apply: eq_bigr => i _; ring.
by rewrite sum_delta; ring.
Qed.

Lemma smm_D2_colsum z v s : \sum_u \sum_t smm_D2 z u t v s = 0.
Proof.
rewrite /smm_D2; under eq_bigr do rewrite -mulr_sumr.
rewrite -mulr_sumr; apply/eqP; rewrite mulf_eq0; apply/orP; right; apply/eqP.
have hA u : \sum_t (u == v)%:R * (t == s)%:R * smm_D z u t =
    (u == v)%:R * smm_D z u s.
  rewrite (bigD1 s)//= eqxx mulr1 big1 ?addr0// => t ts.
  by rewrite (negPf ts) mulr0 mul0r.
have hB u : \sum_t 2 * (u == v)%:R * smm_D z u t * gp z v s =
    2 * (u == v)%:R * gq z u * gp z v s.
  rewrite -mulr_suml -mulr_sumr /smm_D -mulr_sumr gp_sum mulr1.
  by rewrite mulrA.
have hC u : \sum_t smm_D z u t * smm_D z v s = gq z u * smm_D z v s.
  by rewrite -mulr_suml /smm_D -mulr_sumr gp_sum mulr1.
under eq_bigr do rewrite big_split sumrB /= hA hB hC.
rewrite big_split sumrB /=.
have e1 : \sum_(i < p.+1) (i == v)%:R * smm_D z i s = smm_D z v s.
  under eq_bigr do rewrite eq_sym.
  by rewrite (sum_delta v (fun i => smm_D z i s)).
have e2 : \sum_(i < p.+1) 2 * (i == v)%:R * gq z i * gp z v s =
    2 * smm_D z v s.
  have -> : \sum_(i < p.+1) 2 * (i == v)%:R * gq z i * gp z v s =
      \sum_(i < p.+1) (v == i)%:R * (2 * gq z i * gp z v s).
    by apply: eq_bigr => i _; rewrite eq_sym; ring.
  by rewrite sum_delta /smm_D mulrA.
have e3 : \sum_(i < p.+1) gq z i * smm_D z v s = smm_D z v s.
  by rewrite -mulr_suml gq_sum mul1r.
by rewrite e1 e2 e3; ring.
Qed.

Section soft_minmax_b0.
Hypothesis b0 : 0 < b.

Lemma smm_lse z : smm z = - lse b (\row_u (- lse b (row u (vec_mx z)))).
Proof.
rewrite /smm /lse; congr (- (_ * ln _)).
rewrite /gtot; apply: eq_bigr => u _; rewrite mxE.
have hS : 0 < \sum_t expR (b * row u (vec_mx z) 0 t).
  by rewrite (bigD1 ord0)//= ltr_pwDl ?expR_gt0// sumr_ge0.
rewrite mulrN mulrA mulfV ?gt_eqF// mul1r expRN lnK ?posrE//.
by congr (_^-1); apply: eq_bigr => t _; rewrite !mxE.
Qed.

Lemma smm_le z : smm z <= minmax (vec_mx z) + ln q.+1%:R / b.
Proof.
set Z := vec_mx z; rewrite smm_lse -/Z /minmax.
set w := \row_u (- lse b (row u Z)); set w' := \row_u (- rmax (row u Z)).
have h1 : rmax w <= lse b w := rmax_le_lse b0 w.
have h2 : rmax w' <= rmax w + ln q.+1%:R / b.
  apply: rmax_leD => u; rewrite !mxE.
  by have := lse_le_rmax b0 (row u Z); lra.
lra.
Qed.

Lemma le_smm z : minmax (vec_mx z) - ln p.+1%:R / b <= smm z.
Proof.
set Z := vec_mx z; rewrite smm_lse -/Z /minmax.
set w := \row_u (- lse b (row u Z)); set w' := \row_u (- rmax (row u Z)).
have h1 : lse b w <= rmax w + ln p.+1%:R / b := lse_le_rmax b0 w.
have h2 : rmax w <= rmax w' + 0.
  apply: rmax_leD => u; rewrite !mxE addr0 lerN2; exact: rmax_le_lse.
lra.
Qed.

Lemma is_derive_smm z v s :
  is_derive z (delta_mx 0 (idx v s)) smm (smm_D z v s).
Proof.
have h := is_derive_lift (is_derive_gtot z v s)
  (is_deriveN (is_deriveZ b^-1 (is_derive1_ln (gtot_gt0 z)))).
apply: (is_derive_eq h).
have b1 := lt0r_neq0 b0; have S0 := lt0r_neq0 (gsum_gt0 z v).
have T0 := lt0r_neq0 (gtot_gt0 z).
rewrite /smm_D /gq /gp /GRing.scale /=.
by field.
Qed.

Lemma smm_DE v s :
  'D_(delta_mx 0 (idx v s)) smm = (fun z => smm_D z v s) :> ('rV[R]_N -> R).
Proof. by apply/funext => z; have h := is_derive_smm z v s; rewrite derive_val. Qed.

Lemma smm_D2E u t v s :
  'D_(delta_mx 0 (idx v s)) ('D_(delta_mx 0 (idx u t)) smm) =
  (fun z => smm_D2 z u t v s) :> ('rV[R]_N -> R).
Proof.
rewrite smm_DE; apply/funext => z.
by have h := is_derive_smm_D z u t v s; rewrite derive_val.
Qed.

Lemma smm_differentiable z : differentiable (smm : 'rV[R]_N -> R^o) z.
Proof.
apply: (@differentiable_partials R N smm (fun j => 'D_(delta_mx 0 j) smm)).
  move=> j w; case/mxvec_indexP: j => v s.
  by have h := is_derive_smm w v s; rewrite derive_val.
by move=> j; case/mxvec_indexP: j => v s; rewrite smm_DE; exact: continuous_smm_D.
Qed.

End soft_minmax_b0.

End soft_minmax.

Section pairing.
Context {R : realType}.

(* If H has zero row and column sums, its pairing with M only depends on
   the increments M i i + M j j - 2 * M i j. *)
Lemma pairing_zero_sums (n : nat) (M H : 'I_n -> 'I_n -> R) :
  (forall i, \sum_j H i j = 0) -> (forall j, \sum_i H i j = 0) ->
  \sum_i \sum_j M i j * H i j =
  - 2^-1 * \sum_i \sum_j H i j * (M i i + M j j - 2 * M i j).
Proof.
move=> hr hc.
have e1 : \sum_i \sum_j H i j * M i i = 0.
  by rewrite big1// => i _; rewrite -mulr_suml hr mul0r.
have e2 : \sum_i \sum_j H i j * M j j = 0.
  by rewrite exchange_big big1// => j _; rewrite -mulr_suml hc mul0r.
have e3 : \sum_i \sum_j H i j * (M i i + M j j - 2 * M i j) =
    \sum_i \sum_j H i j * M i i + \sum_i \sum_j H i j * M j j
    - 2 * \sum_i \sum_j M i j * H i j.
  rewrite mulr_sumr -big_split -sumrB; apply: eq_bigr => i _.
  rewrite /= mulr_sumr -big_split -sumrB /=; apply: eq_bigr => j _.
  by rewrite /=; ring.
by rewrite e3 e1 e2; field.
Qed.

End pairing.

Section smm_hessian.
Context {R : realType} {p q : nat}.
Variable b : R.
Hypothesis b0 : 0 < b.
Local Notation N := (p.+1 * q.+1)%N.
Local Notation idx := (@mxvec_index p.+1 q.+1).

(* The pairing of the Hessian of smm b with a matrix that vanishes on the
   diagonal, is nonpositive inside the blocks and nonnegative across them,
   is nonnegative. *)
Lemma smm_hessian_sign z (Dl : 'I_N -> 'I_N -> R) :
  (forall j, Dl j j = 0) ->
  (forall u t s, Dl (idx u t) (idx u s) <= 0) ->
  (forall u v t s, u != v -> 0 <= Dl (idx u t) (idx v s)) ->
  0 <= \sum_j \sum_l 'D_(delta_mx 0 l) ('D_(delta_mx 0 j) (smm b)) z * Dl j l.
Proof.
move=> D0 Dsame Dcross.
apply: sumr_ge0 => j _; apply: sumr_ge0 => l _.
case/mxvec_indexP: j => u t; case/mxvec_indexP: l => v s.
rewrite (congr1 (fun f => f z) (smm_D2E b0 u t v s)) /smm_D2.
have Dut := smm_D_ge0 b z u t; have Dvs := smm_D_ge0 b z v s.
have [<-|nuv] := eqVneq u v.
  have [<-|nts] := eqVneq t s; first by rewrite D0 mulr0.
  apply: mulr_le0 (Dsame u t s).
  rewrite /= mulr1n mulr0n mulr0 mul0r sub0r mulr1.
  have g0 := gp_ge0 b z u s; have q1 := gq_le1 b z u.
  have Dus : smm_D b z u s <= gp b z u s.
    by rewrite /smm_D -[leRHS]mul1r ler_wpM2r.
  by rewrite pmulr_rle0//; nra.
apply: mulr_ge0 (Dcross u v t s nuv).
apply: mulr_ge0; first exact: ltW.
by rewrite /= !mulr0n !mulr0 !mul0r; nra.
Qed.

End smm_hessian.

Section gordon.
Context {R : realType}.

Lemma continuous_vec_mx p q : continuous (@vec_mx R p q).
Proof.
apply: continuous_mxP => u t; under eq_fun do rewrite mxE.
exact: coord_continuous.
Qed.

Lemma integrable_gauss_minmax n p q (A : 'M[R]_(n, p.+1 * q.+1)) :
  (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun x => minmax (vec_mx (x *m A)))).
Proof.
have cA : continuous (fun x : 'rV[R]_n => minmax (vec_mx (x *m A))).
  move=> x; apply: (continuous_comp
    (f := fun y : 'rV[R]_n => vec_mx (y *m A)) (g := minmax)).
    apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m A) (g := vec_mx)).
      exact: continuous_mulmxr.
    exact: continuous_vec_mx.
  exact: continuous_minmax.
apply: (integrable_gauss_poly (continuous_measurable_mx cA)
  (C := n%:R * `|A| + 1) (k := 1)) => x.
rewrite (le_trans (minmax_norm _))// (le_trans (norm_vec_mx_le _))//.
rewrite (le_trans (mx_norm_mulmx_le _ _))// expr1.
have h0 := normr_ge0 x; have h1 := normr_ge0 A; have h2 : (0 : R) <= n%:R by [].
nra.
Qed.

Lemma smm_norm p q (b : R) (z : 'rV[R]_(p.+1 * q.+1)) : 0 < b ->
  `|smm b z| <= `|z| + (ln p.+1%:R + ln q.+1%:R) / b.
Proof.
move=> b0; have h1 := smm_le b0 z; have h2 := le_smm b0 z.
have h3 := minmax_norm (vec_mx z); have h4 := norm_vec_mx_le z.
have cp : 0 <= ln p.+1%:R / b by rewrite divr_ge0 ?ln_ge0 ?ler1n// ltW.
have cq : 0 <= ln q.+1%:R / b by rewrite divr_ge0 ?ln_ge0 ?ler1n// ltW.
move: h3; rewrite mulrDl !ler_norml => /andP[h3 h3'].
by apply/andP; split; lra.
Qed.

Lemma integrable_gauss_smm n p q (b : R) (A : 'M[R]_(n, p.+1 * q.+1)) :
  0 < b -> (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun x => smm b (x *m A))).
Proof.
move=> b0.
have cA : continuous (fun x : 'rV[R]_n => smm b (x *m A)).
  move=> x; apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m A) (g := smm b)).
    exact: continuous_mulmxr.
  exact: differentiable_continuous (smm_differentiable b0 _).
have c0 : 0 <= (ln p.+1%:R + ln q.+1%:R) / b.
  by rewrite divr_ge0 ?addr_ge0 ?ln_ge0 ?ler1n// ltW.
apply: (integrable_gauss_poly (continuous_measurable_mx cA)
  (C := n%:R * `|A| + 1 + (ln p.+1%:R + ln q.+1%:R) / b) (k := 1)) => x.
rewrite (le_trans (smm_norm _ b0))// expr1.
have := mx_norm_mulmx_le x A.
have h0 := normr_ge0 x; have h1 := normr_ge0 A; have h2 : (0 : R) <= n%:R by [].
nra.
Qed.

(* Gordon's inequality for expected min-max: the rows u of vec_mx (x *m A)
   and vec_mx (y *m B) are the blocks. *)
Theorem gordon n m p q (A : 'M[R]_(n, p.+1 * q.+1)) (B : 'M[R]_(m, p.+1 * q.+1)) :
  (forall u t s, incr_var A (mxvec_index u t) (mxvec_index u s) <=
                 incr_var B (mxvec_index u t) (mxvec_index u s)) ->
  (forall u v t s, u != v ->
     incr_var B (mxvec_index u t) (mxvec_index v s) <=
     incr_var A (mxvec_index u t) (mxvec_index v s)) ->
  (\int[gauss n]_x (minmax (vec_mx (x *m A)))%:E <=
   \int[gauss m]_y (minmax (vec_mx (y *m B)))%:E)%E.
Proof.
move=> Hsame Hcross.
have iA := integrable_gauss_minmax A; have iB := integrable_gauss_minmax B.
rewrite -(fineK (integrable_fin_num measurableT iA)).
rewrite -(fineK (integrable_fin_num measurableT iB)) lee_fin.
apply/ler_addgt0Pr => e e0.
pose cp : R := ln p.+1%:R; pose cq : R := ln q.+1%:R; pose c := cp + cq.
have cp0 : 0 <= cp by rewrite /cp ln_ge0// ler1n.
have cq0 : 0 <= cq by rewrite /cq ln_ge0// ler1n.
have c0 : 0 <= c by rewrite addr_ge0.
pose b := (c + 1) / e.
have b0 : 0 < b by rewrite divr_gt0// ltr_wpDl.
have cb : c / b <= e.
  rewrite /b invf_div mulrA ler_pdivrMr ?ltr_wpDl// mulrC ler_wpM2l ?ltW//.
  by rewrite ltrDl.
pose C : R := 1 + c / b + 4 * b.
have cb0 : 0 <= c / b by rewrite divr_ge0// ltW.
have C1 : 1 <= C by rewrite /C; have := ltW b0; lra.
(* Compare the soft min-max of x *m A and y *m B. *)
have h2 : (\int[gauss n]_x (smm b (x *m A))%:E <=
           \int[gauss m]_y (smm b (y *m B))%:E)%E.
  apply: (@gauss_comparison R (p.+1 * q.+1) (smm b) _ _ _ C 1).
  - by move=> z; exact: smm_differentiable.
  - move=> j z; case/mxvec_indexP: j => u t.
    by rewrite smm_DE//; exact: smm_D_differentiable.
  - move=> j l; case/mxvec_indexP: j => u t; case/mxvec_indexP: l => v s.
    by rewrite smm_D2E//; exact: continuous_smm_D2.
  - move=> z; rewrite (le_trans (smm_norm _ b0))// expr1.
    by have := normr_ge0 z; have := ltW b0; rewrite /C -/cp -/cq -/c; nra.
  - move=> j z; case/mxvec_indexP: j => u t.
    rewrite (congr1 (fun f => f z) (smm_DE b0 u t)) ger0_norm ?smm_D_ge0//.
    rewrite (le_trans (smm_D_le1 _ _ _ _))// -[1]mulr1 ler_pM ?ler01//.
    by rewrite mul1r lerDl expr1.
  - move=> j l z; case/mxvec_indexP: j => u t; case/mxvec_indexP: l => v s.
    rewrite (congr1 (fun f => f z) (smm_D2E b0 u t v s)) /smm_D2.
    rewrite normrM (ger0_norm (ltW b0)).
    have d0 := smm_D_ge0 b z u t; have d1 := smm_D_le1 b z u t.
    have d0' := smm_D_ge0 b z v s; have d1' := smm_D_le1 b z v s.
    have g0 := gp_ge0 b z v s; have g1 := gp_le1 b z v s.
    have e1 : `|(u == v)%:R * (t == s)%:R * smm_D b z u t -
        2 * (u == v)%:R * smm_D b z u t * gp b z v s +
        smm_D b z u t * smm_D b z v s| <= 4.
      rewrite ler_norml; case: (u == v); case: (t == s) => /=;
        by apply/andP; split; nra.
    by have := normr_ge0 z; have := ltW b0; rewrite /C -/cp -/cq -/c; nra.
  - move=> z.
    pose H j l := 'D_(delta_mx 0 l) ('D_(delta_mx 0 j) (smm b)) z.
    have hr j : \sum_l H j l = 0.
      case/mxvec_indexP: j => u t; rewrite sum_mxvec_index.
      transitivity (\sum_v \sum_s smm_D2 b z u t v s).
        apply: eq_bigr => v _; apply: eq_bigr => s _.
        by rewrite /H (congr1 (fun f => f z) (smm_D2E b0 u t v s)).
      exact: smm_D2_rowsum.
    have hc l : \sum_j H j l = 0.
      case/mxvec_indexP: l => v s; rewrite sum_mxvec_index.
      transitivity (\sum_u \sum_t smm_D2 b z u t v s).
        apply: eq_bigr => u _; apply: eq_bigr => t _.
        by rewrite /H (congr1 (fun f => f z) (smm_D2E b0 u t v s)).
      exact: smm_D2_colsum.
    have := pairing_zero_sums (fun j l => (A^T *m A - B^T *m B) j l) hr hc.
    rewrite /H => ->.
    have hs := smm_hessian_sign b0 z
      (Dl := fun j l => incr_var A j l - incr_var B j l).
    have -> : \sum_i \sum_j 'D_(delta_mx 0 j) ('D_(delta_mx 0 i) (smm b)) z *
        ((A^T *m A - B^T *m B) i i + (A^T *m A - B^T *m B) j j -
         2 * (A^T *m A - B^T *m B) i j) =
      \sum_i \sum_j 'D_(delta_mx 0 j) ('D_(delta_mx 0 i) (smm b)) z *
        (incr_var A i j - incr_var B i j).
      apply: eq_bigr => i _; apply: eq_bigr => j _.
      by rewrite /incr_var !mxE; congr (_ * _); ring.
    rewrite mulNr oppr_le0 mulr_ge0 ?invr_ge0//.
    apply: hs.
    + by move=> j; rewrite /incr_var; ring.
    + by move=> u t s; rewrite subr_le0.
    + by move=> u v t s uv; rewrite subr_ge0 Hcross.
(* minmax - cp / b <= smm b <= minmax + cq / b, and c / b <= e. *)
have iLA := integrable_gauss_smm A b0; have iLB := integrable_gauss_smm B b0.
have iCA : (gauss n).-integrable setT (EFin \o cst (cp / b)).
  exact: finite_measure_integrable_cst.
have iCB : (gauss m).-integrable setT (EFin \o cst (cq / b)).
  exact: finite_measure_integrable_cst.
have iDA : (gauss n).-integrable setT
    (EFin \o (fun x => smm b (x *m A) + cp / b)).
  rewrite (_ : EFin \o _ =
    (EFin \o (fun x => smm b (x *m A))) \+ (EFin \o cst (cp / b)))//.
  exact: integrableD.
have iDB : (gauss m).-integrable setT
    (EFin \o (fun y => minmax (vec_mx (y *m B)) + cq / b)).
  rewrite (_ : EFin \o _ =
    (EFin \o (fun y => minmax (vec_mx (y *m B)))) \+ (EFin \o cst (cq / b)))//.
  exact: integrableD.
have h1 : \int[gauss n]_x minmax (vec_mx (x *m A)) <=
          \int[gauss n]_x (smm b (x *m A) + cp / b).
  by apply: le_Rintegral => // x _; have := le_smm b0 (x *m A); rewrite -/cp; lra.
have h2' : \int[gauss n]_x smm b (x *m A) <= \int[gauss m]_y smm b (y *m B).
  apply: fine_le; [exact: integrable_fin_num|exact: integrable_fin_num|].
  exact: h2.
have h3 : \int[gauss m]_y smm b (y *m B) <=
          \int[gauss m]_y (minmax (vec_mx (y *m B)) + cq / b).
  by apply: le_Rintegral => // y _; have := smm_le b0 (y *m B); rewrite -/cq.
rewrite RintegralD// Rintegral_cst// [X in fine X]probability_setT mulr1 in h1.
rewrite RintegralD// Rintegral_cst// [X in fine X]probability_setT mulr1 in h3.
have : cp / b + cq / b <= e by rewrite -mulrDl.
move: h1 h2' h3.
set I1 := \int[gauss n]_x minmax (vec_mx (x *m A)).
set I4 := \int[gauss m]_x minmax (vec_mx (x *m B)).
move=> h1 h2' h3 hc.
apply: (le_trans h1); apply: (le_trans (lerD h2' (lexx (cp / b)))).
apply: (le_trans (lerD h3 (lexx (cp / b)))).
by rewrite -addrA lerD2l addrC.
Qed.

(* Gordon's inequality with equal variances: larger covariances inside the
   rows and smaller covariances across rows give a smaller expected
   min-max. *)
Corollary gordon_cov n m p q (A : 'M[R]_(n, p.+1 * q.+1))
    (B : 'M[R]_(m, p.+1 * q.+1)) :
  (forall j, (A^T *m A) j j = (B^T *m B) j j) ->
  (forall u t s, (B^T *m B) (mxvec_index u t) (mxvec_index u s) <=
                 (A^T *m A) (mxvec_index u t) (mxvec_index u s)) ->
  (forall u v t s, u != v ->
     (A^T *m A) (mxvec_index u t) (mxvec_index v s) <=
     (B^T *m B) (mxvec_index u t) (mxvec_index v s)) ->
  (\int[gauss n]_x (minmax (vec_mx (x *m A)))%:E <=
   \int[gauss m]_y (minmax (vec_mx (y *m B)))%:E)%E.
Proof.
move=> var_eq same cross; apply: gordon.
  by move=> u t s; rewrite /incr_var !var_eq; have := same u t s; lra.
by move=> u v t s uv; rewrite /incr_var !var_eq; have := cross u v t s uv; lra.
Qed.

End gordon.
