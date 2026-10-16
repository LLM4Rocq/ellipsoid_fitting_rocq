From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals set_interval.
From mathcomp Require Import topology normedtype derive measure lebesgue_stieltjes_measure measurable_realfun.
From mathcomp Require Import realfun measurable_fun_approximation.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.convex Require Import moreau.
From GaussianAnalysis.gaussian Require Import measurable_matrix.

(**md**************************************************************************)
(* # The closest point in a varying linear image                              *)
(*                                                                            *)
(* For a compact nonempty convex set K of row vectors, image_projection K A    *)
(* is the unique point of {x A | x in K} with minimum Euclidean norm.          *)
(* Its preimage in K need not be unique. The squared distance between the     *)
(* image points for A and B is bounded by                                    *)
(* r^2 (opnorm A + opnorm B) opnorm (A - B), when |x|_F <= r on K.             *)
(* This gives continuity and Borel measurability without selecting a         *)
(* minimizing preimage.                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* A quantitative modulus gives continuity in the matrix topology. *)
Section image_projection_modulus.
Context {R : realType} {m n p : nat}.

Lemma compact_frobenius_bound (K : set 'M[R]_(m, n)) :
  compact K -> exists r : R, forall x, K x -> frobenius x <= r.
Proof.
move=> /compact_bounded [b [br hb]].
exists (Num.sqrt (m * n)%:R * (b + 1)) => x Kx.
apply: le_trans (frobenius_le_mx_norm x) _.
apply: ler_wpM2l; first exact: sqrtr_ge0.
change (`|x| <= b + 1).
apply: hb => //.
by rewrite ltrDl.
Qed.

Variable F : 'M[R]_(m,n) -> 'rV[R]_p.
Variable r : R.
Hypothesis modulus : forall A B, frobenius (F A - F B) ^+ 2 <=
  r ^+ 2 * (opnorm A + opnorm B) * opnorm (A - B).
Lemma squared_opnorm_modulus_continuous : continuous F.
Proof.
move=> A; apply/(cvgrPdist_lt (F := nbhs A)) => e e0.
pose c : R := Num.sqrt (m*n)%:R + 1.
have c0 : 0 < c by rewrite /c ltr_wpDl // sqrtr_ge0.
have cb (B : 'M[R]_(m,n)) : opnorm B <= c * `|B|.
  apply: le_trans (opnorm_le_frobenius B) _.
  apply: le_trans (frobenius_le_mx_norm B) _.
  rewrite /c; apply: ler_wpM2r.
    change (0 <= `|B|); exact: normr_ge0.
  by rewrite lerDl.
pose k := r ^+ 2 * (2 * opnorm A + 1) * c + 1.
have opA0 := opnorm_ge0 A.
have r20 : 0 <= r ^+ 2 := sqr_ge0 r.
have k0 : 0 < k.
  rewrite /k ltr_wpDl //.
  apply: mulr_ge0; last exact: ltW c0.
  apply: mulr_ge0 => //.
  by rewrite addr_ge0 // mulr_ge0.
have d0 : 0 < Num.min c^-1 (e ^+ 2 / k).
  by rewrite lt_min invr_gt0 c0 divr_gt0 // exprn_gt0.
have := @cvgr_dist_lt _ _ _ (nbhs A) (nbhs_filter A) id A cvg_id _ d0.
apply: filterS => B /= hB.
move: hB; rewrite lt_min => /andP[hB1 hB2].
have hsmall : c * `|A-B| < 1.
  by move: hB1; rewrite -[c^-1]mul1r ltr_pdivlMr // mulrC.
have hclose : k * `|A-B| < e ^+ 2.
  by move: hB2; rewrite ltr_pdivlMr // mulrC.
have opB : opnorm B <= opnorm A + 1.
  have -> : B = A + -(A-B) by rewrite opprB addrC subrK.
  have := opnormD A (-(A-B)).
  rewrite opnormN; have := cb (A-B); lra.
have gap : frobenius (F A-F B) ^+ 2 < e ^+ 2.
  have hmod := modulus A B.
  have hdiff := cb (A-B).
  have od0 := opnorm_ge0 (A-B).
  have norm0 := normr_ge0 (A-B).
  have hmain : r ^+ 2 * (opnorm A + opnorm B) * opnorm (A-B) <=
      r ^+ 2 * (2 * opnorm A + 1) * (c * `|A-B|).
    apply: ler_pM.
    - by rewrite mulr_ge0 // addr_ge0 // opnorm_ge0.
    - exact: od0.
    - apply: ler_wpM2l => //; lra.
    - exact: hdiff.
  have := le_trans hmod hmain.
  rewrite /k in hclose.
  nra.
have normF : `|F A-F B| <= frobenius (F A-F B).
  exact: mx_norm_le_frobenius.
have f0 := frobenius_ge0 (F A-F B).
apply: le_lt_trans normF _.
nra.
Qed.
Lemma squared_opnorm_modulus_measurable : measurable_fun [set: 'M[R]_(m,n)] F.
Proof.
apply/measurable_fun_mxP => i j.
apply: continuous_measurable_mx => A.
apply: (@continuous_comp _ _ _ F (fun x : 'rV[R]_p => x i j)).
  exact: squared_opnorm_modulus_continuous.
exact: coord_continuous.
Qed.
End image_projection_modulus.

Section measurable_normalization.
Context {R : realType} {d} {T : measurableType d} {m n : nat}.
(* Same generic argument as extension/Paired/Conditional.v:measurable_inv,
   kept local here so this library result does not depend on the application. *)
Let normalization_inverse_measurable : measurable_fun [set: R] (fun x : R => x^-1).
Proof.
have e : [set: R] = [set 0] `|` ~` [set 0].
  apply/seteqP; split => // x _.
  have [->|x0] := eqVneq x 0; first by left.
  by right => /= x00; rewrite x00 eqxx in x0.
rewrite e; apply/measurable_funU.
- exact: measurable_set1.
- exact: measurableC (measurable_set1 _).
split; first exact: measurable_fun_set1.
apply: open_continuous_measurable_fun.
  apply: closed_openC; apply: accessible_closed_set1.
  by apply: hausdorff_accessible; exact: Rhausdorff.
by move=> x; rewrite inE /= => /eqP x0; exact: inv_continuous.
Qed.
Lemma measurable_frobenius_fun (F : T -> 'M[R]_(m,n)) :
  measurable_fun [set: T] F -> measurable_fun [set: T] (fun x => frobenius (F x)).
Proof.
move=> mF; rewrite /frobenius.
apply: measurableT_comp; first exact: continuous_measurable_fun (@sqrt_continuous R).
rewrite /mxdot.
apply: measurable_sum => i; apply: measurable_sum => j.
apply: measurable_funM; exact: measurableT_comp (measurable_mxentry i j) mF.
Qed.
Lemma measurable_normalize_frobenius (F : T -> 'M[R]_(m,n)) :
  measurable_fun [set: T] F ->
  measurable_fun [set: T] (fun x => (frobenius (F x))^-1 *: F x).
Proof.
move=> mF; apply: measurable_scalemx => //.
exact: measurableT_comp normalization_inverse_measurable (measurable_frobenius_fun mF).
Qed.
End measurable_normalization.

Section image_projection.
Context {R : realType} {m n : nat}.
Implicit Types K : set 'rV[R]_m.
Implicit Types A B : 'M[R]_(m, n).

Definition linear_image K A : set 'rV[R]_n := (fun x => x *m A) @` K.
Definition image_projection K A : 'rV[R]_n := proj (linear_image K A) 0.

Lemma linear_image_compact K A : compact K -> compact (linear_image K A).
Proof.
exact: continuous_compact (continuous_subspaceT (@continuous_mulmxr R 1 m n A)).
Qed.

Lemma linear_image_nonempty K A : K !=set0 -> linear_image K A !=set0.
Proof. by move=> [x Kx]; exists (x *m A); exists x. Qed.

Lemma linear_image_convex K A :
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  forall x y (t : R), linear_image K A x -> linear_image K A y ->
    0 <= t <= 1 -> linear_image K A (x + t *: (y - x)).
Proof.
move=> Kcvx _ _ t [x Kx <-] [y Ky <-] ht.
exists (x + t *: (y - x)); first exact: Kcvx Kx Ky ht.
by rewrite mulmxDl -scalemxAl mulmxBl.
Qed.

Lemma image_projectionP K A :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  linear_image K A (image_projection K A) /\
  forall y, K y ->
    mxdot (image_projection K A) (y *m A - image_projection K A) >= 0.
Proof.
move=> Kcp K0 Kcvx.
have Ic : closed (linear_image K A).
  apply: compact_closed; first exact: norm_hausdorff.
  exact: linear_image_compact Kcp.
have [hmem hvar] := projP Ic (linear_image_nonempty A K0)
  (linear_image_convex (A:=A) Kcvx) 0.
split=> // y Ky.
have hy : linear_image K A (y *m A) by exists y.
have := hvar _ hy.
by rewrite sub0r mxdotNl oppr_le0.
Qed.

Lemma image_projection_min K A :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  forall y, K y -> frobenius (image_projection K A) <= frobenius (y *m A).
Proof.
move=> Kcp K0 Kcvx y Ky.
have [hp hv] := image_projectionP A Kcp K0 Kcvx.
have hv' : forall u, linear_image K A u ->
    mxdot (0 - image_projection K A) (u - image_projection K A) <= 0.
  move=> _ [u Ku <-]; rewrite sub0r mxdotNl oppr_le0.
  exact: hv u Ku.
have hm := (proj_variational (linear_image_convex (A:=A) Kcvx) 0 hp).2 hv'.
have hy : linear_image K A (y *m A) by exists y.
have := hm _ hy.
by rewrite !sub0r !mxdotNl !mxdotNr !opprK -!frobenius_sqr
  ler_sqr ?nnegrE ?frobenius_ge0.
Qed.

Lemma image_projection_unique K A (p : 'rV[R]_n) :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  linear_image K A p ->
  (forall y, K y -> frobenius p <= frobenius (y *m A)) ->
  p = image_projection K A.
Proof.
move=> Kcp K0 Kcvx hp hmin.
have [hq hv] := image_projectionP A Kcp K0 Kcvx.
apply: (proj_unique (z:=0) hp hq).
  apply: (proj_variational (linear_image_convex (A:=A) Kcvx) 0 hp).1.
  move=> _ [y Ky <-].
  rewrite !sub0r !mxdotNl !mxdotNr !opprK -!frobenius_sqr
    ler_sqr ?nnegrE ?frobenius_ge0 //.
  exact: hmin y Ky.
move=> _ [y Ky <-]; rewrite sub0r mxdotNl oppr_le0.
exact: hv y Ky.
Qed.

(* The operator norm acts on columns. Transposition gives the same bound
   for the right action on rows, with no dimension-dependent constant. *)
Lemma image_projection_row_bound (x : 'rV[R]_m) A :
  frobenius (x *m A) <= opnorm A * frobenius x.
Proof.
have := frobenius_mulmx_opnorm A^T x^T.
by rewrite -trmx_mul !frobenius_trmx opnorm_trmx.
Qed.

Lemma image_projection_bound K A B (r : R) :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  (forall x, K x -> frobenius x <= r) ->
  frobenius (image_projection K A - image_projection K B) ^+ 2 <=
    r ^+ 2 * (opnorm A + opnorm B) * opnorm (A - B).
Proof.
move=> Kcp K0 Kcvx Kr.
have [[u Ku eu] hA] := image_projectionP A Kcp K0 Kcvx.
have [[v Kv ev] hB] := image_projectionP B Kcp K0 Kcvx.
set p := image_projection K A in eu hA *.
set q := image_projection K B in ev hB *.
have r0 : 0 <= r := le_trans (frobenius_ge0 u) (Kr u Ku).
have key : mxdot (p - q) (p - q) <=
    mxdot p (v *m (A - B)) + mxdot q (u *m (B - A)).
  have ha := hA v Kv; have hb := hB u Ku.
  rewrite !mxdotBr in ha hb.
  rewrite !mulmxBr !mxdotBl !mxdotBr eu ev (mxdotC q p).
  lra.
have rb x (M : 'M[R]_(m,n)) : K x ->
    frobenius (x *m M) <= opnorm M * r.
  move=> Kx; apply: le_trans (image_projection_row_bound x M) _.
  by apply: ler_wpM2l (Kr x Kx); exact: opnorm_ge0.
have pbd : frobenius p <= opnorm A * r by rewrite -eu; exact: rb u A Ku.
have qbd : frobenius q <= opnorm B * r by rewrite -ev; exact: rb v B Kv.
have eAbd := rb v (A - B) Kv.
have eBbd := rb u (B - A) Ku.
have opBA : opnorm (B - A) = opnorm (A - B).
  by rewrite -opnormN opprB.
rewrite opBA in eBbd.
have termA : mxdot p (v *m (A - B)) <=
    (opnorm A * r) * (opnorm (A - B) * r).
  apply: le_trans (ler_mxdot _ _) _.
  exact: ler_pM (frobenius_ge0 _) (frobenius_ge0 _) pbd eAbd.
have termB : mxdot q (u *m (B - A)) <=
    (opnorm B * r) * (opnorm (A - B) * r).
  apply: le_trans (ler_mxdot _ _) _.
  exact: ler_pM (frobenius_ge0 _) (frobenius_ge0 _) qbd eBbd.
rewrite frobenius_sqr; apply: le_trans key _.
apply: le_trans (lerD termA termB) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

Lemma image_projection_continuous K :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  continuous (image_projection K).
Proof.
move=> Kcp K0 Kcvx.
have [r Kr] := compact_frobenius_bound Kcp.
apply: (@squared_opnorm_modulus_continuous R m n n (image_projection K) r).
move=> A B; exact (image_projection_bound A B Kcp K0 Kcvx Kr).
Qed.

Lemma image_projection_measurable K :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  measurable_fun [set: 'M[R]_(m, n)] (image_projection K).
Proof.
move=> Kcp K0 Kcvx.
apply/measurable_fun_mxP => i j.
apply: continuous_measurable_mx => A.
apply: (@continuous_comp _ _ _ (image_projection K)
  (fun x : 'rV[R]_n => x i j)).
  exact (image_projection_continuous (x:=A) Kcp K0 Kcvx).
exact: coord_continuous.
Qed.

(* Examples: a singleton, and a segment collapsed by the zero map. *)
Lemma proj_singleton (p z : 'rV[R]_n) : proj [set p] z = p.
Proof.
apply: proj_eq.
- apply: compact_closed; [exact: norm_hausdorff | exact: compact_set1].
- by exists p.
- by move=> x y t -> -> _; rewrite subrr scaler0 addr0.
- done.
- by move=> y ->; rewrite subrr mxdot0r.
Qed.
Lemma linear_image_singleton (x : 'rV[R]_m) A : linear_image [set x] A = [set x *m A].
Proof.
apply/seteqP; split=> y.
- by move=> [z -> <-].
- by move=> ->; exists x.
Qed.
Lemma linear_image_zero K : K !=set0 -> linear_image K 0 = [set (0 : 'rV[R]_n)].
Proof.
move=> [x Kx]; apply/seteqP; split=> y.
- by move=> [z Kz <-]; rewrite mulmx0.
- by move=> ->; exists x => //; rewrite mulmx0.
Qed.
Lemma image_projection_singleton (x : 'rV[R]_m) A : image_projection [set x] A = x *m A.
Proof. by rewrite /image_projection linear_image_singleton proj_singleton. Qed.
Lemma image_projection_zero K : K !=set0 -> image_projection K 0 = 0.
Proof. by move=> K0; rewrite /image_projection (linear_image_zero K0) proj_singleton. Qed.
Definition radial_segment (v : 'rV[R]_m) :=
  (fun t : R => t *: v) @` `[0,1].
Lemma radial_segment_compact v : compact (radial_segment v).
Proof.
have cv : continuous (fun t : R => t *: v).
  move=> t; exact: cvgZ cvg_id (cvg_cst v).
apply: continuous_compact; first exact: continuous_subspaceT cv.
exact: segment_compact.
Qed.
Lemma radial_segment_zero v : radial_segment v 0.
Proof. exists 0; first by rewrite /= in_itv /= lexx ler01. by rewrite scale0r. Qed.
Lemma radial_segment_one v : radial_segment v v.
Proof. exists 1; first by rewrite /= in_itv /= lexx ler01. by rewrite scale1r. Qed.
Lemma radial_segment_convex v x y (t : R) :
  radial_segment v x -> radial_segment v y -> 0 <= t <= 1 ->
  radial_segment v (x + t *: (y-x)).
Proof.
move=> [a ha <-] [b hb <-] /andP[t0 t1].
exists (a + t * (b-a)).
- move: ha hb; rewrite /= !in_itv /= => /andP[a0 a1] /andP[b0 b1].
  apply/andP; split; nra.
- by rewrite scalerDl -scalerA scalerBl.
Qed.
Lemma radial_segment_nonunique_preimages (v : 'rV[R]_m) : v != 0 ->
  exists x y : 'rV[R]_m, x != y /\ radial_segment v x /\ radial_segment v y /\
    x *m (0 : 'M[R]_(m,n)) = image_projection (radial_segment v) 0 /\
    y *m (0 : 'M[R]_(m,n)) = image_projection (radial_segment v) 0.
Proof.
move=> v0; exists 0, v; rewrite eq_sym v0; split=> //.
split; first exact: radial_segment_zero.
split; first exact: radial_segment_one.
have K0 : radial_segment v !=set0 by exists 0; exact: radial_segment_zero.
by rewrite (image_projection_zero K0) !mulmx0.
Qed.

End image_projection.

(* Normalize the unique image point; inverse zero is zero in the field. *)
Section image_direction.
Context {R : realType} {m n : nat}.
Implicit Types K : set 'rV[R]_m.
Implicit Types A : 'M[R]_(m, n).

Definition image_direction K A : 'rV[R]_n :=
  (frobenius (image_projection K A))^-1 *: image_projection K A.

Lemma image_direction_zero K A : image_projection K A = 0 ->
  image_direction K A = 0.
Proof. by move=> z0; rewrite /image_direction z0 scaler0. Qed.

Lemma image_direction_norm K A : image_projection K A != 0 ->
  frobenius (image_direction K A) = 1.
Proof.
move=> z0; rewrite /image_direction frobeniusZ normrV.
  by rewrite unitfE frobenius_eq0.
by rewrite ger0_norm ?frobenius_ge0 // mulVf // frobenius_eq0.
Qed.

Lemma image_direction_norm_le1 K A : frobenius (image_direction K A) <= 1.
Proof.
have [z0|z0] := eqVneq (image_projection K A) 0.
  by rewrite (image_direction_zero z0) frobenius0 ler01.
by rewrite (image_direction_norm z0).
Qed.

Lemma image_direction_support K A :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  forall x, K x ->
    frobenius (image_projection K A) <= mxdot (image_direction K A) (x *m A).
Proof.
move=> Kcp K0 Kcvx x Kx.
have [z0|z0] := eqVneq (image_projection K A) 0.
  by rewrite (image_direction_zero z0) z0 frobenius0 mxdot0l.
have [_ hv] := image_projectionP A Kcp K0 Kcvx.
have h := hv x Kx.
rewrite mxdotBr -frobenius_sqr subr_ge0 in h.
have f0 : 0 < frobenius (image_projection K A) by rewrite frobenius_gt0.
have fN0 : frobenius (image_projection K A) != 0 by rewrite frobenius_eq0.
rewrite /image_direction mxdotZl.
have if0 : 0 <= (frobenius (image_projection K A))^-1.
  by rewrite invr_ge0; exact: ltW f0.
have hm := ler_wpM2l if0 h.
by rewrite expr2 mulrA mulVf // mul1r in hm.
Qed.

Lemma image_direction_measurable K :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
    K (x + t *: (y - x))) ->
  measurable_fun [set: 'M[R]_(m,n)] (image_direction K).
Proof.
move=> Kcp K0 Kcvx.
apply: measurable_normalize_frobenius.
exact (image_projection_measurable Kcp K0 Kcvx).
Qed.
End image_direction.
