From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import interval topology normedtype.
From mathcomp Require Import derive trigo measure.
From mathcomp Require Import lebesgue_measure measurable_realfun lebesgue_integral.
From GaussianAnalysis Require Import measurable_matrix gauss gauss_ibp.
From GaussianAnalysis Require Import partial_derivative.

(**md**************************************************************************)
(* # Gaussian interpolation and Kahane's comparison inequality                *)
(*                                                                            *)
(* Let x have law gauss n, and let M t : 'M_(n, k) depend differentiably on   *)
(* a real parameter t. Then x *m M t is a centered Gaussian vector with       *)
(* covariance (M t)^T *m M t. For F : 'rV_k -> R of class C^2 whose           *)
(* derivatives of order at most 2 grow at most polynomially,                  *)
(* gauss_interpolation gives the derivative of t |-> E[F (x *m M t)]:         *)
(*   \sum_(j, l) ((M' t)^T *m M t) j l * E[d_l d_j F (x *m M t)],             *)
(* with M' the derivative of M and d_j F = 'D_(delta_mx 0 j) F the partial    *)
(* derivative along the j-th vector of the canonical basis. When the          *)
(* Hessian of F is symmetric, this is half the pairing of the derivative of   *)
(* the covariance with the expected Hessian.                                  *)
(*                                                                            *)
(* gauss_comparison is Kahane's comparison inequality: if                     *)
(*   \sum_(j, l) (A^T *m A - B^T *m B) j l * d_l d_j F z <= 0                 *)
(* for every z, then E[F (x *m A)] <= E[F (y *m B)] for x of law gauss n      *)
(* and y of law gauss m. The inequalities of Slepian, Sudakov-Fernique and    *)
(* Gordon follow from it for suitable F. The proof applies                    *)
(* gauss_interpolation to the path col_mx (cos t *: A) (sin t *: B), t in     *)
(* [0, pi / 2], whose ends give x *m A and y *m B for the two blocks of a     *)
(* vector of law gauss (n + m).                                               *)
(*                                                                            *)
(* gauss_comparison_partial is the same inequality for F given by its         *)
(* partial derivatives of order 1 and 2 at every point, those of order 2      *)
(* continuous: F is then of class C^2 (differentiable_partials of             *)
(* partial_derivative.v).                                                     *)
(*                                                                            *)
(* The first sections hold general facts used by the proofs: the chain rule   *)
(* along a curve, continuity and derivatives of matrix products, and          *)
(* integrals of finite sums.                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section differential_rV.
Context {R : realType} {k : nat} {W : normedModType R}.

Lemma diff_rV_sum (F : 'rV[R]_k -> W) (z v : 'rV[R]_k) : differentiable F z ->
  'd F z v = \sum_(j < k) v 0 j *: 'D_(delta_mx 0 j) F z.
Proof.
move=> dF; rewrite {1}(row_sum_delta v) linear_sum.
by apply: eq_bigr => j _; rewrite linearZ deriveE.
Qed.

Lemma is_derive_rV_comp (F : 'rV[R]_k -> W) (g : R -> 'rV[R]_k) t (dg : 'rV[R]_k) :
  differentiable F (g t) -> is_derive t 1 g dg ->
  is_derive t 1 (F \o g) (\sum_(j < k) dg 0 j *: 'D_(delta_mx 0 j) F (g t)).
Proof.
move=> dF gd.
have dg_ : differentiable g t by apply/derivable1_diffP; case: gd.
have dFg : differentiable (F \o g) t by exact: differentiable_comp.
apply: DeriveDef; first exact: diff_derivable.
rewrite deriveE // diff_comp //= -diff_rV_sum //.
by have -> : 'd g t 1 = dg by rewrite -deriveE //; case: gd.
Qed.

End differential_rV.

Section mulmx_norm.
Context {R : realType}.

Lemma mx_norm_mulmx_le m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  `|A *m B| <= n%:R * `|A| * `|B|.
Proof.
have -> : `|A *m B| = \big[maxr/0]_ij `|(A *m B) ij.1 ij.2| by rewrite -mx_normrE.
apply: bigmax_le => [|[i j] _]; first by rewrite !mulr_ge0.
rewrite mxE /= (le_trans (ler_norm_sum _ _ _))// -mulrA.
have -> : n%:R * (`|A| * `|B|) = \sum_(l < n) (`|A| * `|B|).
  by rewrite sumr_const card_ord mulr_natl.
by apply: ler_sum => l _; rewrite normrM ler_pM // mx_norm_entry_le.
Qed.

Lemma continuous_mulmxr m n p (B : 'M[R]_(n, p)) :
  continuous (fun A : 'M[R]_(m, n) => A *m B).
Proof.
move=> A; apply/(cvgrPdist_lt (F := nbhs A)) => e e0.
have k0 : 0 < n%:R * `|B| + 1 :> R by rewrite ltr_pwDr // mulr_ge0.
have := @cvgr_dist_lt _ _ _ (nbhs A) (nbhs_filter A) id A cvg_id _ (divr_gt0 e0 k0).
apply: filterS => A' hA'; rewrite -mulmxBl (le_lt_trans (mx_norm_mulmx_le _ _))//.
move: hA'; rewrite ltr_pdivlMr // => h.
have hn : 0 <= n%:R * `|B| :> R by rewrite mulr_ge0.
by have ha := normr_ge0 (A - A'); nra.
Qed.

Lemma continuous_mulmxl m n p (A : 'M[R]_(m, n)) :
  continuous (fun B : 'M[R]_(n, p) => A *m B).
Proof.
move=> B; apply/(cvgrPdist_lt (F := nbhs B)) => e e0.
have k0 : 0 < n%:R * `|A| + 1 :> R by rewrite ltr_pwDr // mulr_ge0.
have := @cvgr_dist_lt _ _ _ (nbhs B) (nbhs_filter B) id B cvg_id _ (divr_gt0 e0 k0).
apply: filterS => B' hB'; rewrite -mulmxBr (le_lt_trans (mx_norm_mulmx_le _ _))//.
move: hB'; rewrite ltr_pdivlMr // => h.
have hn : 0 <= n%:R * `|A| :> R by rewrite mulr_ge0.
by have hb := normr_ge0 (B - B'); nra.
Qed.

Lemma is_derive_mulmxl m n p (A : 'M[R]_(m, n)) (M : R -> 'M[R]_(n, p)) (t : R) dM :
  is_derive t 1 M dM -> is_derive t 1 (fun s => A *m M s) (A *m dM).
Proof.
move=> Md; have dM_ : differentiable M t by apply/derivable1_diffP; case: Md.
pose L : {linear 'M[R]_(n, p) -> 'M[R]_(m, p)} := mulmx A.
have cL : continuous L by exact: continuous_mulmxl.
have dL z : differentiable L z by exact: linear_differentiable.
have dLM : differentiable (L \o M) t by exact: differentiable_comp.
apply: DeriveDef; first exact: diff_derivable.
rewrite (_ : (fun s => A *m M s) = L \o M) // deriveE // diff_comp // diff_lin //=.
by rewrite -deriveE //; case: Md => _ ->.
Qed.

Lemma mx_norm_col_mx_le m1 m2 n (P : 'M[R]_(m1, n)) (Q : 'M[R]_(m2, n)) :
  `|col_mx P Q| <= `|P| + `|Q|.
Proof.
have -> : `|col_mx P Q| = \big[maxr/0]_ij `|col_mx P Q ij.1 ij.2|.
  by rewrite -mx_normrE.
apply: bigmax_le => [|[i j] _]; first by rewrite addr_ge0.
rewrite /= -[i]splitK; case: (fintype.split i) => i' /=.
  by rewrite col_mxEu (le_trans (mx_norm_entry_le _ _ _)) // lerDl.
by rewrite col_mxEd (le_trans (mx_norm_entry_le _ _ _)) // lerDr.
Qed.

Lemma mulmx_col_mx m n1 n2 p (x : 'M[R]_(m, n1 + n2)) (P : 'M[R]_(n1, p))
    (Q : 'M[R]_(n2, p)) :
  x *m col_mx P Q = lsubmx x *m P + rsubmx x *m Q.
Proof. by rewrite -{1}(hsubmxK x) mul_row_col. Qed.

End mulmx_norm.

Section is_derive_scalel.
Context {R : realType} {V : normedModType R}.

Lemma is_derive_scalel (a : R -> R) (P : V) (t da : R) :
  is_derive t 1 a da -> is_derive t 1 (fun s => a s *: P) (da *: P).
Proof.
move=> ad; have da_ : differentiable a t by apply/derivable1_diffP; case: ad.
have dZ : differentiable (fun s => a s *: P) t by exact: differentiableZl.
apply: DeriveDef; first exact: diff_derivable.
rewrite deriveE // diffZl //=.
by rewrite -deriveE //; case: ad => _ ->.
Qed.

End is_derive_scalel.

Section Rintegral_sum.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Lemma Rintegral_sum (I : Type) (s : seq I) (D : set T) (f : I -> T -> R) :
  measurable D -> (forall i, mu.-integrable D (EFin \o f i)) ->
  \int[mu]_(x in D) \sum_(i <- s) f i x = \sum_(i <- s) \int[mu]_(x in D) f i x.
Proof.
move=> mD fi; elim: s => [|i s IH].
  by under eq_Rintegral do rewrite big_nil; rewrite big_nil Rintegral_cst// mul0r.
under eq_Rintegral do rewrite big_cons.
rewrite big_cons -IH RintegralD //.
rewrite (_ : EFin \o _ = (fun x => \sum_(j <- s) (EFin \o f j) x)).
  by apply/funext => x; rewrite /= sumEFin.
by apply: integrable_sum => // j _; exact: fi.
Qed.

End Rintegral_sum.

Section gauss_entry_integrable.
Context {R : realType}.

Lemma integrable_gauss_entry n (i : 'I_n) (G : 'rV[R]_n -> R) (c : R) q :
  measurable_fun [set: 'rV[R]_n] G -> (forall x, `|G x| <= c * (1 + `|x| ^+ q)) ->
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun x : 'rV[R]_n => x 0 i * G x)).
Proof.
move=> mG GC; have c0 : 0 <= c.
  have := GC 0; rewrite normr0 expr0n => h; have := normr_ge0 (G 0).
  by case: (q == 0%N) h => /= h; nra.
have mxG : measurable_fun [set: 'rV[R]_n] (fun x : 'rV[R]_n => x 0 i * G x).
  by apply: measurable_funM => //; exact: measurable_mxentry.
apply: (integrable_gauss_poly mxG (C := 2 * c) (k := q.+1)) => x.
rewrite normrM exprS; have hb := GC x; have a0 := normr_ge0 x.
have ae := mx_norm_entry_le x 0 i; have e0 := normr_ge0 (x 0 i).
have p0 := exprn_ge0 q a0; have b0 := normr_ge0 (G x).
have h1 : `|x 0 i| * `|G x| <= c * (`|x| + `|x| * `|x| ^+ q).
  by have := ler_wpM2r b0 ae; have := ler_wpM2l a0 hb; nra.
have h2 : `|x| <= 1 + `|x| * `|x| ^+ q.
  case: (leP `|x| 1) => x1; first by nra.
  have : 1 <= `|x| ^+ q by rewrite exprn_ege1// ltW.
  nra.
nra.
Qed.

End gauss_entry_integrable.

(* F is of class C^2, and F and its partial derivatives of order 1 and 2
   are bounded by C (1 + |z|^p). *)
Section gauss_interpolation.
Context {R : realType} {k : nat}.
Variable F : 'rV[R]_k -> R.
Local Notation DF j := ('D_(delta_mx 0 j) F).
Local Notation D2F j l := ('D_(delta_mx 0 l) ('D_(delta_mx 0 j) F)).

Hypothesis F_diff : forall z, differentiable F z.
Hypothesis DF_diff : forall j z, differentiable (DF j) z.
Hypothesis D2F_cont : forall j l, continuous (D2F j l).
Variables (C : R) (p : nat).
Hypothesis F_poly : forall z, `|F z| <= C * (1 + `|z| ^+ p).
Hypothesis DF_poly : forall j z, `|DF j z| <= C * (1 + `|z| ^+ p).
Hypothesis D2F_poly : forall j l z, `|D2F j l z| <= C * (1 + `|z| ^+ p).

Let C_ge0 : 0 <= C.
Proof.
have := F_poly 0; rewrite normr0 expr0n => h; have := normr_ge0 (F 0).
by case: (p == 0%N) h => /= h; nra.
Qed.

Let poly_mulmx n (G : 'rV[R]_k -> R) (M : 'M[R]_(n, k)) (K : R) :
  `|M| <= K -> (forall z, `|G z| <= C * (1 + `|z| ^+ p)) ->
  forall x : 'rV[R]_n,
    `|G (x *m M)| <= C * (1 + (n%:R * K) ^+ p) * (1 + `|x| ^+ p).
Proof.
move=> MK GC x; have C0 := C_ge0.
have K0 : 0 <= K := le_trans (normr_ge0 _) MK.
apply: (le_trans (GC _)).
have h1 : `|x *m M| <= n%:R * K * `|x|.
  rewrite (le_trans (mx_norm_mulmx_le _ _)) // mulrAC.
  by apply: ler_wpM2r => //; apply: ler_wpM2l.
have h2 : `|x *m M| ^+ p <= (n%:R * K) ^+ p * `|x| ^+ p.
  by rewrite -exprMn; apply: lerXn2r => //; rewrite nnegrE ?mulr_ge0.
have c0 := exprn_ge0 p (mulr_ge0 (ler0n R n) K0).
have a0 := exprn_ge0 p (normr_ge0 x).
have b0 := exprn_ge0 p (normr_ge0 (x *m M)).
nra.
Qed.

Let integrable_D2F_mulmx n (M : 'M[R]_(n, k)) j l :
  (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun x : 'rV[R]_n => D2F j l (x *m M))).
Proof.
have cD2 : continuous (fun x : 'rV[R]_n => D2F j l (x *m M)).
  move=> x; apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m M)
    (g := D2F j l)); [exact: continuous_mulmxr|exact: D2F_cont].
exact: (integrable_gauss_poly (continuous_measurable_mx cD2)
  (poly_mulmx (lexx _) (D2F_poly j l))).
Qed.

(* Integration by parts for x_i against a partial derivative of F at x *m M. *)
Lemma gauss_ibp_mulmx n (M : 'M[R]_(n, k)) (i : 'I_n) (j : 'I_k) :
  \int[gauss n]_x (x 0 i * DF j (x *m M)) =
  \sum_(l < k) M i l * \int[gauss n]_x D2F j l (x *m M).
Proof.
have C0 := C_ge0; set c := C * (1 + (n%:R * `|M|) ^+ p).
have c0 : 0 <= c by rewrite mulr_ge0 // addr_ge0 // exprn_ge0 // mulr_ge0.
have cM : continuous (fun x : 'rV[R]_n => x *m M) := continuous_mulmxr (B := M).
pose G (x : 'rV[R]_n) := DF j (x *m M).
pose dG (x : 'rV[R]_n) := \sum_(l < k) M i l * D2F j l (x *m M).
have cG : continuous G.
  by move=> x; apply: continuous_comp; [exact: cM|exact: differentiable_continuous].
have cD2 l : continuous (fun x : 'rV[R]_n => D2F j l (x *m M)).
  move=> x; apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m M)
    (g := D2F j l)); [exact: cM|exact: D2F_cont].
have cdG : continuous dG.
  by apply: continuous_sum => l x; exact: (cvgM (cvg_cst _) (cD2 l x)).
have dG_ x : is_derive x (delta_mx 0 i) G (dG x).
  apply: (is_derive_transfer (G := DF j) (b := x *m M) (w := delta_mx 0 i *m M)).
    by move=> h; rewrite /G mulmxDl scalemxAl.
  apply: DeriveDef; first exact/diff_derivable/DF_diff.
  rewrite deriveE // diff_rV_sum //; apply: eq_bigr => l _.
  by rewrite -rowE mxE.
set c' := c * (1 + k%:R * `|M|).
have kM : 0 <= k%:R * `|M| :> R by rewrite mulr_ge0.
have hb (x : 'rV[R]_n) : 0 <= c * (1 + `|x| ^+ p).
  by rewrite mulr_ge0 // addr_ge0 // exprn_ge0.
have bG x : `|G x| <= c' * (1 + `|x| ^+ p).
  apply: (le_trans (poly_mulmx (lexx _) (DF_poly j) x)).
  by rewrite -/c /c'; have := hb x; nra.
have bD2 l x : `|D2F j l (x *m M)| <= c * (1 + `|x| ^+ p).
  exact: (poly_mulmx (lexx _) (D2F_poly j l) x).
have bdG x : `|dG x| <= c' * (1 + `|x| ^+ p).
  rewrite /dG (le_trans (ler_norm_sum _ _ _)) //.
  apply: (@le_trans _ _ (\sum_(l < k) `|M| * (c * (1 + `|x| ^+ p)))).
    apply: ler_sum => l _; rewrite normrM.
    by apply: ler_pM => //; exact: mx_norm_entry_le.
  rewrite sumr_const card_ord -mulr_natl /c'.
  by have := hb x; have := normr_ge0 M; nra.
have -> : \int[gauss n]_x (x 0 i * DF j (x *m M)) = \int[gauss n]_x dG x.
  by rewrite /Rintegral (gauss_ibp dG_ cG cdG bG bdG).
have iD2 l : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun x => D2F j l (x *m M))).
  exact: (integrable_gauss_poly (continuous_measurable_mx (cD2 l)) (bD2 l)).
rewrite /dG Rintegral_sum //.
  move=> l; rewrite (_ : EFin \o _ =
      (fun x => (M i l)%:E * (EFin \o (fun x => D2F j l (x *m M))) x)%E).
    by apply/funext => x; rewrite /= EFinM.
  exact: integrableZl.
by apply: eq_bigr => l _; rewrite RintegralZl.
Qed.

(* The same for the derivative of F at x *m M in the direction x *m M'. *)
Lemma gauss_ibp_gradient n (M M' : 'M[R]_(n, k)) :
  \int[gauss n]_x (\sum_(j < k) (x *m M') 0 j * DF j (x *m M)) =
  \sum_(j < k) \sum_(l < k) (M'^T *m M) j l * \int[gauss n]_x D2F j l (x *m M).
Proof.
have cM : continuous (fun x : 'rV[R]_n => x *m M) := continuous_mulmxr (B := M).
have cDF j : continuous (fun x : 'rV[R]_n => DF j (x *m M)).
  move=> x; apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m M)
    (g := DF j)); [exact: cM|exact: differentiable_continuous].
have iE i j : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun x : 'rV[R]_n => x 0 i * DF j (x *m M))).
  exact: (integrable_gauss_entry i (continuous_measurable_mx (cDF j))
    (poly_mulmx (lexx _) (DF_poly j))).
have -> : \int[gauss n]_x \sum_(j < k) (x *m M') 0 j * DF j (x *m M) =
    \int[gauss n]_x \sum_(ji : 'I_k * 'I_n)
      M' ji.2 ji.1 * (x 0 ji.2 * DF ji.1 (x *m M)).
  apply: eq_Rintegral => x _.
  rewrite -(pair_bigA _ (fun j i => M' i j * (x 0 i * DF j (x *m M)))) /=.
  apply: eq_bigr => j _; rewrite mxE mulr_suml; apply: eq_bigr => i _.
  by rewrite mulrCA mulrA.
rewrite Rintegral_sum //.
  move=> ji; pose g := fun x : 'rV[R]_n => x 0 ji.2 * DF ji.1 (x *m M).
  rewrite (_ : EFin \o _ = (fun x => (M' ji.2 ji.1)%:E * (EFin \o g) x)%E).
    by apply/funext => x; rewrite /= EFinM.
  by apply: integrableZl => //; exact: iE.
under eq_bigr => ji _ do rewrite RintegralZl // gauss_ibp_mulmx.
rewrite -(pair_bigA _ (fun j i =>
  M' i j * \sum_(l < k) M i l * \int[gauss n]_x D2F j l (x *m M))) /=.
apply: eq_bigr => j _; under eq_bigr => i _ do rewrite big_distrr /=.
rewrite exchange_big /=; apply: eq_bigr => l _.
rewrite mxE big_distrl /=; apply: eq_bigr => i _.
by rewrite mxE mulrA.
Qed.

Theorem gauss_interpolation n (M M' : R -> 'M[R]_(n, k)) (u v K : R) :
  (forall s, s \in `]u, v[ -> is_derive s 1 M (M' s)) ->
  (forall s, s \in `]u, v[ -> `|M s| <= K) ->
  (forall s, s \in `]u, v[ -> `|M' s| <= K) ->
  forall t, t \in `]u, v[ ->
  is_derive t 1 (fun s => \int[gauss n]_x F (x *m M s))
    (\sum_(j < k) \sum_(l < k) ((M' t)^T *m M t) j l *
      \int[gauss n]_x D2F j l (x *m M t)).
Proof.
move=> Md Mb M'b t tI; have C0 := C_ge0.
have K0 : 0 <= K by exact: le_trans (normr_ge0 _) (Mb t tI).
have cF : continuous F := fun z => differentiable_continuous (F_diff z).
pose f s (x : 'rV[R]_n) := F (x *m M s).
pose df s (x : 'rV[R]_n) := \sum_(j < k) (x *m M' s) 0 j * DF j (x *m M s).
have mf s : measurable_fun [set: 'rV[R]_n] (f s).
  apply: continuous_measurable_mx => x.
  apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m M s) (g := F)).
    exact: continuous_mulmxr.
  exact: cF.
have intf s : `]u, v[%classic s -> (gauss n).-integrable setT (EFin \o f s).
  move=> sI'; have sI : s \in `]u, v[ := sI'.
  apply: (integrable_gauss_poly (mf s) (C := C * (1 + (n%:R * K) ^+ p)) (k := p)).
  exact: (poly_mulmx (Mb s sI) F_poly).
have fd s x : s \in `]u, v[ -> is_derive s 1 (f ^~ x) (df s x).
  move=> sI; exact: (is_derive_rV_comp (F_diff (x *m M s))
    (is_derive_mulmxl x (Md s sI))).
(* A bound on the derivative of the integrand, uniform in s. *)
set c := C * (1 + (n%:R * K) ^+ p).
have c0 : 0 <= c by rewrite mulr_ge0 // addr_ge0 // exprn_ge0 // mulr_ge0.
set c2 := k%:R * (n%:R * K) * c.
have c20 : 0 <= c2.
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; apply: mulr_ge0.
pose G (x : 'rV[R]_n) := 2 * c2 * (1 + `|x| ^+ p.+1).
have G_ge0 x : 0 <= G x.
  by apply: mulr_ge0; [apply: mulr_ge0|rewrite addr_ge0 // exprn_ge0].
have mG : measurable_fun [set: 'rV[R]_n] G.
  apply: measurable_funM => //; apply: measurable_funD => //.
  apply: measurable_funX; exact: (continuous_measurable_mx (@norm_continuous _ _)).
have intG : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o G).
  apply: (integrable_gauss_poly mG (C := 2 * c2) (k := p.+1)) => x.
  by rewrite ger0_norm.
have G_ub s x : `]u, v[%classic s -> [set: 'rV[R]_n] x ->
    `|partial1of2 f s x| <= G x.
  move=> sI' _; have sI : s \in `]u, v[ := sI'.
  rewrite partial1of2E (@derive_val _ _ _ _ _ _ _ (fd s x sI)) /df.
  rewrite (le_trans (ler_norm_sum _ _ _)) //.
  apply: (@le_trans _ _
    (\sum_(j < k) (n%:R * K * `|x|) * (c * (1 + `|x| ^+ p)))).
    apply: ler_sum => j _; rewrite normrM; apply: ler_pM => //.
      apply: (le_trans (mx_norm_entry_le _ 0 j)).
      apply: (le_trans (mx_norm_mulmx_le _ _)); rewrite mulrAC.
      by apply: ler_wpM2r => //; apply: ler_wpM2l => //; exact: M'b.
    exact: (poly_mulmx (Mb s sI) (DF_poly j) x).
  rewrite sumr_const card_ord -mulr_natl /G -/c2 exprS.
  have a0 := normr_ge0 x; have p0 := exprn_ge0 p a0.
  have h2 : `|x| <= 1 + `|x| * `|x| ^+ p.
    case: (leP `|x| 1) => x1; first by nra.
    have : 1 <= `|x| ^+ p by rewrite exprn_ege1// ltW.
    nra.
  by move: c20; rewrite /c2 => q0; nra.
have tI' : `]u, v[%classic t := tI.
have derf1 s x : `]u, v[%classic s -> [set: 'rV[R]_n] x ->
    derivable (f ^~ x) s 1.
  by move=> sI _; exact: (@ex_derive _ _ _ _ _ _ _ (fd s x sI)).
apply: DeriveDef.
  exact: (derivable_under_integral measurableT tI' intf derf1 G_ge0 intG G_ub).
rewrite -derive1E.
rewrite (differentiation_under_integral measurableT tI' intf derf1 G_ge0 intG G_ub).
rewrite -gauss_ibp_gradient; apply: eq_Rintegral => x _.
by rewrite partial1of2E (@derive_val _ _ _ _ _ _ _ (fd t x tI)).
Qed.

Theorem gauss_comparison n m (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k)) :
  (forall z, \sum_(j < k) \sum_(l < k) (A^T *m A - B^T *m B) j l * D2F j l z <= 0) ->
  (\int[gauss n]_x (F (x *m A))%:E <= \int[gauss m]_y (F (y *m B))%:E)%E.
Proof.
move=> SF; set S := A^T *m A - B^T *m B.
(* Interpolate between x *m A and y *m B, with x and y the two blocks of a
   vector of law gauss (n + m), along a quarter circle. *)
pose M (t : R) : 'M[R]_(n + m, k) := col_mx (cos t *: A) (sin t *: B).
pose M' (t : R) : 'M[R]_(n + m, k) := col_mx (- sin t *: A) (cos t *: B).
pose phi (t : R) := \int[gauss (n + m)]_x F (x *m M t).
have Md (t : R) : is_derive t 1 M (M' t).
  have -> : M = fun t => cos t *: col_mx A 0 + sin t *: col_mx 0 B.
    by apply/funext => s; rewrite /M !scale_col_mx add_col_mx !scaler0 addr0 add0r.
  have -> : M' t = - sin t *: col_mx A 0 + cos t *: col_mx 0 B.
    by rewrite /M' !scale_col_mx add_col_mx !scaler0 addr0 add0r.
  exact: (is_deriveD (is_derive_scalel _ (is_derive_cos t))
    (is_derive_scalel _ (is_derive_sin t))).
have Zb (a : R) n' (P : 'M[R]_(n', k)) : `|a| <= 1 -> `|a *: P| <= `|P|.
  by move=> a1; rewrite normrZ; have := normr_ge0 P; have := normr_ge0 a; nra.
have Mb t : `|M t| <= `|A| + `|B|.
  apply: (le_trans (mx_norm_col_mx_le _ _)); apply: lerD; apply: Zb.
    exact: cos_max.
  exact: sin_max.
have M'b t : `|M' t| <= `|A| + `|B|.
  apply: (le_trans (mx_norm_col_mx_le _ _)); apply: lerD; apply: Zb.
    by rewrite normrN; exact: sin_max.
  exact: cos_max.
have phid (t : R) : t \in `]-1, 2[ -> is_derive t 1 phi
    (\sum_(j < k) \sum_(l < k) ((M' t)^T *m M t) j l *
      \int[gauss (n + m)]_x D2F j l (x *m M t)).
  exact: (gauss_interpolation (fun s _ => Md s) (fun s _ => Mb s)
    (fun s _ => M'b s)).
have MM (t : R) : (M' t)^T *m M t = - (sin t * cos t) *: S.
  rewrite /M /M' tr_col_mx mul_row_col !linearZ /=.
  rewrite -!scalemxAl !scalerA scalerBr -scaleNr.
  congr (_ *: _ + _ *: _).
    by rewrite /GRing.scale /= mulrN mulrN mulrC.
  by rewrite /GRing.scale /= mulrN opprK.
(* The expected second derivative along S is nonpositive. *)
have Ile0 (t : R) : \sum_(j < k) \sum_(l < k)
    S j l * \int[gauss (n + m)]_x D2F j l (x *m M t) <= 0.
  rewrite pair_bigA /=.
  pose h (jl : 'I_k * 'I_k) (x : 'rV[R]_(n + m)) :=
    S jl.1 jl.2 * D2F jl.1 jl.2 (x *m M t).
  have ih jl : (gauss (n + m)).-integrable [set: 'rV[R]_(n + m)] (EFin \o h jl).
    rewrite (_ : EFin \o _ = (fun x => (S jl.1 jl.2)%:E *
        (EFin \o (fun x : 'rV[R]_(n + m) => D2F jl.1 jl.2 (x *m M t))) x)%E).
      by apply/funext => x; rewrite /= EFinM.
    by apply: integrableZl => //; exact: integrable_D2F_mulmx.
  have -> : \sum_(jl : 'I_k * 'I_k)
      S jl.1 jl.2 * \int[gauss (n + m)]_x D2F jl.1 jl.2 (x *m M t) =
      \int[gauss (n + m)]_x \sum_(jl : 'I_k * 'I_k) h jl x.
    rewrite Rintegral_sum //; apply: eq_bigr => jl _.
    by rewrite RintegralZl //; exact: integrable_D2F_mulmx.
  have ig : (gauss (n + m)).-integrable [set: 'rV[R]_(n + m)]
      (EFin \o (fun x => \sum_(jl : 'I_k * 'I_k) h jl x)).
    rewrite (_ : EFin \o _ = (fun x => \sum_(jl : 'I_k * 'I_k) (EFin \o h jl) x)%E).
      by apply/funext => x; rewrite /= sumEFin.
    by apply: integrable_sum => // jl _; exact: ih.
  rewrite -oppr_ge0 -mulN1r -RintegralZl //.
  apply: Rintegral_ge0 => x _; rewrite mulN1r oppr_ge0.
  by rewrite -(pair_bigA _ (fun j l => S j l * D2F j l (x *m M t))) /=; exact: SF.
(* So phi is nondecreasing on [0, pi / 2]. *)
have pi2 : 0 < pi / 2 :> R by rewrite divr_gt0 // pi_gt0.
have pi2lt : pi / 2 < 2 :> R := @pihalf_lt2 R.
have inI (t : R) : 0 <= t -> t <= pi / 2 -> t \in `]-1, 2[.
  by move=> t0 t1; rewrite in_itv /=; apply/andP; split; lra.
have dphi (t : R) : 0 <= t -> t <= pi / 2 -> derivable phi t 1.
  by move=> t0 t1; case: (phid t (inI t t0 t1)).
have phi'ge0 (t : R) : t \in `]0, pi / 2[ -> 0 <= phi^`() t.
  rewrite in_itv /= => /andP[t0 t1].
  rewrite derive1E (@derive_val _ _ _ _ _ _ _ (phid t (inI t (ltW t0) (ltW t1)))).
  have -> : \sum_(j < k) \sum_(l < k) ((M' t)^T *m M t) j l *
      \int[gauss (n + m)]_x D2F j l (x *m M t) =
      - (sin t * cos t) * \sum_(j < k) \sum_(l < k)
        S j l * \int[gauss (n + m)]_x D2F j l (x *m M t).
    rewrite big_distrr /=; apply: eq_bigr => j _.
    rewrite big_distrr /=; apply: eq_bigr => l _.
    by rewrite MM mxE mulrA.
  apply: mulr_le0 => //; rewrite oppr_le0; apply: mulr_ge0; apply: ltW.
    by apply: sin_gt0_pihalf; rewrite t0 t1.
  by apply: cos_gt0_pihalf; rewrite t1 andbT; lra.
have cphi : {within `[0, pi / 2], continuous phi}.
  apply: derivable_within_continuous => t.
  by rewrite in_itv /= => /andP[t0 t1]; exact: dphi.
have le_phi : phi 0 <= phi (pi / 2).
  apply: (ger0_derive1_ndecr _ phi'ge0 cphi) => //; last exact: ltW.
  by move=> t; rewrite in_itv /= => /andP[t0 t1]; apply: dphi; exact: ltW.
(* At the ends of the path, phi is the expectation of F (x *m A) and of
   F (y *m B). *)
have iF n' (P : 'M[R]_(n', k)) : (gauss n').-integrable [set: 'rV[R]_n']
    (EFin \o (fun x : 'rV[R]_n' => F (x *m P))).
  apply: (integrable_gauss_poly _ (poly_mulmx (lexx _) F_poly)).
  apply: continuous_measurable_mx => x.
  apply: (continuous_comp (f := fun y : 'rV[R]_n' => y *m P) (g := F)).
    exact: continuous_mulmxr.
  exact: differentiable_continuous.
have phi0 : (phi 0)%:E = (\int[gauss n]_x (F (x *m A))%:E)%E.
  rewrite /phi /M cos0 sin0 scale1r scale0r.
  under eq_Rintegral do rewrite mulmx_col_mx mulmx0 addr0.
  have E := integral_gauss_lsubmx m (iF n A).
  rewrite /Rintegral (_ : (\int[gauss (n + m)]_x (F (lsubmx x *m A))%:E)%E =
      \int[gauss n]_x (F (x *m A))%:E)%E; first exact: E.
  by rewrite fineK //; exact: (integrable_fin_num _ (iF n A)).
have phi1 : (phi (pi / 2))%:E = (\int[gauss m]_y (F (y *m B))%:E)%E.
  rewrite /phi /M cos_pihalf sin_pihalf scale1r scale0r.
  under eq_Rintegral do rewrite mulmx_col_mx mulmx0 add0r.
  have E := integral_gauss_rsubmx n (iF m B).
  rewrite /Rintegral (_ : (\int[gauss (n + m)]_x (F (rsubmx x *m B))%:E)%E =
      \int[gauss m]_y (F (y *m B))%:E)%E; first exact: E.
  by rewrite fineK //; exact: (integrable_fin_num _ (iF m B)).
by rewrite -phi0 -phi1 lee_fin.
Qed.

End gauss_interpolation.

(* Kahane's comparison inequality for F given by its partial derivatives of
   order 1 and 2, continuous at order 2: F is then of class C^2. *)
Section gauss_comparison_partial.
Context {R : realType} {k : nat}.
Variables (F : 'rV[R]_k -> R) (DF : 'I_k -> 'rV[R]_k -> R)
  (D2F : 'I_k -> 'I_k -> 'rV[R]_k -> R).
Hypothesis F_partial : forall j z, is_derive z (delta_mx 0 j) F (DF j z).
Hypothesis DF_partial : forall j l z, is_derive z (delta_mx 0 l) (DF j) (D2F j l z).
Hypothesis D2F_cont : forall j l, continuous (D2F j l).
Variables (C : R) (p : nat).
Hypothesis F_poly : forall z, `|F z| <= C * (1 + `|z| ^+ p).
Hypothesis DF_poly : forall j z, `|DF j z| <= C * (1 + `|z| ^+ p).
Hypothesis D2F_poly : forall j l z, `|D2F j l z| <= C * (1 + `|z| ^+ p).

Let DF_diff j z : differentiable (DF j) z.
Proof.
exact: (differentiable_partials (fun l z => @DF_partial j l z)
  (fun l => @D2F_cont j l)).
Qed.

Let DF_cont j : continuous (DF j).
Proof. by move=> z; apply: differentiable_continuous; exact: DF_diff. Qed.

Let F_diff z : differentiable F z.
Proof. exact: (differentiable_partials (fun j z => @F_partial j z) DF_cont). Qed.

Let DFE j : 'D_(delta_mx 0 j) F = DF j.
Proof. by apply/funext => z; case: (@F_partial j z). Qed.

Let D2FE j l : 'D_(delta_mx 0 l) ('D_(delta_mx 0 j) F) = D2F j l.
Proof. by rewrite DFE; apply/funext => z; case: (@DF_partial j l z). Qed.

Let DFEz j z : 'D_(delta_mx 0 j) F z = DF j z.
Proof. by case: (@F_partial j z). Qed.

Let D2FEz j l z : 'D_(delta_mx 0 l) ('D_(delta_mx 0 j) F) z = D2F j l z.
Proof. by rewrite (DFE j); case: (@DF_partial j l z). Qed.

Theorem gauss_comparison_partial n m (A : 'M[R]_(n, k)) (B : 'M[R]_(m, k)) :
  (forall z, \sum_(j < k) \sum_(l < k) (A^T *m A - B^T *m B) j l * D2F j l z <= 0) ->
  (\int[gauss n]_x (F (x *m A))%:E <= \int[gauss m]_y (F (y *m B))%:E)%E.
Proof.
move=> SF; apply: (gauss_comparison F_diff _ _ F_poly).
- by move=> j z; rewrite (DFE j); exact: DF_diff.
- by move=> j l; rewrite (D2FE j l).
- by move=> j z; rewrite DFEz.
- by move=> j l z; rewrite D2FEz.
- move=> z; under eq_bigr => j _ do under eq_bigr => l _ do rewrite D2FEz.
  exact: SF.
Qed.

End gauss_comparison_partial.
