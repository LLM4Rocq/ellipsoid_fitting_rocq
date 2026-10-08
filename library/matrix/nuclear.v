From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals topology.
From mathcomp Require Import normedtype ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.convex Require Import moreau.

(**md**************************************************************************)
(* # The nuclear norm and the range duality                                   *)
(*                                                                            *)
(* The nuclear norm of A : 'M[R]_(m, n) is the dual norm of the operator norm *)
(* for the Frobenius pairing <A, B> = mxdot A B. For a symmetric matrix it is *)
(* the sum of the absolute values of the eigenvalues.                         *)
(*                                                                            *)
(* - nuclear_ub, nuclear_le: the supremum; nuclear_ge0, nuclearZ, nuclearN,   *)
(*   nuclearD and nuclear_eq0: a norm; mxdot_le_nuclear, the duality          *)
(*   inequality |<A, B>| <= opnorm B * nuclear A.                             *)
(* - frobenius_le_nuclear and nuclear_le_frobenius: frobenius A <= nuclear A  *)
(*   <= sqrt n * frobenius A (frobenius_le_opnorm: frobenius B <= sqrt n *    *)
(*   opnorm B); frobenius_sqr_le_nuclear: |A|_F^2 <= opnorm A * nuclear A.    *)
(* - nuclear_outer: nuclear (x x^T) = |x|^2.                                  *)
(* - nuclear_spectral: for A = P^T diag(d) P with P orthogonal, nuclear A =   *)
(*   sum_i |d_i|, attained at P^T diag(sign d_i) P; nuclear_sym: for A        *)
(*   symmetric, the supremum may be taken over the symmetric B.               *)
(* - range_duality, Lemma 2.2 of Koehler and Sohn (arXiv 2608.27372, lines    *)
(*   794-826) in the form the paper uses: for W_1, ..., W_k in 'M[R]_n, if    *)
(*   |<l, y>| <= M nuclear (coef_adj W l) for every l in 'rV[R]_k, then       *)
(*   y = coef_map W D for some D with opnorm D <= M; range_duality_sym: D is  *)
(*   symmetric when the W_i are. The proof projects y on the compact convex   *)
(*   set {coef_map W D | opnorm D <= M} (proj of library/convex/moreau.v),    *)
(*   seen in 'rV[R]_(n * n) through vec_mx (mxdot_vec_mxr): no Slater         *)
(*   condition or general convex duality is needed.                           *)
(*                                                                            *)
(* ```                                                                        *)
(*     nuclear A == sup of <A, B> over the B with opnorm B <= 1               *)
(*   coef_map W D == the row (<W_i, D>)_i                                     *)
(*   coef_adj W l == sum_i l_i W_i, the adjoint of coef_map W                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section nuclear.
Variable R : realType.
Implicit Types m n : nat.

Definition nuclear m n (A : 'M[R]_(m, n)) : R :=
  sup [set mxdot A B | B in [set B : 'M[R]_(m, n) | opnorm B <= 1]].

Lemma frobenius_le_opnorm m n (B : 'M[R]_(m, n)) :
  frobenius B <= Num.sqrt n%:R * opnorm B.
Proof.
have := frobenius_mulmx_mx_opnorm B (1%:M : 'M[R]_n).
rewrite mulmx1 => h; apply: le_trans h _.
have -> : frobenius (1%:M : 'M[R]_n) = Num.sqrt n%:R.
  by rewrite /frobenius mxdot_trace trmx1 mulmx1 mxtrace1.
by rewrite mulrC.
Qed.

Lemma nuclear_has_sup m n (A : 'M[R]_(m, n)) :
  has_sup [set mxdot A B | B in [set B : 'M[R]_(m, n) | opnorm B <= 1]].
Proof.
split; first by exists (mxdot A 0), 0 => //=; rewrite opnorm0 ler01.
exists (frobenius A * Num.sqrt n%:R) => _ [B /= B1 <-].
apply: le_trans (ler_mxdot A B) _; apply: ler_wpM2l; first exact: frobenius_ge0.
apply: le_trans (frobenius_le_opnorm B) _.
by rewrite -[leRHS]mulr1 ler_wpM2l ?sqrtr_ge0.
Qed.

Lemma nuclear_ub m n (A B : 'M[R]_(m, n)) : opnorm B <= 1 -> mxdot A B <= nuclear A.
Proof.
by move=> B1; apply: (ub_le_sup (proj2 (nuclear_has_sup A))); exists B.
Qed.

Lemma nuclear_le m n (A : 'M[R]_(m, n)) (b : R) :
  (forall B : 'M[R]_(m, n), opnorm B <= 1 -> mxdot A B <= b) -> nuclear A <= b.
Proof.
move=> Ab; apply: ge_sup; first exact: (proj1 (nuclear_has_sup A)).
by move=> _ [B /= B1 <-]; exact: Ab.
Qed.

Lemma nuclear_ge0 m n (A : 'M[R]_(m, n)) : 0 <= nuclear A.
Proof.
by apply: le_trans (nuclear_ub A (B := 0) _); rewrite ?mxdot0r // opnorm0 ler01.
Qed.

(* The duality inequality. *)
Lemma mxdot_le_nuclear m n (A B : 'M[R]_(m, n)) :
  `|mxdot A B| <= opnorm B * nuclear A.
Proof.
have [B0|B0] := eqVneq (opnorm B) 0.
  rewrite B0 mul0r; apply: le_trans (mxdot_le A B) _.
  have := frobenius_le_opnorm B; rewrite B0 mulr0 => h.
  have -> : frobenius B = 0 by apply/le_anti; rewrite h frobenius_ge0.
  by rewrite mulr0.
have Bp : 0 < opnorm B by rewrite lt_def B0 opnorm_ge0.
set B' := (opnorm B)^-1 *: B.
have B1 : opnorm B' <= 1.
  by rewrite opnormZ ger0_norm ?invr_ge0 ?opnorm_ge0 // mulVf.
have B1' : opnorm (- B') <= 1 by rewrite opnormN.
have e : mxdot A B = opnorm B * mxdot A B'.
  by rewrite /B' mxdotZr mulrA mulfV ?mul1r.
rewrite e normrM (ger0_norm (opnorm_ge0 _)) ler_wpM2l ?opnorm_ge0 //.
rewrite ler_norml; apply/andP; split; last exact: nuclear_ub.
by rewrite lerNl -mxdotNr; apply: nuclear_ub.
Qed.

Lemma nuclearZ m n (a : R) (A : 'M[R]_(m, n)) : nuclear (a *: A) = `|a| * nuclear A.
Proof.
have le b (X : 'M[R]_(m, n)) : nuclear (b *: X) <= `|b| * nuclear X.
  apply: nuclear_le => B B1; rewrite mxdotZl.
  apply: le_trans (ler_norm _) _; rewrite normrM ler_wpM2l //.
  apply: le_trans (mxdot_le_nuclear X B) _.
  by rewrite -[leRHS]mul1r ler_wpM2r ?nuclear_ge0.
apply/le_anti/andP; split; first exact: le.
have [->|a0] := eqVneq a 0; first by rewrite normr0 mul0r nuclear_ge0.
have := le a^-1 (a *: A); rewrite scalerA mulVf // scale1r normrV ?unitfE //.
have ap : 0 < `|a| by rewrite normr_gt0.
by rewrite -(ler_pM2l ap) mulrA mulfV ?mul1r // gt_eqF.
Qed.

Lemma nuclearN m n (A : 'M[R]_(m, n)) : nuclear (- A) = nuclear A.
Proof. by rewrite -scaleN1r nuclearZ normrN normr1 mul1r. Qed.

Lemma nuclearD m n (A B : 'M[R]_(m, n)) : nuclear (A + B) <= nuclear A + nuclear B.
Proof.
apply: nuclear_le => C C1; rewrite mxdotDl.
by apply: lerD; exact: nuclear_ub.
Qed.

Lemma frobenius_sqr_le_nuclear m n (A : 'M[R]_(m, n)) :
  frobenius A ^+ 2 <= opnorm A * nuclear A.
Proof.
rewrite frobenius_sqr; apply: le_trans (ler_norm _) _.
exact: mxdot_le_nuclear.
Qed.

Lemma frobenius_le_nuclear m n (A : 'M[R]_(m, n)) : frobenius A <= nuclear A.
Proof.
have h := frobenius_sqr_le_nuclear A.
have h2 := opnorm_le_frobenius A.
have [->|f0] := eqVneq (frobenius A) 0; first exact: nuclear_ge0.
have fp : 0 < frobenius A by rewrite lt_def f0 frobenius_ge0.
rewrite -(ler_pM2l fp) -expr2; apply: le_trans h _.
by rewrite ler_wpM2r ?nuclear_ge0.
Qed.

Lemma nuclear_le_frobenius m n (A : 'M[R]_(m, n)) :
  nuclear A <= Num.sqrt n%:R * frobenius A.
Proof.
apply: nuclear_le => B B1; apply: le_trans (ler_mxdot A B) _.
rewrite mulrC; apply: ler_wpM2r; first exact: frobenius_ge0.
apply: le_trans (frobenius_le_opnorm B) _.
by rewrite -[leRHS]mulr1 ler_wpM2l ?sqrtr_ge0.
Qed.

Lemma nuclear_eq0 m n (A : 'M[R]_(m, n)) : (nuclear A == 0) = (A == 0).
Proof.
apply/eqP/eqP => [h|->]; last first.
  by apply/le_anti; rewrite nuclear_ge0 andbT; apply: nuclear_le => B _; rewrite mxdot0l.
apply/eqP; rewrite -frobenius_eq0; apply/eqP/le_anti.
by rewrite frobenius_ge0 andbT -h frobenius_le_nuclear.
Qed.

(* nuclear (x x^T) = |x|^2. *)
Lemma nuclear_outer n (x : 'cV[R]_n) : nuclear (x *m x^T) = frobenius x ^+ 2.
Proof.
have e B : mxdot (x *m x^T) B = mxdot x (B *m x).
  by rewrite mxdotC mxdot_outer mxdot_colE mulmxA.
apply/le_anti/andP; split.
  apply: nuclear_le => B B1; rewrite e; apply: le_trans (ler_norm _) _.
  apply: le_trans (mxdot_opnorm _ _ _) _.
  by rewrite -mulrA -expr2 -[leRHS]mul1r ler_wpM2r ?exprn_ge0 ?frobenius_ge0.
have I1 : opnorm (1%:M : 'M[R]_n) <= 1.
  by apply/opnorm_leP => // y; rewrite mul1mx mul1r.
by apply: le_trans (nuclear_ub _ I1); rewrite e mul1mx frobenius_sqr.
Qed.

(* For a symmetric matrix, the sum of the absolute values of the
   eigenvalues. *)
Lemma nuclear_spectral n (A P : 'M[R]_n) (d : 'rV[R]_n) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  nuclear A = \sum_i `|d 0 i|.
Proof.
move=> Po AE.
have Asym : A \is symmetricmx.
  rewrite AE -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
(* <A, B> = sum_i (P B P^T)_ii d_i *)
have E B : mxdot A B = \sum_i (P *m B *m P^T) i i * d 0 i.
  rewrite mxdotC mxdot_trace; have /symmetricmxP -> := Asym.
  rewrite AE mulmxA mulmxA mxtrace_mulC !mulmxA.
  by apply: eq_bigr => i _; rewrite mul_mx_diag mxE.
apply/le_anti/andP; split.
  apply: nuclear_le => B B1; rewrite E.
  apply: ler_sum => i _; apply: le_trans (ler_norm _) _.
  rewrite normrM mulrC -[leRHS]mulr1 ler_wpM2l //.
  have e1 : frobenius (delta_mx i 0 : 'cV[R]_n) = 1.
    by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1.
  have := mxdot_delta_opnorm (P *m B *m P^T) i i; rewrite e1 !mulr1.
  rewrite opnorm_orthogonalmxr ?trmx_orthogonal// opnorm_orthogonalmxl// => h.
  exact: le_trans h B1.
(* the supremum is attained at P^T diag (sign d_i) P *)
pose s : 'rV[R]_n := \row_i (if 0 <= d 0 i then 1 else -1).
have s1 i : `|s 0 i| <= 1.
  by rewrite mxE; case: ifP; rewrite ?normrN normr1.
have sd i : s 0 i * d 0 i = `|d 0 i|.
  rewrite mxE; case: ifP => h; first by rewrite mul1r ger0_norm.
  by rewrite mulN1r ltr0_norm // ltNge h.
pose B := P^T *m diag_mx s *m P.
have B1 : opnorm B <= 1.
  rewrite (opnorm_spectral Po (erefl B)).
  by apply/bigmax_leP; split => // i _; exact: s1.
apply: le_trans (nuclear_ub A B1); rewrite E.
have PP : P *m P^T = 1%:M by have /orthogonalmxP -> := Po.
have -> : P *m B *m P^T = diag_mx s.
  by rewrite /B !mulmxA PP mul1mx -mulmxA PP mulmx1.
by apply: ler_sum => i _; rewrite mxE eqxx mulr1n sd.
Qed.

(* The supremum for a symmetric matrix is attained on the symmetric
   matrices. *)
Lemma nuclear_sym n (A : 'M[R]_n) (b : R) : A \is symmetricmx ->
  (forall B : 'M[R]_n, B \is symmetricmx -> opnorm B <= 1 -> mxdot A B <= b) ->
  nuclear A <= b.
Proof.
move=> Asym h; apply: nuclear_le => B B1.
(* <A, B> = <A, (B + B^T)/2> and opnorm ((B + B^T)/2) <= 1 *)
pose C := 2^-1 *: (B + B^T).
have Csym : C \is symmetricmx.
  by apply/symmetricmxP; rewrite /C linearZ /= linearD /= trmxK addrC.
have C1 : opnorm C <= 1.
  rewrite /C opnormZ ger0_norm ?invr_ge0 ?ler0n//.
  apply: le_trans (ler_wpM2l _ (opnormD _ _)) _; first by rewrite invr_ge0 ler0n.
  rewrite opnorm_trmx.
  have -> : 2^-1 * (opnorm B + opnorm B) = opnorm B :> R by field.
  exact: B1.
have -> : mxdot A B = mxdot A C.
  rewrite /C mxdotZr mxdotDr.
  have -> : mxdot A B^T = mxdot A B.
    by rewrite -mxdot_trmx trmxK; have /symmetricmxP -> := Asym.
  by field.
exact: h.
Qed.

End nuclear.

Section range_duality.
Variable R : realType.
Variables (k n : nat) (W : 'I_k -> 'M[R]_n).

(* L D = (<W_i, D>)_i and its adjoint L^* l = sum_i l_i W_i. *)
Definition coef_map (D : 'M[R]_n) : 'rV[R]_k := \row_i mxdot (W i) D.

Definition coef_adj (l : 'rV[R]_k) : 'M[R]_n := \sum_i l 0 i *: W i.

Lemma mxdot_coef_map (l : 'rV[R]_k) (D : 'M[R]_n) :
  mxdot l (coef_map D) = mxdot (coef_adj l) D.
Proof.
rewrite /coef_adj mxdot_suml [LHS]/mxdot big_ord1; apply: eq_bigr => i _.
by rewrite mxE mxdotZl.
Qed.

Lemma mxdot_vec_mxr m p (A : 'M[R]_(m, p)) (v : 'rV[R]_(m * p)) :
  mxdot A (vec_mx v) = mxdot (mxvec A) v.
Proof.
rewrite /mxdot [in RHS]big_ord1 [in LHS]pair_bigA /=.
rewrite [in RHS](reindex (uncurry (@mxvec_index m p))) /=.
  exact: curry_mxvec_bij.
by apply: eq_bigr => -[i j] _; rewrite !mxE mxvecE.
Qed.

(* Lemma 2.2 of Koehler and Sohn: if |<l, y>| <= M nuclear (L^* l) for
   every l, then y = L D for some D with opnorm D <= M. *)
Theorem range_duality (y : 'rV[R]_k) (M : R) : 0 <= M ->
  (forall l : 'rV[R]_k, `|mxdot l y| <= M * nuclear (coef_adj l)) ->
  exists2 D : 'M[R]_n, opnorm D <= M & coef_map D = y.
Proof.
move=> M0 hy.
(* S = {L D | opnorm D <= M}, seen through vec_mx as the image of the
   compact set T of 'rV_(n * n) under v |-> v *m Wm *)
pose T := [set v : 'rV[R]_(n * n) | opnorm (vec_mx v) <= M].
pose Wm : 'M[R]_(n * n, k) := \matrix_(j, i) mxvec (W i) 0 j.
have cmE v : coef_map (vec_mx v) = v *m Wm.
  apply/rowP => i; rewrite !mxE mxdot_vec_mxr /mxdot big_ord1.
  by apply: eq_bigr => j _; rewrite !mxE mulrC.
have key (v : 'rV[R]_(n * n)) (a b : 'cV[R]_n) :
    mxdot a (vec_mx v *m b) = mxdot v (mxvec (a *m b^T)).
  by rewrite [RHS]mxdotC -mxdot_vec_mxr [RHS]mxdotC mxdot_outer mxdot_colE mulmxA.
have cdot (c : 'rV[R]_(n * n)) :
    continuous (fun v : 'rV[R]_(n * n) => mxdot v c).
  move=> v; have -> : (fun v : 'rV[R]_(n * n) => mxdot v c) =
      (fun N : 'M[R]_(1, 1) => N 0 0) \o (fun v => v *m c^T).
    by apply/funext => w /=; rewrite mxdot_rowE.
  apply: continuous_comp; first exact: continuous_mulmxr.
  exact: matrix_normedtype.coord_continuous.
have Tcl : closed T.
  have -> : T = \bigcap_(ab in [set: 'cV[R]_n * 'cV[R]_n])
      [set v | `|mxdot v (mxvec (ab.1 *m ab.2^T))| <=
               M * frobenius ab.1 * frobenius ab.2].
    apply/seteqP; split => v.
      move=> Tv [a b] _ /=; rewrite -key.
      exact: (opnorm_bilinearP (vec_mx v) M0).2 Tv a b.
    move=> h; apply/(opnorm_bilinearP (vec_mx v) M0) => a b; rewrite key.
    exact: (h (a, b) I).
  apply: closed_bigI => ab _.
  have cn : continuous (fun v : 'rV[R]_(n * n) =>
      `|mxdot v (mxvec (ab.1 *m ab.2^T))|).
    move=> v; apply: (continuous_comp (f := fun v : 'rV[R]_(n * n) =>
      mxdot v (mxvec (ab.1 *m ab.2^T))) (g := Num.norm)).
      exact: cdot.
    exact: norm_continuous.
  exact: (continuous_closedP _).1 cn _ (@closed_le _ _).
have frobE (v : 'rV[R]_(n * n)) : frobenius (vec_mx v) = frobenius v.
  by rewrite /frobenius mxdot_vec_mxr vec_mxK.
have Tc : compact T.
  apply: bounded_closed_compact => //.
  exists (Num.sqrt n%:R * M); split; first exact: num_real.
  move=> M' M'1 w /= Tw; apply: le_trans (ltW M'1).
  rewrite [leLHS]/Num.Def.normr /= (le_trans (mx_norm_le_frobenius w)) //.
  rewrite -frobE; apply: le_trans (frobenius_le_opnorm _) _.
  by rewrite ler_wpM2l ?sqrtr_ge0.
pose S := [set v *m Wm | v in T].
have Scl : closed S.
  apply: compact_closed; first exact: norm_hausdorff.
  apply: continuous_compact Tc.
  exact: continuous_subspaceT (@continuous_mulmxr _ _ _ _ Wm).
have T0 : T 0 by rewrite /T /= linear0 opnorm0.
have S0 : S !=set0 by exists (0 *m Wm); exists 0.
have Scvx (a b : 'rV[R]_k) (t : R) :
    S a -> S b -> 0 <= t <= 1 -> S (a + t *: (b - a)).
  move=> [v Tv <-] [w Tw <-] /andP[t0 t1].
  exists (v + t *: (w - v)); last by rewrite mulmxDl -scalemxAl mulmxBl.
  rewrite /T /= linearD linearZ linearB /=.
  have -> : vec_mx v + t *: (vec_mx w - vec_mx v) =
      (1 - t) *: vec_mx v + t *: vec_mx w.
    by rewrite scalerBr scalerBl scale1r addrA addrAC.
  apply: le_trans (opnormD _ _) _; rewrite !opnormZ !ger0_norm ?subr_ge0 //.
  have t1' : 0 <= 1 - t by rewrite subr_ge0.
  have := ler_wpM2l t1' Tv; have := ler_wpM2l t0 Tw.
  move=> h1 h2; apply: le_trans (lerD h2 h1) _.
  by rewrite -mulrDl subrK mul1r.
(* y is its own nearest point p in S *)
have [Sp Svar] := projP Scl S0 Scvx y.
set p := proj S y in Sp Svar.
suff yp : y = p.
  case: Sp => v Tv vp; exists (vec_mx v) => //.
  by rewrite cmE vp yp.
pose l := y - p.
have h1 (D : 'M[R]_n) : opnorm D <= M -> mxdot l (coef_map D) <= mxdot l p.
  move=> DM; have SD : S (coef_map D).
    exists (mxvec D); first by rewrite /T /= mxvecK.
    by rewrite -cmE mxvecK.
  by have := Svar _ SD; rewrite mxdotBr subr_le0.
have cm0 : coef_map 0 = 0 by apply/rowP => i; rewrite !mxE mxdot0r.
have h0 : 0 <= mxdot l p.
  by have := h1 0; rewrite opnorm0 cm0 mxdot0r => ->.
have cmZ (a : R) (D : 'M[R]_n) : coef_map (a *: D) = a *: coef_map D.
  by apply/rowP => i; rewrite !mxE mxdotZr.
(* M nuclear (L^* l) <= <l, p> *)
have h2 : M * nuclear (coef_adj l) <= mxdot l p.
  have [->|Mn] := eqVneq M 0; first by rewrite mul0r.
  have Mp : 0 < M by rewrite lt_def Mn M0.
  rewrite mulrC -ler_pdivlMr //; apply: nuclear_le => B B1.
  rewrite -mxdot_coef_map ler_pdivlMr // mulrC -mxdotZr -cmZ.
  apply: h1; rewrite opnormZ ger0_norm //.
  by rewrite -[leRHS]mulr1 ler_wpM2l.
have h3 : mxdot l y = mxdot l p + mxdot l l.
  by rewrite -mxdotDr; congr (mxdot l _); rewrite /l addrC subrK.
have := hy l; rewrite h3 => h.
have ll : mxdot l l <= 0.
  have := le_trans (ler_norm _) (le_trans h h2).
  by rewrite -[X in _ <= X]addr0 lerD2l.
by apply/eqP; rewrite -subr_eq0 -/l -mxdot_eq0 eq_le ll mxdot_ge0.
Qed.

(* With symmetric W_i, the preimage can be taken symmetric. *)
Corollary range_duality_sym (y : 'rV[R]_k) (M : R) : 0 <= M ->
  (forall i, W i \is symmetricmx) ->
  (forall l : 'rV[R]_k, `|mxdot l y| <= M * nuclear (coef_adj l)) ->
  exists2 D : 'M[R]_n, D \is symmetricmx & opnorm D <= M /\ coef_map D = y.
Proof.
move=> M0 Ws hy; have [D DM DE] := range_duality M0 hy.
(* the symmetric part (D + D^T)/2 has the same image and a smaller norm *)
pose C := 2^-1 *: (D + D^T).
exists C.
  by apply/symmetricmxP; rewrite /C linearZ /= linearD /= trmxK addrC.
split.
  rewrite /C opnormZ ger0_norm ?invr_ge0 ?ler0n//.
  apply: le_trans (ler_wpM2l _ (opnormD _ _)) _; first by rewrite invr_ge0 ler0n.
  rewrite opnorm_trmx.
  have -> : 2^-1 * (opnorm D + opnorm D) = opnorm D :> R by field.
  exact: DM.
rewrite -DE; apply/rowP => i; rewrite !mxE /C mxdotZr mxdotDr.
have -> : mxdot (W i) D^T = mxdot (W i) D.
  by rewrite -mxdot_trmx trmxK; have /symmetricmxP -> := Ws i.
by field.
Qed.

End range_duality.
