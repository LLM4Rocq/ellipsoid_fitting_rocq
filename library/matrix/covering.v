From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions archimedean.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.comparison Require Import gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_concentration slepian.
From GaussianAnalysis.comparison Require Import gordon escape sudakov.

(**md**************************************************************************)
(* # Covering the nuclear-norm ball by products of column balls               *)
(*                                                                            *)
(* Lemma 3.10 of Koehler and Sohn (arXiv 2608.27372, lines 2880-2953): for    *)
(* c0 d <= m, q <= C0 d, the m x q matrices of nuclear norm at most gam d     *)
(* are covered by C^(m q) translates of the product of q Euclidean balls of   *)
(* radius gam, one for each column, with C depending on c0 and C0 only. The   *)
(* paper bounds the volume of the nuclear-norm ball by Urysohn's inequality.  *)
(* Here the covering number is bounded in two steps (dual_ball_covering), for *)
(* G = vec_mx g with g of law gauss (m * q):                                  *)
(* - Sudakov's minoration (sudakov.v) covers the set K by Frobenius balls of  *)
(*   radius lam = sqrt (r gam), since E max over K of <G, A> is at most       *)
(*   r E opnorm G <= r (sqrt m + sqrt q) (escape.v);                          *)
(* - the dual Sudakov inequality covers each such ball by products of column  *)
(*   balls of radius gam, since E colmax G <= E opnorm G.                     *)
(* The nuclear norm enters only through the duality <A, B> <= r opnorm B, so  *)
(* the results hold for every set K with this property.                       *)
(* - dual_ball_covering: for m, q > 0, r, gam > 0 and K with                  *)
(*   <A, B> <= r opnorm B for every A in K and every B, there are at most     *)
(*   exp (48 (m + q) r / gam + 33) matrices such that every A in K is within  *)
(*   gam of one of them for colmax.                                           *)
(* - product_covering (Lemma 3.10): with r = gam d, d > 0, c0 > 0 and         *)
(*   c0 d <= m, q <= C0 d, at most exp ((96 C0 + 33) / c0^2) ^ (m q) of them. *)
(*                                                                            *)
(* ```                                                                        *)
(*   colmax A == max_j |A e_j|, the largest Euclidean norm of a column of A,  *)
(*               the norm of A from l^1 to l^2                                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section colmax.
Context {R : realType} {m q : nat}.
Implicit Types A B : 'M[R]_(m, q).

(* The largest Euclidean norm of a column, the norm of A as an operator from
   l^1 to l^2. *)
Definition colmax A : R := \big[maxr/0]_(j < q) frobenius (col j A).

Lemma colmax_ge0 A : 0 <= colmax A.
Proof.
rewrite /colmax; elim/big_ind: _ => // [x y hx hy|j _].
  by rewrite le_max hx.
exact: frobenius_ge0.
Qed.

Lemma colmax_col A j : frobenius (col j A) <= colmax A.
Proof. exact: (le_bigmax _ _ j). Qed.

Lemma colmax_le A c : 0 <= c -> (forall j, frobenius (col j A) <= c) ->
  colmax A <= c.
Proof. by move=> c0 h; apply: bigmax_le => // j _; exact: h. Qed.

Lemma colmaxN A : colmax (- A) = colmax A.
Proof. by apply: eq_bigr => j _; rewrite linearN /= frobeniusN. Qed.

Lemma colmaxD A B : colmax (A + B) <= colmax A + colmax B.
Proof.
apply: colmax_le => [|j]; first by rewrite addr_ge0 // colmax_ge0.
rewrite linearD /=; apply: le_trans (frobeniusD _ _) _.
by apply: lerD; exact: colmax_col.
Qed.

Lemma colmaxZ (c : R) A : 0 <= c -> colmax (c *: A) = c * colmax A.
Proof.
move=> c0; rewrite /colmax.
rewrite (big_morph (fun x : R => c * x) (fun y z => maxr_pMr y z c0) (mulr0 c)).
by apply: eq_bigr => j _; rewrite linearZ /= frobeniusZ ger0_norm.
Qed.

Lemma colmax_le_opnorm A : colmax A <= opnorm A.
Proof.
apply: colmax_le => [|j]; first exact: opnorm_ge0.
rewrite colE; apply: le_trans (frobenius_mulmx_opnorm _ _) _.
rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1 mulr1 //.
Qed.

Lemma colmax_le_frobenius A : colmax A <= frobenius A.
Proof. exact: le_trans (colmax_le_opnorm A) (opnorm_le_frobenius A). Qed.

Lemma colmax_lipschitz A B : `|colmax A - colmax B| <= colmax (A - B).
Proof.
have h (X Y : 'M[R]_(m, q)) : colmax X - colmax Y <= colmax (X - Y).
  by rewrite lerBlDr -{1}(subrK Y X) colmaxD.
have h1 := h A B; have h2 := h B A.
have e : B - A = - (A - B) by rewrite opprB.
rewrite e colmaxN in h2.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

End colmax.

Section dual_ball_covering.
Context {R : realType} {m q : nat}.

Let mxdot_vec_mx (g : 'rV[R]_(m * q)) (A : 'M[R]_(m, q)) :
  mxdot (vec_mx g) A = mxdot g (mxvec A).
Proof.
rewrite /mxdot big_ord1 sum_mxvec_index; apply: eq_bigr => i _.
by apply: eq_bigr => j _; rewrite mxvecE !mxE.
Qed.

Let frobenius_mxvec_mx (A : 'M[R]_(m, q)) :
  frobenius (mxvec A) = frobenius A.
Proof. by rewrite -[in RHS](mxvecK A) frobenius_vec_mx. Qed.

(* E opnorm G <= sqrt m + sqrt q, for G = vec_mx g of law gauss (m * q). *)
Let gopnorm_mean : (0 < m)%N -> (0 < q)%N ->
  \int[gauss (m * q)]_g colmax (vec_mx g : 'M[R]_(m, q)) <=
  Num.sqrt m%:R + Num.sqrt q%:R.
Proof.
move=> m0 q0; apply: le_trans (gauss_opnorm_mean_sqrt m0 q0).
have L1 (F : 'M[R]_(m, q) -> R) :
    (forall A B, `|F A - F B| <= frobenius (A - B)) ->
    (gauss (m * q)).-integrable setT
      (EFin \o (fun g : 'rV[R]_(m * q) => F (vec_mx g))).
  move=> FL; apply: (@integrable_gauss_lipschitz _ _ _ 1) => g g'.
  by rewrite mul1r (le_trans (FL _ _)) // -linearB /= frobenius_vec_mx.
apply: le_Rintegral => //.
- apply: L1 => A B; apply: le_trans (colmax_lipschitz _ _) _.
  exact: colmax_le_frobenius.
- exact: integrable_gauss_opnorm.
- by move=> g _; exact: colmax_le_opnorm.
Qed.

Let colmax0 : colmax (0 : 'M[R]_(m, q)) = 0.
Proof.
by have := colmaxZ (0 : 'M[R]_(m, q)) (lexx 0); rewrite scale0r mul0r.
Qed.

Let frob_sep (K : set 'M[R]_(m, q)) (r lam : R) (s : seq 'M[R]_(m, q)) :
  (0 < m)%N -> (0 < q)%N -> 0 <= r -> 0 < lam ->
  (forall A, K A -> forall B, mxdot A B <= r * opnorm B) ->
  separated (fun A B => frobenius (A - B)) K lam s ->
  (size s)%:R <=
  expR ((2 * Num.sqrt 2 * r * (Num.sqrt m%:R + Num.sqrt q%:R) / lam + 4) ^+ 2).
Proof.
move=> m0 q0 r0 l0 hK [us sK ssep].
set a := Num.sqrt m%:R + Num.sqrt q%:R.
case: s us sK ssep => [|A0 s'] us sK ssep; first by rewrite /= expR_ge0.
set k := size s'.
pose xs (i : 'I_k.+1) := mxvec (nth A0 (A0 :: s') i).
have hsep i j : i != j -> lam <= frobenius (xs i - xs j).
  move=> ij; rewrite /xs -linearB /= frobenius_mxvec_mx.
  apply: ltW; apply: ssep; rewrite ?mem_nth //.
  by rewrite nth_uniq.
have hS := sudakov_minoration (ltW l0) hsep.
pose Am : 'M[R]_(m * q, k.+1) := \matrix_(j, i) xs i 0 j.
have rowA (g : 'rV[R]_(m * q)) : \row_i mxdot g (xs i) = g *m Am.
  apply/rowP => i; rewrite !mxE /mxdot big_ord1; apply: eq_bigr => j _.
  by rewrite !mxE.
have iO := @integrable_gauss_opnorm R m q.
have hE : \int[gauss (m * q)]_g rmax (\row_i mxdot g (xs i)) <= r * a.
  apply: (@le_trans _ _
    (\int[gauss (m * q)]_g (r * opnorm (vec_mx g : 'M[R]_(m, q))))).
    apply: le_Rintegral => //.
    - have := integrable_gauss_rmax Am.
      by apply: eq_integrable => // g _; rewrite /= rowA.
    - have := integrableZl measurableT r iO.
      by apply: eq_integrable => // g _.
    - move=> g _; apply: rmax_le => i; rewrite mxE /xs -mxdot_vec_mx mxdotC.
      apply: hK; have := sK _ (@mem_nth _ A0 (A0 :: s') i (ltn_ord i)).
      by rewrite inE.
  rewrite RintegralZl //; apply: ler_wpM2l => //.
  exact: gauss_opnorm_mean_sqrt.
have s2 : 0 < Num.sqrt 2 :> R by rewrite sqrtr_gt0.
have hl : Num.sqrt (ln k.+1%:R) <= 2 * Num.sqrt 2 * r * a / lam + 4.
  have h1 : lam * (Num.sqrt (ln k.+1%:R) / 2 - 2) <= Num.sqrt 2 * (r * a).
    exact: le_trans hS (ler_wpM2l (ltW s2) hE).
  have h2 : Num.sqrt (ln k.+1%:R) / 2 - 2 <= Num.sqrt 2 * (r * a) / lam.
    by rewrite ler_pdivlMr // mulrC.
  have -> : 2 * Num.sqrt 2 * r * a / lam = 2 * (Num.sqrt 2 * (r * a) / lam).
    by rewrite !mulrA.
  by lra.
have ln0 : 0 <= ln k.+1%:R :> R by rewrite ln_ge0 // ler1n.
have hln : ln k.+1%:R <= (2 * Num.sqrt 2 * r * a / lam + 4) ^+ 2.
  rewrite -(sqr_sqrtr ln0); apply: lerXn2r; rewrite ?nnegrE ?sqrtr_ge0 //.
  by apply: le_trans (sqrtr_ge0 _) hl.
by rewrite -(lnK (_ : k.+1%:R \is Num.pos)) ?posrE ?ltr0n // ler_expR.
Qed.

Let colmax_sep (lam gam : R) (s : seq 'M[R]_(m, q)) :
  (0 < m)%N -> (0 < q)%N -> 0 < gam ->
  separated (fun A B => colmax (A - B)) [set B | frobenius B <= lam] gam s ->
  (size s)%:R <=
  2 * expR (8 * lam ^+ 2 * (Num.sqrt m%:R + Num.sqrt q%:R) ^+ 2 / gam ^+ 2).
Proof.
move=> m0 q0 g0 [us sK ssep].
set a := Num.sqrt m%:R + Num.sqrt q%:R.
have a0 : 0 < a by rewrite ltr_wpDr ?sqrtr_ge0 // sqrtr_gt0 ltr0n.
case: s us sK ssep => [|A0 s'] us sK ssep.
  by rewrite /= mulr_ge0 ?expR_ge0.
set k := size s'.
pose xs (i : 'I_k.+1) := mxvec (nth A0 (A0 :: s') i).
pose nrm (v : 'rV[R]_(m * q)) := colmax (vec_mx v : 'M[R]_(m, q)).
have nL v w : `|nrm v - nrm w| <= 1 * frobenius (v - w).
  rewrite mul1r; apply: le_trans (colmax_lipschitz _ _) _.
  by rewrite -linearB /= -frobenius_vec_mx colmax_le_frobenius.
have := @dual_sudakov R (m * q) nrm lam gam a k xs.
apply.
- exact: continuous_measurable_mx (lipschitz_frobenius_continuous nL).
- by move=> v; rewrite /nrm linearN /= colmaxN.
- by move=> v w; rewrite /nrm linearD /= colmaxD.
- by move=> c v c0; rewrite /nrm linearZ /= colmaxZ.
- exact: integrable_gauss_lipschitz nL.
- by [].
- by [].
- exact: gopnorm_mean.
- move=> i; rewrite /xs frobenius_mxvec_mx.
  by have := sK _ (@mem_nth _ A0 (A0 :: s') i (ltn_ord i)); rewrite inE.
- move=> i j ij; rewrite /nrm /xs -linearB /= mxvecK.
  by apply: ssep; rewrite ?mem_nth // nth_uniq.
Qed.

(* Covering a set K of matrices on which every linear form is bounded by r
   times the operator norm (a set contained in the ball of radius r of the
   nuclear norm) by products of Euclidean balls of radius gam, one for each
   column: at most exp (48 (m + q) r / gam + 33) of them suffice. *)
Theorem dual_ball_covering (K : set 'M[R]_(m, q)) (r gam : R) :
  (0 < m)%N -> (0 < q)%N -> 0 < r -> 0 < gam ->
  (forall A, K A -> forall B, mxdot A B <= r * opnorm B) ->
  exists N : seq 'M[R]_(m, q),
    (size N)%:R <= expR (48 * (m + q)%:R * r / gam + 33) /\
    forall A, K A -> exists2 B, B \in N & colmax (A - B) <= gam.
Proof.
move=> m0 q0 r0 g0 hK.
pose a : R := Num.sqrt m%:R + Num.sqrt q%:R.
have a0 : 0 < a by rewrite ltr_wpDr ?sqrtr_ge0 // sqrtr_gt0 ltr0n.
have a2 : a ^+ 2 <= 2 * (m + q)%:R.
  have := sqr_ge0 (Num.sqrt m%:R - Num.sqrt q%:R :> R).
  have um : Num.sqrt m%:R ^+ 2 = m%:R :> R by rewrite sqr_sqrtr // ler0n.
  have uq : Num.sqrt q%:R ^+ 2 = q%:R :> R by rewrite sqr_sqrtr // ler0n.
  by rewrite /a natrD => h; nra.
pose lam : R := Num.sqrt (r * gam).
have rg : 0 < r * gam by rewrite mulr_gt0.
have l0 : 0 < lam by rewrite sqrtr_gt0.
have l2 : lam ^+ 2 = r * gam by rewrite sqr_sqrtr // ltW.
(* a lam-net of K in the Frobenius distance, by Sudakov's minoration *)
pose M1 : R := expR ((2 * Num.sqrt 2 * r * a / lam + 4) ^+ 2).
have dsym (A B : 'M[R]_(m, q)) : frobenius (A - B) = frobenius (B - A).
  by rewrite -frobeniusN opprB.
have drefl (A : 'M[R]_(m, q)) : frobenius (A - A) <= lam.
  by rewrite subrr frobenius0 ltW.
have hM1 s : separated (fun A B : 'M[R]_(m, q) => frobenius (A - B)) K lam s ->
    (size s <= truncn M1)%N.
  move=> hs; rewrite truncn_ge_nat ?expR_ge0 //.
  exact: frob_sep (ltW r0) l0 hK hs.
have [N1 [N1K N1s N1net]] := separated_net dsym drefl hM1.
(* a gam-net of the Frobenius ball of radius lam in colmax, by the dual
   Sudakov inequality *)
have csym (A B : 'M[R]_(m, q)) : colmax (A - B) = colmax (B - A).
  by rewrite -colmaxN opprB.
have crefl (A : 'M[R]_(m, q)) : colmax (A - A) <= gam.
  by rewrite subrr colmax0 ltW.
pose M2 : R := 2 * expR (8 * lam ^+ 2 * a ^+ 2 / gam ^+ 2).
have hM2 s : separated (fun A B : 'M[R]_(m, q) => colmax (A - B))
    [set B | frobenius B <= lam] gam s -> (size s <= truncn M2)%N.
  move=> hs; rewrite truncn_ge_nat ?mulr_ge0 ?expR_ge0 //.
  exact: colmax_sep.
have [N2 [N2F N2s N2net]] := separated_net csym crefl hM2.
(* the sums of the two nets *)
exists [seq A + B | A <- N1, B <- N2]; split; last first.
  move=> A KA; have [B1 B1N hB1] := N1net A KA.
  have [B2 B2N hB2] := N2net (A - B1) hB1.
  exists (B1 + B2); first exact: allpairs_f.
  by rewrite opprD addrA.
have hs1 : (size N1)%:R <= M1.
  apply: le_trans (_ : (truncn M1)%:R <= M1); first by rewrite ler_nat.
  by rewrite truncn_le expR_ge0.
have hs2 : (size N2)%:R <= M2.
  apply: le_trans (_ : (truncn M2)%:R <= M2); first by rewrite ler_nat.
  by rewrite truncn_le mulr_ge0 ?expR_ge0.
rewrite size_allpairs natrM.
apply: le_trans (ler_pM (ler0n _ _) (ler0n _ _) hs1 hs2) _.
have rne : r != 0 by rewrite gt_eqF.
have gne : gam != 0 by rewrite gt_eqF.
have lne : lam != 0 by rewrite gt_eqF.
set Z := r * a ^+ 2 / gam.
have t2 : (2 * Num.sqrt 2 * r * a / lam) ^+ 2 = 8 * Z.
  by rewrite /Z !exprMn exprVn sqr_sqrtr // l2; field.
have X1le : (2 * Num.sqrt 2 * r * a / lam + 4) ^+ 2 <= 2 * (8 * Z) + 32.
  have := sqr_ge0 (2 * Num.sqrt 2 * r * a / lam - 4); move: t2.
  by set t := 2 * Num.sqrt 2 * r * a / lam => t2 h; nra.
have X2E : 8 * lam ^+ 2 * a ^+ 2 / gam ^+ 2 = 8 * Z by rewrite /Z l2; field.
have ra : Z <= 2 * (m + q)%:R * r / gam.
  rewrite /Z -!mulrA !(mulrCA _ r) ler_pM2l //.
  by rewrite !mulrA -expr2 ler_pM2r ?invr_gt0.
rewrite /M1 /M2 mulrCA -expRD X2E.
apply: le_trans (_ : 2 * expR (48 * (m + q)%:R * r / gam + 32) <= _).
  by rewrite ler_wpM2l // ler_expR; lra.
have e1 : 2 <= expR 1 :> R by have := expR_ge1Dx (1 : R); lra.
have e33 : 48 * (m + q)%:R * r / gam + 33 =
  (48 * (m + q)%:R * r / gam + 32) + 1 by lra.
rewrite e33 [X in _ <= X]expRD [X in _ <= X]mulrC.
by apply: ler_wpM2r; [exact: expR_ge0|exact: e1].
Qed.

(* Lemma 3.10 of Koehler and Sohn: when c0 d <= m, q <= C0 d, the matrices
   of nuclear norm at most gam d (written by duality with opnorm) are covered
   by C^(m q) products of column balls of radius gam, with
   C = exp ((96 C0 + 33) / c0^2). *)
Corollary product_covering (c0 C0 gam : R) (d : nat) (K : set 'M[R]_(m, q)) :
  0 < c0 -> (0 < d)%N -> 0 < gam ->
  c0 * d%:R <= m%:R -> c0 * d%:R <= q%:R ->
  m%:R <= C0 * d%:R -> q%:R <= C0 * d%:R ->
  (forall A, K A -> forall B, mxdot A B <= gam * d%:R * opnorm B) ->
  exists N : seq 'M[R]_(m, q),
    (size N)%:R <= expR ((96 * C0 + 33) / c0 ^+ 2) ^+ (m * q) /\
    forall A, K A -> exists2 B, B \in N & colmax (A - B) <= gam.
Proof.
move=> c00 d0 g0 cm cq mC qC hK.
set D := d%:R : R; set Mr := m%:R : R; set Qr := q%:R : R.
have D1 : 1 <= D by rewrite /D ler1n.
have cD : 0 < c0 * D by rewrite mulr_gt0 // (lt_le_trans ltr01 D1).
have m0 : (0 < m)%N by rewrite -(ltr0n R); exact: lt_le_trans cD cm.
have q0 : (0 < q)%N by rewrite -(ltr0n R); exact: lt_le_trans cD cq.
have r0 : 0 < gam * D by rewrite mulr_gt0 // (lt_le_trans ltr01 D1).
have [N [hN hcov]] := dual_ball_covering m0 q0 r0 g0 hK.
exists N; split => //; apply: le_trans hN _.
rewrite -expRM_natl ler_expR.
have gne : gam != 0 by rewrite gt_eqF.
have -> : 48 * (m + q)%:R * (gam * D) / gam = 48 * ((Mr + Qr) * D).
  by rewrite natrD -/Mr -/Qr; field.
have C00 : 0 < C0.
  have : c0 * D <= C0 * D := le_trans cm mC.
  by rewrite ler_pM2r ?(lt_le_trans ltr01 D1) // => /(lt_le_trans c00).
have h1 : (Mr + Qr) * D <= 2 * C0 * D ^+ 2.
  by rewrite expr2 mulrA ler_pM2r ?(lt_le_trans ltr01 D1) //; lra.
have h2 : 1 <= D ^+ 2 by rewrite -(expr1n _ 2) lerXn2r ?nnegrE // ler01.
have h3 : (c0 * D) ^+ 2 <= Mr * Qr.
  by rewrite expr2; apply: ler_pM => //; exact: ltW.
have c2 : 0 < c0 ^+ 2 by rewrite exprn_gt0.
rewrite natrM -/Mr -/Qr.
apply: le_trans (_ : _ <= (96 * C0 + 33) * D ^+ 2) _; first by lra.
have c0ne : c0 != 0 by rewrite gt_eqF.
have -> : (96 * C0 + 33) * D ^+ 2 = (96 * C0 + 33) / c0 ^+ 2 * (c0 * D) ^+ 2.
  by field.
rewrite [X in _ <= X]mulrC; apply: ler_wpM2l => //.
by rewrite divr_ge0 ?(ltW c2) //; lra.
Qed.

End dual_ball_covering.
