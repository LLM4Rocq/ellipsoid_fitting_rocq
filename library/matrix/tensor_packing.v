From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear archimedean boolp classical_sets.
From mathcomp Require Import functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.matrix Require Import psd_part nets.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.comparison Require Import gauss_concentration slepian.
From GaussianAnalysis.comparison Require Import sudakov.
From GaussianAnalysis.random_matrix Require Import matrix_series.

(**md**************************************************************************)
(* # Tensor packing                                                           *)
(*                                                                            *)
(* Rows x_1, ..., x_m in the unit ball of 'rV[R]_n1 and y_1, ..., y_m in the  *)
(* unit ball of 'rV[R]_n2 are almost orthogonal: |<x_a, x_b>| <= eta and      *)
(* |<y_a, y_b>| <= eta for a != b outside two relations Gx and Gy with at     *)
(* most L successors at every vertex. Then few of the tensors x_a^T y_a of    *)
(* 'M[R]_(n1, n2), with the Frobenius inner product, have a large             *)
(* projection on a subspace of small dimension: if A_1, ..., A_r are          *)
(* Frobenius-orthonormal with r <= d, 0 < eps <= 1, d >= 1 and                *)
(* 0 <= eta <= eps^2 / 10^4, then at most                                     *)
(*   30000 (1 + L) / eps^2 exp (30000 sqrt d ln (2 + d) / eps^2)              *)
(* indices a have sum_k (x_a A_k y_a^T)^2 >= eps^2, the left side being the   *)
(* squared norm of the projection of x_a^T y_a on the span of the A_k.        *)
(*                                                                            *)
(* This file is a Rocq formalization of the credited argument of Theorem      *)
(* 4.1, 'Tensor packing', of 'Pointwise convergence of fourfold ergodic       *)
(* averages for mixing transformations' (OpenAI, 4 October 2026), family      *)
(* 154 of the OpenAI math collection at revision 1581d4cbd                    *)
(* (sections/04-packing.tex). The same theorem is in the section 'Tensor      *)
(* packing' of its companion 'Pointwise Multiple Ergodic Averages for         *)
(* Mixing Transformations'. There is no Lean version. The proof is the        *)
(* manuscript's:                                                              *)
(* - the spectral subspaces E_1 of \sum_k A_k A_k^T and E_2 of                *)
(*   \sum_k A_k^T A_k for the eigenvalues larger than sqrt d have             *)
(*   dimension at most sqrt d, since both traces are r <= d;                  *)
(* - few indices a have a projection of x_a on E_1, or of y_a on E_2, of      *)
(*   norm larger than eps / 10: cover these projections by balls of radius    *)
(*   eps / 40 and apply the cluster bound to each ball;                       *)
(* - for the other indices, the coefficients v_a of x_a^T y_a on the          *)
(*   compressions B_k = Q_1 A_k Q_2, where Q_i projects on the orthogonal     *)
(*   complement of E_i, have norm at least 4 eps / 5, so the clusters         *)
(*   around a maximal eps / 8-separated set J of them have at most            *)
(*   3 (1 + L) / eps^2 indices each;                                          *)
(* - Sudakov's minoration (comparison/sudakov.v) bounds sqrt (ln #|J|) by     *)
(*   a multiple of E opnorm (\sum_k g_k B_k) / eps, and the Gaussian          *)
(*   matrix series bound gauss_mx_series_opnorm_log of                        *)
(*   random_matrix/matrix_series.v bounds this expectation by                 *)
(*   5 d^(1/4) sqrt (ln (2 + d)), since \sum_k B_k B_k^T and                  *)
(*   \sum_k B_k^T B_k have operator norm at most sqrt d and trace at most     *)
(*   d.                                                                       *)
(* The formalization differs from the manuscript in four points:              *)
(* - the dimensions are finite, and the projection of rank at most d is       *)
(*   given by an orthonormal basis A_1, ..., A_r of its range; the            *)
(*   reduction from Hilbert spaces to finite spans and the consequence for    *)
(*   d_m = (1 + log m)^(3/2) are not formalized;                              *)
(* - the relations need not be symmetric, and their degree is the number      *)
(*   of successors;                                                           *)
(* - the clusters of the remaining indices use the relation Gx alone, with    *)
(*   |<x_a^T y_a, x_b^T y_b>| = |<x_a, x_b>| |<y_a, y_b>| <= eta, where the   *)
(*   manuscript uses the union of the two graphs and eta^2;                   *)
(* - the constant is explicit, C = 30000, and the coverings are those of      *)
(*   net_exists (matrix/nets.v), with (2 e (1 + 80 / eps))^k balls in         *)
(*   dimension k where the manuscript has (1 + 80 / eps)^k.                   *)
(*                                                                            *)
(* Proved:                                                                    *)
(* - almost_orthogonal_sum_le, the cluster bound: if <v_a, v_a> <= 1 and      *)
(*   |<v_a, v_b>| <= eta for a != b outside a relation with at most L         *)
(*   successors, then |\sum_(a in S) v_a|^2 <= (1 + L) |S| + eta |S|^2;       *)
(*   almost_orthogonal_card_le: if moreover |\sum_(a in S) v_a| >= rho |S|    *)
(*   with rho >= 0 and rho^2 > eta, then |S| <= (1 + L) / (rho^2 - eta).      *)
(* - large_projection_card: for such columns X_a in the unit ball and V       *)
(*   with orthonormal rows (V V^T = 1) in 'M[R]_(k, n), at most               *)
(*   (2 e (1 + 80 / eps))^k 200 (1 + L) / eps^2 indices have                  *)
(*   |V X_a| > eps / 10, when 0 <= eta <= eps^2 / 10^4.                       *)
(* - bessel_mxdot, Bessel's inequality: \sum_k <Z, A_k>^2 <= <Z, Z> for a     *)
(*   Frobenius-orthonormal family, so the coefficient map mxcoef A is a       *)
(*   contraction (frobenius_mxcoef_le).                                       *)
(* - maximal_separated_subset: every finite set I of indices has a            *)
(*   delta-separated subset J such that every point of I is at distance       *)
(*   less than delta of a point of J.                                         *)
(* - spectral_rowperp_form_le: for P orthogonal and t >= 0, the quadratic     *)
(*   form of P^T diag(e) P on the range of rowperp V, where                   *)
(*   V = select_rows P [set u | t < e_u], is at most t |z|^2.                 *)
(* - opnorm_compress_gram, trace_compress_gram: if the quadratic form of      *)
(*   \sum_k A_k A_k^T on the range of rowperp V1 is at most t |z|^2, with     *)
(*   t >= 0, then the compressions B_k = rowperp V1 A_k rowperp V2 satisfy    *)
(*   opnorm (\sum_k B_k B_k^T) <= t and                                       *)
(*   tr (\sum_k B_k B_k^T) <= \sum_k |A_k|^2.                                 *)
(* - sudakov_mx_series: if the coefficient vectors on B_1, ..., B_r of the    *)
(*   tensors x_i^T y_i of l + 1 pairs of rows in the unit balls are           *)
(*   delta-separated, then for g of law gauss r,                              *)
(*   delta (sqrt (ln (l + 1)) / 2 - 2) <= sqrt 2 E opnorm (\sum_k g_k B_k).   *)
(* - tensor_packing: the theorem, with the constant 30000.                    *)
(*                                                                            *)
(* ```                                                                        *)
(* select_rows P S == the rows of P indexed by the set S, a matrix with       *)
(*                    #|S| rows                                               *)
(*       rowproj V == V^T V, the orthogonal projection on the span of the     *)
(*                    rows of V when V V^T = 1                                *)
(*       rowperp V == 1 - V^T V                                               *)
(*      mxcoef A Z == the row of the inner products <Z, A_k>, k < r           *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Section frobenius_sum.
Context {R : realType} {p q : nat}.

(* The triangle inequality for finite sums. *)
Lemma frobenius_sum_le (I : finType) (P : pred I) (F : I -> 'M[R]_(p, q)) :
  frobenius (\sum_(i | P i) F i) <= \sum_(i | P i) frobenius (F i).
Proof.
elim/big_ind2: _ => [|u a w c hu hw|i _]; first by rewrite frobenius0.
  by apply: le_trans (frobeniusD _ _) _; exact: lerD.
exact: lexx.
Qed.

End frobenius_sum.

Section almost_orthogonal.
Context {R : realType} {m p q : nat}.

(* The cluster bound: unit vectors whose inner products are at most eta
   outside a relation of out-degree at most L have, on every set S,
   |\sum_(a in S) v a|^2 <= (1 + L) |S| + eta |S|^2. *)
Lemma almost_orthogonal_sum_le (v : 'I_m -> 'M[R]_(p, q)) (G : rel 'I_m)
    (L : nat) (eta : R) (S : {set 'I_m}) :
  0 <= eta -> (forall a, mxdot (v a) (v a) <= 1) ->
  (forall a, #|[set b | G a b]| <= L)%N ->
  (forall a b, a != b -> ~~ G a b -> `|mxdot (v a) (v b)| <= eta) ->
  mxdot (\sum_(a in S) v a) (\sum_(a in S) v a) <=
    (1 + L%:R) * #|S|%:R + eta * #|S|%:R ^+ 2.
Proof.
move=> eta0 v1 deg ex.
have f1 a : frobenius (v a) <= 1 by rewrite -sqrtr1 ler_wsqrtr.
have vv a b : `|mxdot (v a) (v b)| <= 1.
  apply: le_trans (mxdot_le _ _) _; rewrite -[1](mulr1 1).
  by apply: ler_pM; rewrite ?frobenius_ge0 ?f1.
rewrite mxdot_suml; under eq_bigr do rewrite mxdot_sumr.
have -> : (1 + L%:R) * #|S|%:R + eta * #|S|%:R ^+ 2 =
    \sum_(a in S) ((1 + L%:R) + eta * #|S|%:R).
  by rewrite sumr_const; move: #|S| => s; rewrite -[_ *+ s]mulr_natr; ring.
apply: ler_sum => a aS.
rewrite (bigID (fun b => (b == a) || G a b)) /=; apply: lerD.
  apply: le_trans (_ : \sum_(b in S | (b == a) || G a b) (1 : R) <= _).
    by apply: ler_sum => b _; apply: le_trans (ler_norm _) (vv a b).
  rewrite sumr_const nat1r ler_nat.
  apply: leq_trans (_ : #|a |: [set b | G a b]| <= _)%N.
    apply: subset_leq_card; apply/fintype.subsetP => b.
    rewrite unfold_in /= !inE => /andP[_].
    by case/orP => [->|->]; rewrite ?orbT.
  by rewrite cardsU1; apply: leq_add (leq_b1 _) (deg a).
apply: le_trans (_ : \sum_(i in S | ~~ ((i == a) || G a i)) eta <= _).
  apply: ler_sum => b /andP [_]; rewrite negb_or => /andP [ba nG].
  by apply: le_trans (ler_norm _) (ex a b _ nG); rewrite eq_sym.
apply: le_trans (_ : \sum_(i in S) eta <= _).
  rewrite [X in _ <= X](bigID (fun i => ~~ ((i == a) || G a i))) /= lerDl.
  by apply: sumr_ge0 => i _.
by rewrite sumr_const mulr_natr.
Qed.

End almost_orthogonal.

Section almost_orthogonal_card.
Context {R : realType} {m p q : nat}.
Variables (T : 'I_m -> 'M[R]_(p, q)) (G : rel 'I_m) (L : nat) (eta : R).
Hypothesis eta0 : 0 <= eta.
Hypothesis T1 : forall a, mxdot (T a) (T a) <= 1.
Hypothesis deg : forall a, (#|[set b | G a b]| <= L)%N.
Hypothesis ex : forall a b, a != b -> ~~ G a b -> `|mxdot (T a) (T b)| <= eta.

(* A set whose sum has norm at least rho times its size, with rho^2 > eta,
   has at most (1 + L) / (rho^2 - eta) elements. *)
Lemma almost_orthogonal_card_le (C : {set 'I_m}) (rho : R) :
  0 <= rho -> eta < rho ^+ 2 ->
  rho * #|C|%:R <= frobenius (\sum_(a in C) T a) ->
  #|C|%:R <= (1 + L%:R) / (rho ^+ 2 - eta).
Proof.
move=> rho0 er hC; set s : R := #|C|%:R.
have s0 : 0 <= s := ler0n _ _.
have L0 : 0 <= L%:R :> R := ler0n _ _.
have h3 := almost_orthogonal_sum_le C eta0 T1 deg ex.
have h4 : (rho * s) ^+ 2 <= mxdot (\sum_(a in C) T a) (\sum_(a in C) T a).
  by rewrite -frobenius_sqr lerXn2r ?nnegrE ?frobenius_ge0 ?mulr_ge0.
have re : 0 < rho ^+ 2 - eta by rewrite subr_gt0.
rewrite ler_pdivlMr //.
have [s00|sp] := eqVneq s 0; first by rewrite s00 mul0r addr_ge0.
have sp' : 0 < s by rewrite lt_def sp s0.
rewrite -(ler_pM2r sp').
move: h3 h4; rewrite -/s; set S2 := mxdot _ _ => h3 h4.
nra.
Qed.

End almost_orthogonal_card.

Section bessel.
Context {R : realType} {p q r : nat}.

(* Bessel's inequality for a Frobenius-orthonormal family. *)
Lemma bessel_mxdot (A : 'I_r -> 'M[R]_(p, q)) (Z : 'M[R]_(p, q)) :
  (forall k l, mxdot (A k) (A l) = (k == l)%:R) ->
  \sum_k mxdot Z (A k) ^+ 2 <= mxdot Z Z.
Proof.
move=> on; pose c k := mxdot Z (A k); pose W := \sum_k c k *: A k.
have ZW : mxdot Z W = \sum_k c k ^+ 2.
  by rewrite /W mxdot_sumr; apply: eq_bigr => k _; rewrite mxdotZr expr2.
have WW : mxdot W W = \sum_k c k ^+ 2.
  rewrite {1}/W mxdot_suml; apply: eq_bigr => k _.
  rewrite mxdotZl /W mxdot_sumr (bigD1 k) //= big1 ?addr0.
    by move=> l lk; rewrite mxdotZr on eq_sym (negbTE lk) mulr0.
  by rewrite mxdotZr on eqxx mulr1 expr2.
have := mxdot_ge0 (Z - W).
rewrite mxdotBl !mxdotBr [mxdot W Z]mxdotC ZW WW -/c.
by move: (mxdot Z Z) (\sum_k c k ^+ 2) => a s; lra.
Qed.

End bessel.

Section isometry.
Context {R : realType} {k n : nat}.
Variable V : 'M[R]_(k, n).
Hypothesis VV : V *m V^T = 1%:M.

(* For V with orthonormal rows, V^T is an isometry and V a contraction. *)
Lemma frobenius_trmx_isometry (w : 'cV[R]_k) :
  frobenius (V^T *m w) = frobenius w.
Proof.
rewrite /frobenius; congr Num.sqrt.
by rewrite mxdot_mulmxl trmxK mulmxA VV mul1mx.
Qed.

Lemma frobenius_isometry_le (z : 'cV[R]_n) : frobenius (V *m z) <= frobenius z.
Proof.
have h : frobenius (V *m z) ^+ 2 <= frobenius z * frobenius (V *m z).
  rewrite frobenius_sqr mxdot_mulmxl.
  apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_le _ _) _.
  by rewrite frobenius_trmx_isometry.
have [->|zp] := eqVneq (frobenius (V *m z)) 0; first exact: frobenius_ge0.
have f0 : 0 < frobenius (V *m z) by rewrite lt_def zp frobenius_ge0.
by rewrite expr2 ler_pM2r in h.
Qed.

End isometry.

Section large_projection.
Context {R : realType} {k n m : nat}.
Variables (V : 'M[R]_(k, n)) (X : 'I_m -> 'cV[R]_n) (G : rel 'I_m).
Variables (L : nat) (eta eps : R).
Hypothesis VV : V *m V^T = 1%:M.
Hypothesis eps0 : 0 < eps.
Hypothesis eta0 : 0 <= eta.
Hypothesis eta_eps : eta <= eps ^+ 2 / 10000.
Hypothesis X1 : forall a, frobenius (X a) <= 1.
Hypothesis deg : forall a, (#|[set b | G a b]| <= L)%N.
Hypothesis ex : forall a b, a != b -> ~~ G a b -> `|mxdot (X a) (X b)| <= eta.

(* A cluster of vectors whose images under V are within eps / 40 of a point
   of norm larger than eps / 10 has at most 200 (1 + L) / eps^2 elements. *)
Lemma large_projection_cluster_card (y : 'cV[R]_k) (C : {set 'I_m}) :
  eps / 10 < frobenius y ->
  (forall a, a \in C -> frobenius (V *m X a - y) <= eps / 40) ->
  #|C|%:R <= 200 * (1 + L%:R) / eps ^+ 2.
Proof.
move=> yb hC.
set s : R := #|C|%:R.
have s0 : 0 <= s by exact: ler0n.
set Sx := \sum_(a in C) X a.
have h1 : frobenius (V *m Sx - s *: y) <= s * (eps / 40).
  rewrite /Sx mulmx_sumr /s scaler_nat -sumr_const -sumrB.
  apply: le_trans (frobenius_sum_le _ _) _; rewrite mulr_natl -sumr_const.
  by apply: ler_sum => a aC; exact: hC.
have h2 : s * (3 * eps / 40) <= frobenius Sx.
  have hz := frobeniusD (s *: y - V *m Sx) (V *m Sx); rewrite subrK in hz.
  rewrite -[frobenius (s *: y - _)]frobeniusN opprB in hz.
  rewrite frobeniusZ ger0_norm // in hz.
  have := frobenius_isometry_le VV Sx.
  have : s * (eps / 10) <= s * frobenius y.
    by apply: ler_wpM2l => //; exact: ltW.
  move: h1 hz; set a := frobenius _; set b := frobenius _.
  by set c := frobenius _; move=> *; nra.
have Xx a : mxdot (X a) (X a) <= 1.
  by rewrite -frobenius_sqr exprn_ile1 ?frobenius_ge0.
have h3 := almost_orthogonal_sum_le C eta0 Xx deg ex.
rewrite -/Sx -/s in h3.
have h4 : (s * (3 * eps / 40)) ^+ 2 <= mxdot Sx Sx.
  rewrite -frobenius_sqr lerXn2r ?nnegrE ?frobenius_ge0 //.
  by rewrite mulr_ge0 // divr_ge0 // mulr_ge0 // ltW.
have L0 : 0 <= L%:R :> R := ler0n _ _.
have [s00|sp] := eqVneq s 0.
  by rewrite s00 !mulr_ge0 ?invr_ge0 ?exprn_ge0 // ?addr_ge0 // ltW.
have sp' : 0 < s by rewrite lt_def sp s0.
have h5 : s * eps ^+ 2 * (9 / 1600 - 1 / 10000) <= 1 + L%:R.
  rewrite -(ler_pM2r sp').
  have e2 : eta * s ^+ 2 <= eps ^+ 2 / 10000 * s ^+ 2.
    by apply: ler_wpM2r => //; exact: sqr_ge0.
  by move: h3 h4 e2; set S2 := mxdot Sx Sx; move=> *; nra.
by rewrite ler_pdivlMr ?exprn_gt0 //; nra.
Qed.

(* The number of vectors whose image under V has norm larger than eps / 10
   is at most (2 e (1 + 80 / eps))^k 200 (1 + L) / eps^2: cover the images,
   in the unit ball of 'cV[R]_k, by balls of radius eps / 40. *)
Lemma large_projection_card :
  #|[set a | eps / 10 < frobenius (V *m X a)]|%:R <=
  (2 * expR 1 * (1 + 80 / eps)) ^+ k * (200 * (1 + L%:R) / eps ^+ 2).
Proof.
set D := [set a | eps / 10 < frobenius (V *m X a)].
pose S : set 'cV[R]_k := fun z => exists2 a, a \in D & z = V *m X a.
have Sr z : S z -> frobenius z <= 1.
  by case=> a _ ->; apply: le_trans (frobenius_isometry_le VV _) (X1 a).
have e40 : 0 < eps / 40 by rewrite divr_gt0.
have [N [NS SN Nk]] := net_exists ler01 e40 Sr.
have en : eps != 0 by rewrite gt_eqF.
have -> : 80 / eps = 2 * 1 / (eps / 40) by field.
apply: le_trans (_ : (size N)%:R * (200 * (1 + L%:R) / eps ^+ 2) <= _);
  last first.
  apply: ler_wpM2r Nk.
  by rewrite !mulr_ge0 ?invr_ge0 ?exprn_ge0 ?addr_ge0 // ltW.
pose P y a := frobenius (V *m X a - y) <= eps / 40.
have cover a : a \in D -> 1 <= \sum_(y <- N) (if P y a then 1 else 0 : R).
  move=> aD; have [y yN ya] := SN (V *m X a) (ex_intro2 _ _ a aD erefl).
  rewrite (big_rem y) //= /P ya lerDl.
  by apply: sumr_ge0 => z _; case: ifP.
apply: le_trans
  (_ : \sum_(a in D) \sum_(y <- N) (if P y a then 1 else 0 : R) <= _).
  by rewrite -sum1_card natr_sum; apply: ler_sum => a aD; exact: cover.
rewrite exchange_big /=.
apply: le_trans (_ : \sum_(y <- N) (200 * (1 + L%:R) / eps ^+ 2) <= _);
  last first.
  have sc (c : R) (s : seq 'cV[R]_k) : \sum_(y <- s) c = (size s)%:R * c.
    elim: s => [|y s IH]; first by rewrite big_nil mul0r.
    by rewrite big_cons IH /= -nat1r mulrDl mul1r.
  by rewrite sc.
rewrite big_seq_cond [X in _ <= X]big_seq_cond.
apply: ler_sum => y /andP[yN _]; have [a0 a0D ya0] := NS y yN.
have -> : \sum_(i in D) (if P y i then 1 else 0 : R) =
    #|[set i in D | P y i]|%:R.
  rewrite -big_mkcondr /= -sumr_const; apply: eq_bigl => i.
  by rewrite !inE.
apply: (large_projection_cluster_card (y := y)).
  by rewrite ya0; move: a0D; rewrite inE.
by move=> a; rewrite !inE => /andP[_].
Qed.

End large_projection.

Section maximal_separated.
Context {R : realType} {m r : nat}.
Variables (v : 'I_m -> 'rV[R]_r) (delta : R).
Hypothesis delta0 : 0 < delta.

(* A maximal delta-separated subset J of a finite set I of indices: the
   points v b, b in J, are pairwise at distance at least delta, and every
   point v a, a in I, is at distance less than delta of one of them. *)
Lemma maximal_separated_subset (I : {set 'I_m}) : exists J : {set 'I_m},
  [/\ J \subset I,
      forall a b, a \in J -> b \in J -> a != b -> delta <= frobenius (v a - v b)
    & forall a, a \in I -> exists2 b, b \in J & frobenius (v a - v b) < delta].
Proof.
pose sep (J : {set 'I_m}) := (J \subset I) &&
  [forall a in J, forall b in J,
     (a != b) ==> (delta <= frobenius (v a - v b))].
have sep0 : sep (finset.set0 : {set 'I_m}).
  by rewrite /sep finset.sub0set; apply/forallP => a; rewrite inE.
have [J sepJ maxJ] := @arg_maxnP _ finset.set0 sep (fun J => #|J|) sep0.
case/andP: sepJ => JI /forallP Jsep.
have Jsep' a b : a \in J -> b \in J -> a != b ->
    delta <= frobenius (v a - v b).
  move=> aJ bJ ab.
  by have /implyP/(_ aJ)/forallP/(_ b)/implyP/(_ bJ)/implyP := Jsep a; apply.
exists J; split => // a aI.
case: (boolP [exists b in J, frobenius (v a - v b) < delta]).
  by case/existsP => b /andP[bJ ab]; exists b.
rewrite negb_exists => /forallP far; exfalso.
have far' b : b \in J -> delta <= frobenius (v a - v b).
  by move=> bJ; have := far b; rewrite bJ /= -leNgt.
have aJ : a \notin J.
  apply/negP => aJ; have := far' a aJ; rewrite subrr frobenius0.
  by rewrite leNgt delta0.
have : sep (a |: J).
  apply/andP; split; first by rewrite finset.subUset finset.sub1set aI JI.
  apply/forallP => x; apply/implyP; rewrite in_setU1 => hx.
  apply/forallP => y; apply/implyP; rewrite in_setU1 => hy.
  apply/implyP => xy.
  case/orP: hx => [/eqP xa|xJ]; case/orP: hy => [/eqP ya|yJ].
  - by rewrite xa ya eqxx in xy.
  - by rewrite xa; exact: far'.
  - by rewrite ya -frobeniusN opprB; exact: far'.
  - exact: Jsep'.
by move/maxJ; rewrite cardsU1 aJ /= /geq add1n ltnn.
Qed.

End maximal_separated.

Section cover_count.
Context {R : realType} {m : nat}.

(* A set covered by clusters C b, b in J, of at most B elements each has at
   most #|J| B elements. *)
Lemma card_le_cover (I J : {set 'I_m}) (C : 'I_m -> {set 'I_m}) (B : R) :
  (forall a, a \in I -> exists2 b, b \in J & a \in C b) ->
  (forall b, b \in J -> #|C b|%:R <= B) ->
  #|I|%:R <= #|J|%:R * B.
Proof.
move=> cov CB.
apply: le_trans
  (_ : \sum_(a in I) \sum_(b in J) (if a \in C b then 1 else 0 : R) <= _).
  rewrite -sum1_card natr_sum; apply: ler_sum => a aI.
  have [b bJ aC] := cov a aI.
  rewrite (bigD1 b) //= aC lerDl.
  by apply: sumr_ge0 => c _; case: ifP.
rewrite exchange_big /= mulr_natl -sumr_const.
apply: ler_sum => b bJ; apply: le_trans (CB b bJ).
rewrite -big_mkcondr /= -sumr_const.
apply: (@le_trans _ _ (\sum_(i in C b | i \in I) (1 : R))).
  rewrite (eq_bigl (fun i => (i \in C b) && (i \in I))) //.
  by move=> i; rewrite andbC.
rewrite [X in _ <= X](bigID (fun i => i \in I)) /= lerDl.
by apply: sumr_ge0.
Qed.

End cover_count.

Section select_rows.
Context {R : realType} {n : nat}.
Variables (P : 'M[R]_n) (A : {set 'I_n}).
Hypothesis Po : P \is orthogonalmx.

(* The rows of P indexed by A, an orthonormal family. *)
Definition select_rows : 'M[R]_(#|A|, n) := \matrix_(i, j) P (enum_val i) j.

Lemma select_rows_orth : select_rows *m select_rows^T = 1%:M.
Proof.
apply/matrixP => i i'; rewrite !mxE.
have := congr1 (fun M : 'M[R]_n => M (enum_val i) (enum_val i'))
  (orthogonalmxP _ Po).
rewrite !mxE => e.
rewrite (inj_eq enum_val_inj) in e; rewrite -e; apply: eq_bigr => j _.
by rewrite !mxE.
Qed.

Lemma select_rows_proj : select_rows^T *m select_rows =
  P^T *m diag_mx (\row_u (if u \in A then 1 else 0)) *m P.
Proof.
apply/matrixP => j j'; rewrite !mxE.
under [RHS]eq_bigr do rewrite mul_mx_diag !mxE.
rewrite [RHS](bigID (fun u => u \in A)) /= [X in _ = _ + X]big1 ?addr0.
  by move=> u /negbTE ->; rewrite mulr0 mul0r.
rewrite [RHS]big_enum_val /=.
by apply: eq_bigr => i _; rewrite !mxE enum_valP mulr1.
Qed.

End select_rows.

Section rowproj.
Context {R : realType} {k n : nat}.
Variable V : 'M[R]_(k, n).
Hypothesis VV : V *m V^T = 1%:M.

(* The orthogonal projection V^T V onto the span of the rows of V, and the
   projection onto its orthogonal complement. *)
Definition rowproj : 'M[R]_n := V^T *m V.
Definition rowperp : 'M[R]_n := 1%:M - rowproj.

Lemma rowprojT : rowproj^T = rowproj.
Proof. by rewrite /rowproj trmx_mul trmxK. Qed.

Lemma rowperpT : rowperp^T = rowperp.
Proof. by rewrite /rowperp linearB /= trmx1 rowprojT. Qed.

Lemma rowprojK : rowproj *m rowproj = rowproj.
Proof. by rewrite /rowproj mulmxA -(mulmxA V^T) VV mulmx1. Qed.

Lemma rowproj_perp : rowproj *m rowperp = 0.
Proof. by rewrite /rowperp mulmxBr mulmx1 rowprojK subrr. Qed.

Lemma rowperpK : rowperp *m rowperp = rowperp.
Proof.
by rewrite {1}/rowperp mulmxBl mul1mx rowproj_perp subr0.
Qed.

Lemma mxdot_rowproj_perp p (Z : 'M[R]_(n, p)) :
  mxdot (rowproj *m Z) (rowperp *m Z) = 0.
Proof.
rewrite mxdot_mulmxl rowprojT mulmxA.
by rewrite (_ : rowproj *m rowperp = 0) ?rowproj_perp // mul0mx mxdot0r.
Qed.

Lemma frobenius_rowperp_le p (Z : 'M[R]_(n, p)) :
  frobenius (rowperp *m Z) <= frobenius Z.
Proof.
have e : Z = rowproj *m Z + rowperp *m Z.
  by rewrite -mulmxDl /rowperp addrC subrK mul1mx.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 // !frobenius_sqr.
rewrite [in X in _ <= X]e mxdotDl !mxdotDr.
have h := mxdot_rowproj_perp Z.
have h' : mxdot (rowperp *m Z) (rowproj *m Z) = 0 by rewrite mxdotC.
by have := mxdot_ge0 (rowproj *m Z); lra.
Qed.

Lemma frobenius_rowproj p (Z : 'M[R]_(n, p)) :
  frobenius (rowproj *m Z) = frobenius (V *m Z).
Proof.
rewrite /frobenius; congr Num.sqrt.
rewrite /rowproj -mulmxA mxdot_mulmxl trmxK.
by rewrite [V *m (V^T *m _)]mulmxA VV mul1mx.
Qed.

End rowproj.

Section spectral_rowperp.
Context {R : realType} {n : nat}.
Variables (P : 'M[R]_n) (e : 'rV[R]_n) (t : R).
Hypothesis Po : P \is orthogonalmx.
Hypothesis t0 : 0 <= t.
Local Notation S := [set u | t < e 0 u].
Local Notation V := (select_rows P S).

(* For V the rows of P of the eigenvalues e_u > t, rowperp V removes the
   coordinates of these eigenvalues in the basis of the rows of P. *)
Lemma spectral_rowperp_coord (z : 'cV[R]_n) u :
  (P *m (rowperp V *m z)) u 0 = if u \in S then 0 else (P *m z) u 0.
Proof.
rewrite /rowperp /rowproj select_rows_proj // mulmxBl mul1mx mulmxBr !mulmxA.
rewrite (orthogonalmxP _ Po) mul1mx -mulmxA mul_diag_mx.
move: (P *m z) => w; rewrite !mxE.
by case: ifP; rewrite ?mul1r ?subrr ?mul0r ?subr0.
Qed.

(* So the quadratic form of P^T diag(e) P on the range of rowperp V is at
   most t. *)
Lemma spectral_rowperp_form_le (z : 'cV[R]_n) :
  mxdot (rowperp V *m z) ((P^T *m diag_mx e *m P) *m (rowperp V *m z)) <=
  t * mxdot z z.
Proof.
rewrite (spectral_form _ (erefl _)) -(mxdot_orthogonalmxl z z Po).
rewrite /mxdot mulr_sumr; apply: ler_sum => u _.
rewrite big_ord1 spectral_rowperp_coord.
rewrite inE -expr2; case: ltP => [_|etu].
  by rewrite expr0n /= mulr0; apply: mulr_ge0 t0 (sqr_ge0 _).
exact: (ler_wpM2r (sqr_ge0 _) etu).
Qed.

End spectral_rowperp.

Section gram.
Context {R : realType} {n1 n2 r : nat}.
Variable A : 'I_r -> 'M[R]_(n1, n2).

(* The matrix \sum_k A_k A_k^T: its quadratic form is \sum_k |A_k^T z|^2,
   its trace \sum_k |A_k|^2, so r for an orthonormal family, and it is
   symmetric and positive semidefinite. *)
Lemma gram_form (z : 'cV[R]_n1) :
  mxdot z ((\sum_k A k *m (A k)^T) *m z) =
  \sum_k mxdot ((A k)^T *m z) ((A k)^T *m z).
Proof.
rewrite mulmx_suml mxdot_sumr; apply: eq_bigr => k _.
by rewrite -mulmxA mxdotC mxdot_mulmxl.
Qed.

Lemma gram_trace : \tr (\sum_k A k *m (A k)^T) = \sum_k mxdot (A k) (A k).
Proof. by rewrite raddf_sum /=; apply: eq_bigr => k _; rewrite mxdot_trace. Qed.

Lemma gram_sym : \sum_k A k *m (A k)^T \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite raddf_sum /=; apply: eq_bigr => k _.
by rewrite trmx_mul trmxK.
Qed.

Lemma gram_form_ge0 (z : 'cV[R]_n1) :
  0 <= mxdot z ((\sum_k A k *m (A k)^T) *m z).
Proof. by rewrite gram_form; apply: sumr_ge0 => k _; exact: mxdot_ge0. Qed.

Lemma gram_trace_on : (forall k l, mxdot (A k) (A l) = (k == l)%:R) ->
  \tr (\sum_k A k *m (A k)^T) = r%:R.
Proof.
move=> on; rewrite gram_trace (eq_bigr (fun _ => 1)).
  by move=> k _; rewrite on eqxx.
by rewrite sumr_const card_ord.
Qed.

End gram.

Section card_large.
Context {R : realType} {n : nat}.

(* At most (\sum_u e_u) / t of the nonnegative e_u exceed t. *)
Lemma card_large_le (e : 'rV[R]_n) (t : R) : (forall u, 0 <= e 0 u) ->
  #|[set u | t < e 0 u]|%:R * t <= \sum_u e 0 u.
Proof.
move=> e0; rewrite (bigID (fun u => u \in [set u | t < e 0 u])) /=.
apply: le_trans (_ : \sum_(u | u \in [set u | t < e 0 u]) e 0 u <= _).
  rewrite mulr_natl -sumr_const; apply: ler_sum => u.
  by rewrite inE => /ltW.
by rewrite lerDl; apply: sumr_ge0 => u _.
Qed.

End card_large.

Section tensor_rows.
Context {R : realType} {n1 n2 : nat}.

(* The tensor x^T y of two rows: <x^T y, x'^T y'> = <x, x'> <y, y'>, and
   <x^T y, A> is the bilinear form x A y^T. *)
Lemma mxdot_tensor (x x' : 'rV[R]_n1) (y y' : 'rV[R]_n2) :
  mxdot (x^T *m y) (x'^T *m y') = mxdot x x' * mxdot y y'.
Proof.
have := mxdot_outer2 x^T x'^T y^T y'^T.
by rewrite !trmxK !mxdot_trmx.
Qed.

Lemma frobenius_tensor (x : 'rV[R]_n1) (y : 'rV[R]_n2) :
  frobenius (x^T *m y) = frobenius x * frobenius y.
Proof.
by rewrite /frobenius mxdot_tensor sqrtrM ?mxdot_ge0.
Qed.

Lemma mxdot_tensor_form (x : 'rV[R]_n1) (y : 'rV[R]_n2) (A : 'M[R]_(n1, n2)) :
  mxdot (x^T *m y) A = (x *m A *m y^T) 0 0.
Proof.
by rewrite mxdotC -{1}[y]trmxK mxdot_outer trmxK.
Qed.

End tensor_rows.

Section mxcoef.
Context {R : realType} {p q r : nat}.
Variable A : 'I_r -> 'M[R]_(p, q).
Hypothesis Aon : forall k l, mxdot (A k) (A l) = (k == l)%:R.

(* The coefficients of a matrix on the family A, its inner products with
   the A_k; a contraction when the family is orthonormal. *)
Definition mxcoef (Z : 'M[R]_(p, q)) : 'rV[R]_r := \row_k mxdot Z (A k).

Lemma mxcoefD Z Z' : mxcoef (Z + Z') = mxcoef Z + mxcoef Z'.
Proof. by apply/rowP => k; rewrite !mxE mxdotDl. Qed.

Lemma mxcoefB Z Z' : mxcoef (Z - Z') = mxcoef Z - mxcoef Z'.
Proof. by apply/rowP => k; rewrite !mxE mxdotBl. Qed.

Lemma mxcoef_sum (I : finType) (P : pred I) (F : I -> 'M[R]_(p, q)) :
  mxcoef (\sum_(i | P i) F i) = \sum_(i | P i) mxcoef (F i).
Proof.
apply/rowP => k; rewrite mxE summxE mxdot_suml.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma frobenius_mxcoef_sqr Z :
  frobenius (mxcoef Z) ^+ 2 = \sum_k mxdot Z (A k) ^+ 2.
Proof.
rewrite frobenius_sqr /mxdot big_ord1; apply: eq_bigr => k _.
by rewrite mxE expr2.
Qed.

Lemma frobenius_mxcoef_le Z : frobenius (mxcoef Z) <= frobenius Z.
Proof.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 // frobenius_mxcoef_sqr frobenius_sqr.
exact: bessel_mxdot.
Qed.

End mxcoef.

Section compress_gram.
Context {R : realType} {n1 n2 r k1 k2 : nat}.
Variable A : 'I_r -> 'M[R]_(n1, n2).
Variables (V1 : 'M[R]_(k1, n1)) (V2 : 'M[R]_(k2, n2)).
Variable t : R.
Hypothesis V1V1 : V1 *m V1^T = 1%:M.
Hypothesis V2V2 : V2 *m V2^T = 1%:M.
Hypothesis t0 : 0 <= t.
Hypothesis cut1 : forall z : 'cV[R]_n1,
  mxdot (rowperp V1 *m z) ((\sum_k A k *m (A k)^T) *m (rowperp V1 *m z)) <=
  t * mxdot z z.

(* The compressions rowperp V1 A_k rowperp V2 inherit the bound t of the
   quadratic form on the range of rowperp V1, and the trace bound. *)
Lemma opnorm_compress_gram :
  opnorm (\sum_k (rowperp V1 *m A k *m rowperp V2) *m
                 (rowperp V1 *m A k *m rowperp V2)^T) <= t.
Proof.
set B := fun k => rowperp V1 *m A k *m rowperp V2.
have Msym : (\sum_k B k *m (B k)^T) \is symmetricmx.
  apply/symmetricmxP; rewrite raddf_sum /=; apply: eq_bigr => k _.
  by rewrite trmx_mul trmxK.
apply/(opnorm_symP Msym t0) => z.
have g0 : 0 <= mxdot z ((\sum_k B k *m (B k)^T) *m z).
  by rewrite gram_form; apply: sumr_ge0 => k _; exact: mxdot_ge0.
rewrite ger0_norm // gram_form.
apply: le_trans (cut1 z); rewrite gram_form; apply: ler_sum => k _.
rewrite /B !trmx_mul !rowperpT -!mulmxA.
rewrite -!frobenius_sqr lerXn2r ?nnegrE ?frobenius_ge0 //.
exact: frobenius_rowperp_le.
Qed.

Lemma trace_compress_gram :
  \tr (\sum_k (rowperp V1 *m A k *m rowperp V2) *m
              (rowperp V1 *m A k *m rowperp V2)^T) <=
  \sum_k mxdot (A k) (A k).
Proof.
rewrite (gram_trace (fun k => rowperp V1 *m A k *m rowperp V2)).
apply: ler_sum => k _.
rewrite -!frobenius_sqr lerXn2r ?nnegrE ?frobenius_ge0 //.
rewrite -mulmxA; apply: le_trans (frobenius_rowperp_le V1V1 _) _.
rewrite -frobenius_trmx trmx_mul rowperpT -[X in _ <= X]frobenius_trmx.
exact: frobenius_rowperp_le.
Qed.

End compress_gram.

Section compress.
Context {R : realType} {n1 n2 r k1 k2 : nat}.
Variable A : 'I_r -> 'M[R]_(n1, n2).
Variables (V1 : 'M[R]_(k1, n1)) (V2 : 'M[R]_(k2, n2)).
Hypothesis Aon : forall k l, mxdot (A k) (A l) = (k == l)%:R.
Hypothesis V1V1 : V1 *m V1^T = 1%:M.
Hypothesis V2V2 : V2 *m V2^T = 1%:M.

Lemma frobenius_outer m n (c : 'cV[R]_m) (w : 'rV[R]_n) :
  frobenius (c *m w) = frobenius c * frobenius w.
Proof. by rewrite -[c]trmxK frobenius_tensor !frobenius_trmx. Qed.

(* Compressing by projections does not increase the Frobenius norm. *)
Lemma frobenius_rowperp_compress_le (Z : 'M[R]_(n1, n2)) :
  frobenius (rowperp V1 *m Z *m rowperp V2) <= frobenius Z.
Proof.
rewrite -mulmxA; apply: le_trans (frobenius_rowperp_le V1V1 _) _.
rewrite -frobenius_trmx trmx_mul rowperpT -[X in _ <= X]frobenius_trmx.
exact: frobenius_rowperp_le.
Qed.

(* If the projections of x and y on the rows of V1 and V2 are small, then the
   coefficients of x^T y and of its compression are close. *)
Lemma mxcoef_compress_near (x : 'rV[R]_n1) (y : 'rV[R]_n2) (eps : R) :
  frobenius x <= 1 -> frobenius y <= 1 ->
  frobenius (V1 *m x^T) <= eps -> frobenius (V2 *m y^T) <= eps ->
  frobenius (mxcoef A (x^T *m y) -
             mxcoef A (rowperp V1 *m (x^T *m y) *m rowperp V2)) <= 2 * eps.
Proof.
move=> x1 y1 hx hy.
rewrite -mxcoefB; apply: le_trans (frobenius_mxcoef_le Aon _) _.
set Z := x^T *m y.
have -> : Z - rowperp V1 *m Z *m rowperp V2 =
    (Z - rowperp V1 *m Z) + (rowperp V1 *m Z - rowperp V1 *m Z *m rowperp V2).
  by rewrite addrA subrK.
have e1 : Z - rowperp V1 *m Z = (rowproj V1 *m x^T) *m y.
  by rewrite /rowperp mulmxBl mul1mx opprB addrC subrK /Z mulmxA.
have e2 : rowperp V1 *m Z - rowperp V1 *m Z *m rowperp V2 =
    (rowperp V1 *m x^T) *m (y *m rowproj V2).
  rewrite {2}/rowperp mulmxBr mulmx1 opprB addrC subrK /Z.
  by rewrite !mulmxA.
rewrite e1 e2; apply: le_trans (frobeniusD _ _) _.
rewrite !frobenius_outer (frobenius_rowproj V1V1).
have -> : frobenius (y *m rowproj V2) = frobenius (V2 *m y^T).
  by rewrite -frobenius_trmx trmx_mul rowprojT (frobenius_rowproj V2V2).
have l1 : frobenius (rowperp V1 *m x^T) <= 1.
  by apply: le_trans (frobenius_rowperp_le V1V1 _) _; rewrite frobenius_trmx.
have := frobenius_ge0 (V1 *m x^T); have := frobenius_ge0 y.
have := frobenius_ge0 (rowperp V1 *m x^T); have := frobenius_ge0 (V2 *m y^T).
nra.
Qed.

End compress.

Section sum_near.
Context {R : realType} {m p q : nat}.

(* Points within delta of a center w have a sum of norm at least
   (|w| - delta) times their number. *)
Lemma frobenius_sum_near (u : 'I_m -> 'M[R]_(p, q)) (w : 'M[R]_(p, q))
    (C : {set 'I_m}) (delta : R) :
  (forall a, a \in C -> frobenius (u a - w) <= delta) ->
  (frobenius w - delta) * #|C|%:R <= frobenius (\sum_(a in C) u a).
Proof.
move=> hC; set s : R := #|C|%:R.
have s0 : 0 <= s := ler0n _ _.
have h1 : frobenius (\sum_(a in C) u a - s *: w) <= s * delta.
  rewrite /s scaler_nat -sumr_const -sumrB.
  apply: le_trans (frobenius_sum_le (mem C) (fun i => u i - w)) _.
  rewrite mulr_natl -sumr_const.
  by apply: ler_sum => a aC; exact: hC.
have hz := frobeniusD (s *: w - \sum_(a in C) u a) (\sum_(a in C) u a).
rewrite subrK -[frobenius (s *: w - _)]frobeniusN opprB in hz.
rewrite frobeniusZ ger0_norm // in hz.
by rewrite mulrBl mulrC [delta * _]mulrC; lra.
Qed.

End sum_near.

Section sudakov_mx_series.
Context {R : realType} {n1 n2 r : nat}.
Variable B : 'I_r -> 'M[R]_(n1, n2).

(* Sudakov's minoration for the coefficient vectors of x_i^T y_i on B: if
   they are delta-separated, then E opnorm (\sum_k g_k B_k) is at least
   delta (sqrt (ln (l + 1)) / 2 - 2) / sqrt 2. *)
Lemma sudakov_mx_series l (x : 'I_l.+1 -> 'rV[R]_n1) (y : 'I_l.+1 -> 'rV[R]_n2)
    (delta : R) :
  0 <= delta -> (forall i, frobenius (x i) <= 1) ->
  (forall i, frobenius (y i) <= 1) ->
  (forall i j, i != j ->
    delta <= frobenius (mxcoef B ((x i)^T *m y i) -
                        mxcoef B ((x j)^T *m y j))) ->
  delta * (Num.sqrt (ln l.+1%:R) / 2 - 2) <=
  Num.sqrt 2 * \int[gauss r]_g opnorm (\sum_k g 0 k *: B k).
Proof.
move=> d0 x1 y1 sep.
set vv := fun i => mxcoef B ((x i)^T *m y i).
apply: le_trans (sudakov_minoration (xs := vv) d0 sep) _.
apply: ler_wpM2l; first exact: sqrtr_ge0.
pose M : 'M[R]_(r, l.+1) := \matrix_(j, i) vv i 0 j.
have rowM (g : 'rV[R]_r) : \row_i mxdot g (vv i) = g *m M.
  apply/rowP => i; rewrite !mxE /mxdot big_ord1; apply: eq_bigr => j _.
  by rewrite !mxE.
apply: le_Rintegral => //.
- under eq_fun do rewrite /= rowM.
  exact: integrable_gauss_rmax.
- exact: integrable_gauss_lipschitz (series_opnorm_lipschitz B).
move=> g _; apply: rmax_le => i; rewrite mxE /vv.
have -> : mxdot g (mxcoef B ((x i)^T *m y i)) =
    mxdot ((x i)^T *m y i) (\sum_k g 0 k *: B k).
  rewrite mxdot_sumr {1}/mxdot big_ord1; apply: eq_bigr => k _.
  by rewrite mxdotZr mxE.
set G := \sum_k g 0 k *: B k.
rewrite mxdot_tensor_form.
have -> : (x i *m G *m (y i)^T) 0 0 = mxdot (x i)^T (G *m (y i)^T).
  by rewrite mxdot_colE trmxK mulmxA.
apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_opnorm _ _ _) _.
rewrite !frobenius_trmx -[X in _ <= X]mulr1 -mulrA.
apply: ler_wpM2l; first exact: opnorm_ge0.
by rewrite -[1]mul1r; apply: ler_pM; rewrite ?frobenius_ge0 ?x1 ?y1.
Qed.

End sudakov_mx_series.

Section separated_card.
Context {R : realType} {n1 n2 r m : nat}.
Variables (B : 'I_r -> 'M[R]_(n1, n2)) (x : 'I_m -> 'rV[R]_n1).
Variables (y : 'I_m -> 'rV[R]_n2).
Hypothesis x1 : forall a, frobenius (x a) <= 1.
Hypothesis y1 : forall a, frobenius (y a) <= 1.

Lemma separated_card_sudakov (J : {set 'I_m}) (delta M : R) : 0 <= delta ->
  (forall a b, a \in J -> b \in J -> a != b ->
    delta <= frobenius (mxcoef B ((x a)^T *m y a) -
                        mxcoef B ((x b)^T *m y b))) ->
  \int[gauss r]_g opnorm (\sum_k g 0 k *: B k) <= M ->
  delta * (Num.sqrt (ln #|J|%:R) / 2 - 2) <= Num.sqrt 2 * M.
Proof.
move=> d0 sep hM.
have M0 : 0 <= M.
  by apply: le_trans hM; apply: Rintegral_ge0 => g _; exact: opnorm_ge0.
have [J0|Jp] := posnP #|J|.
  rewrite J0 ln0 // sqrtr0 mul0r sub0r mulrN.
  by apply: le_trans (_ : 0 <= _); rewrite ?oppr_le0 ?mulr_ge0 ?sqrtr_ge0.
have [l Jl] : exists l, #|J| = l.+1 by exists #|J|.-1; rewrite prednK.
pose e (i : 'I_l.+1) : 'I_m := enum_val (cast_ord (esym Jl) i).
have eJ i : e i \in J by exact: enum_valP.
have einj i j : i != j -> e i != e j.
  move=> ij; apply: contra ij => /eqP /enum_val_inj /cast_ord_inj ->.
  exact: eqxx.
rewrite Jl.
have := sudakov_mx_series (B := B) (x := x \o e) (y := y \o e) d0.
move=> /(_ (fun i => x1 _) (fun i => y1 _)) h.
apply: le_trans (h _) _.
  by move=> i j ij; apply: sep => //; exact: einj.
by apply: ler_wpM2l; first exact: sqrtr_ge0.
Qed.

End separated_card.

Section packing_arith.
Context {R : realType}.

(* ln u <= u - 1 for u > 0. *)
Lemma ln_le_subr1 (u : R) : 0 < u -> ln u <= u - 1.
Proof.
move=> u0; have := expR_ge1Dx (ln u); rewrite lnK ?posrE //; lra.
Qed.

(* The number of balls covering the discarded projections, for a
   dimension k <= sqrt d. *)
Lemma tensor_packing_net (eps d : R) (k : nat) :
  0 < eps -> eps <= 1 -> 1 <= d ->
  k%:R <= Num.sqrt d ->
  (2 * expR 1 * (1 + 80 / eps)) ^+ k <=
  expR (972 * Num.sqrt d * ln (2 + d) / eps ^+ 2).
Proof.
move=> e0 e1 d1 kd.
have L23 := ln2D_ge d1.
set K := 2 * expR 1 * (1 + 80 / eps).
have ie1 : 1 <= eps^-1 by rewrite invf_ge1.
have ie2 : eps^-1 <= (eps ^+ 2)^-1.
  have e2 : (eps ^+ 2)^-1 = eps^-1 * eps^-1 by rewrite expr2 invfM.
  by rewrite e2; move: ie1; set u := eps^-1 => ie1; nra.
have E4 := @expR1_le4 R.
have E2 : 2 <= expR 1 :> R by have := @expR_ge1Dx R 1; lra.
have h80 : 0 <= 80 / eps by rewrite divr_ge0 // ltW.
have K1 : 1 <= K by rewrite /K; nra.
have K0 : 0 < K by apply: lt_le_trans K1.
have hK : ln K <= 648 / eps ^+ 2.
  apply: le_trans (ln_le_subr1 K0) _.
  move: ie1 ie2; rewrite /K; set u := eps^-1; set w := eps ^- 2 => ie1 ie2.
  have p : 0 <= (4 - expR 1) * (1 + 80 * u) by rewrite mulr_ge0 //; lra.
  nra.
rewrite -[K]lnK ?posrE // -expRM_natl ler_expR.
apply: le_trans (_ : Num.sqrt d * (648 / eps ^+ 2) <= _).
  by apply: ler_pM; rewrite ?ler0n ?ln_ge0.
have s0 : 0 <= Num.sqrt d := sqrtr_ge0 d.
have w0 : 0 <= (eps ^+ 2)^-1 by rewrite invr_ge0 exprn_ge0 // ltW.
move: L23; set Ld := ln (2 + d); set sd := Num.sqrt d; set w := (eps ^+ 2)^-1.
move=> L23; have p : 0 <= sd * w * (972 * Ld - 648).
  by apply: mulr_ge0; [exact: mulr_ge0 | lra].
lra.
Qed.

(* The size l of the separated set, from Sudakov's minoration and the
   bound 5 d^(1/4) sqrt (ln (2 + d)) of the expected operator norm. *)
Lemma tensor_packing_separated (eps d : R) (l : nat) :
  0 < eps -> eps <= 1 -> 1 <= d ->
  eps / 8 * (Num.sqrt (ln l%:R) / 2 - 2) <=
    Num.sqrt 2 * (5 * d `^ 4^-1 * Num.sqrt (ln (2 + d))) ->
  l%:R <= expR (25648 * Num.sqrt d * ln (2 + d) / eps ^+ 2).
Proof.
move=> e0 e1 d1 h.
have L23 := ln2D_ge d1.
have [l0|lp] := posnP l; first by rewrite l0 expR_ge0.
have l1 : 1 <= l%:R :> R by rewrite ler1n.
rewrite -[l%:R]lnK ?posrE ?ltr0n // ler_expR.
have Ll0 : 0 <= ln l%:R :> R := ln_ge0 l1.
have ss : Num.sqrt (ln l%:R) ^+ 2 = ln l%:R :> R by rewrite sqr_sqrtr.
have d0 : 0 <= d by apply: le_trans d1.
have y2 : (d `^ 4^-1) ^+ 2 = Num.sqrt d.
  rewrite -powR_mulrn ?powR_ge0 // -powRrM (_ : 4^-1 * 2%:R = 2^-1).
    by field.
  exact: powR12_sqrt.
have q2 : Num.sqrt (ln (2 + d)) ^+ 2 = ln (2 + d) by rewrite sqr_sqrtr //; lra.
have c2 : Num.sqrt 2 ^+ 2 = 2 :> R by rewrite sqr_sqrtr.
have sd1 : 1 <= Num.sqrt d by rewrite -sqrtr1 ler_wsqrtr.
move: h ss y2 q2 c2 sd1.
set s := Num.sqrt (ln l%:R); set y := d `^ 4^-1; set q := Num.sqrt (ln (2 + d)).
set c := Num.sqrt 2; set Ll := ln l%:R; set L' := ln (2 + d).
set sd := Num.sqrt d => h ss y2 q2 c2 sd1.
have s0 : 0 <= s := sqrtr_ge0 _.
have y0 : 0 <= y := powR_ge0 _ _.
have q0 : 0 <= q := sqrtr_ge0 _.
have c0 : 0 <= c := sqrtr_ge0 _.
rewrite -/L' in L23.
have Z2 : (c * y * q) ^+ 2 = 2 * sd * L' by rewrite !exprMn c2 y2 q2.
have Z0 : 0 <= c * y * q by rewrite !mulr_ge0.
(* sqrt (ln l) <= 4 + 80 sqrt 2 d^(1/4) sqrt (ln (2 + d)) / eps *)
have hZ : eps * (s - 4) <= 80 * (c * y * q).
  have -> : eps * (s - 4) = 16 * (eps / 8 * (s / 2 - 2)) by field.
  have -> : 80 * (c * y * q) = 16 * (c * (5 * y * q)) by ring.
  by rewrite ler_pM2l.
have sdL : 2 / 3 <= sd * L'.
  have : 0 <= (sd - 1) * L' by apply: mulr_ge0; lra.
  lra.
rewrite ler_pdivlMr ?exprn_gt0 // -ss.
have e2 : eps ^+ 2 <= 1 by rewrite exprn_ile1 // ltW.
have [s4|s4] := leP s 4.
  have h16 : s ^+ 2 <= 16.
    by rewrite (_ : 16 = 4 ^+ 2) ?lerXn2r ?nnegrE //; lra.
  have : 0 <= s ^+ 2 * (1 - eps ^+ 2).
    by apply: mulr_ge0; [exact: sqr_ge0 | lra].
  lra.
have t0 : 0 <= eps * (s - 4) by apply: mulr_ge0; [exact: ltW | lra].
have hZ2 : (eps * (s - 4)) ^+ 2 <= (80 * (c * y * q)) ^+ 2.
  by apply: lerXn2r; rewrite ?nnegrE // mulr_ge0.
rewrite [X in _ <= X]exprMn Z2 in hZ2.
have key : s ^+ 2 * eps ^+ 2 <= 2 * (eps * (s - 4)) ^+ 2 + 32 * eps ^+ 2.
  have := sqr_ge0 (eps * (s - 4) - 4 * eps).
  by rewrite !exprMn !expr2; lra.
lra.
Qed.

(* The size of the clusters of the remaining indices, for
   rho = 27 eps / 40. *)
Lemma tensor_packing_cluster (eps eta u : R) : 0 < eps -> 0 <= eta ->
  eta <= eps ^+ 2 / 10000 -> 0 <= u ->
  u / ((27 * eps / 40) ^+ 2 - eta) <= 3 * (u / eps ^+ 2).
Proof.
move=> e0 eta0 ee u0.
have r2 : (27 * eps / 40) ^+ 2 = 729 / 1600 * eps ^+ 2 by field.
have e20 : 0 < eps ^+ 2 by rewrite exprn_gt0.
have rq : eps ^+ 2 / 3 <= (27 * eps / 40) ^+ 2 - eta by rewrite r2; lra.
have rq0 : 0 < eps ^+ 2 / 3 by rewrite divr_gt0.
rewrite mulrCA; apply: ler_wpM2l => //.
rewrite -[3 / _]invf_div lef_pV2 ?posrE //; exact: lt_le_trans rq0 rq.
Qed.

(* The final count: the discarded indices and the clusters around the
   separated set. *)
Lemma tensor_packing_count (N D1 D2 I J K1 K2 F Q X : R) :
  0 <= F -> 0 <= X -> 0 <= J -> 0 <= Q ->
  N <= D1 + D2 + I ->
  D1 <= K1 * (200 * F) -> D2 <= K2 * (200 * F) -> I <= J * Q ->
  K1 <= expR (972 * X) -> K2 <= expR (972 * X) -> J <= expR (25648 * X) ->
  Q <= 3 * F ->
  N <= 30000 * F * expR (30000 * X).
Proof.
move=> F0 X0 J0 Q0 hN h1 h2 hI k1 k2 j q.
set E := expR (30000 * X).
have E0 : 0 <= E := expR_ge0 _.
have le (c : R) : c <= 30000 -> expR (c * X) <= E.
  by move=> c3; rewrite ler_expR ler_wpM2r.
have {}k1 := le_trans k1 (le 972 ltac:(lra)).
have {}k2 := le_trans k2 (le 972 ltac:(lra)).
have {}j := le_trans j (le 25648 ltac:(lra)).
have F2 : 0 <= 200 * F by rewrite mulr_ge0.
have a1 := le_trans h1 (ler_wpM2r F2 k1).
have a2 := le_trans h2 (ler_wpM2r F2 k2).
have a3 : I <= E * (3 * F) by apply: le_trans hI (ler_pM J0 Q0 j q).
have : 0 <= E * F by rewrite mulr_ge0.
lra.
Qed.

End packing_arith.

Section tensor_packing.
Context {R : realType}.
Local Notation gauss := (@gauss R).

(* Tensor packing (Theorem 4.1 of the fourfold paper of family 154), with
   the constant 30000. *)
Theorem tensor_packing (m n1 n2 r d L : nat) (eps eta : R)
    (x : 'I_m -> 'rV[R]_n1) (y : 'I_m -> 'rV[R]_n2) (Gx Gy : rel 'I_m)
    (A : 'I_r -> 'M[R]_(n1, n2)) :
  0 < eps -> eps <= 1 -> (0 < d)%N -> 0 <= eta -> eta <= eps ^+ 2 / 10000 ->
  (forall a, frobenius (x a) <= 1) -> (forall a, frobenius (y a) <= 1) ->
  (forall a, #|[set b | Gx a b]| <= L)%N ->
  (forall a, #|[set b | Gy a b]| <= L)%N ->
  (forall a b, a != b -> eta < `|mxdot (x a) (x b)| -> Gx a b) ->
  (forall a b, a != b -> eta < `|mxdot (y a) (y b)| -> Gy a b) ->
  (forall k l, mxdot (A k) (A l) = (k == l)%:R) -> (r <= d)%N ->
  #|[set a | eps ^+ 2 <= \sum_k ((x a) *m A k *m (y a)^T) 0 0 ^+ 2]|%:R <=
  30000 * (1 + L%:R) / eps ^+ 2 *
    expR (30000 * Num.sqrt d%:R * ln (2 + d%:R) / eps ^+ 2).
Proof.
move=> eps0 eps1 d0 eta0 eta_eps x1 y1 degx degy exx exy Aon rd.
set t : R := Num.sqrt d%:R.
have d1 : 1 <= d%:R :> R by rewrite ler1n.
have t1 : 1 <= t by rewrite -sqrtr1 ler_wsqrtr.
have t0 : 0 <= t by apply: le_trans t1.
have tt : t * t = d%:R by rewrite -expr2 sqr_sqrtr // ler0n.
pose At k := (A k)^T.
have Aton k l : mxdot (At k) (At l) = (k == l)%:R by rewrite mxdot_trmx Aon.
(* the spectral decompositions of \sum_k A_k A_k^T and \sum_k A_k^T A_k *)
have [P1 Po1 [e1 E1]] := symmetric_spectral (gram_sym A).
have [P2 Po2 [e2 E2]] := symmetric_spectral (gram_sym At).
have e10 u : 0 <= e1 0 u := (spectral_psd Po1 E1).1 (gram_form_ge0 A) u.
have e20 u : 0 <= e2 0 u := (spectral_psd Po2 E2).1 (gram_form_ge0 At) u.
set S1 := [set u | t < e1 0 u]; set S2 := [set u | t < e2 0 u].
set V1 := select_rows P1 S1; set V2 := select_rows P2 S2.
have V1V1 : V1 *m V1^T = 1%:M := select_rows_orth S1 Po1.
have V2V2 : V2 *m V2^T = 1%:M := select_rows_orth S2 Po2.
have cut1 (z : 'cV[R]_n1) :
    mxdot (rowperp V1 *m z) ((\sum_k A k *m (A k)^T) *m (rowperp V1 *m z)) <=
    t * mxdot z z by rewrite E1; exact: spectral_rowperp_form_le.
have cut2 (z : 'cV[R]_n2) :
    mxdot (rowperp V2 *m z) ((\sum_k At k *m (At k)^T) *m (rowperp V2 *m z)) <=
    t * mxdot z z by rewrite E2; exact: spectral_rowperp_form_le.
have rdR : r%:R <= d%:R :> R by rewrite ler_nat.
(* the compressed family B_k = lo1 A_k lo2 and the coefficient vectors *)
pose B k := rowperp V1 *m A k *m rowperp V2.
pose T a := (x a)^T *m y a.
pose v a := mxcoef B (T a).
have vE Z : mxcoef B Z = mxcoef A (rowperp V1 *m Z *m rowperp V2).
  apply/rowP => k; rewrite !mxE /B mxdot_mulmxr mxdot_mulmxl !rowperpT.
  by rewrite mulmxA.
(* the counted, discarded and remaining indices *)
set N := [set a | eps ^+ 2 <= \sum_k (x a *m A k *m (y a)^T) 0 0 ^+ 2].
set D1 := [set a | eps / 10 < frobenius (V1 *m (x a)^T)].
set D2 := [set a | eps / 10 < frobenius (V2 *m (y a)^T)].
set I := N :\: (D1 :|: D2).
(* the remaining indices have compressed coefficients of norm >= 4 eps / 5 *)
have vfar a : a \in I -> 4 * eps / 5 <= frobenius (v a).
  rewrite !inE negb_or => /andP[/andP[nD1 nD2] aN].
  rewrite -leNgt in nD1; rewrite -leNgt in nD2.
  have hn := mxcoef_compress_near Aon V1V1 V2V2 (x1 a) (y1 a) nD1 nD2.
  have hc : eps <= frobenius (mxcoef A (T a)).
    have h2 : eps ^+ 2 <= frobenius (mxcoef A (T a)) ^+ 2.
      rewrite frobenius_mxcoef_sqr /T.
      by under eq_bigr do rewrite mxdot_tensor_form.
    have f0 := frobenius_ge0 (mxcoef A (T a)).
    nra.
  rewrite /v vE /T; rewrite /T in hc.
  have := frobeniusD
    (mxcoef A ((x a)^T *m y a) -
     mxcoef A (rowperp V1 *m ((x a)^T *m y a) *m rowperp V2))
    (mxcoef A (rowperp V1 *m ((x a)^T *m y a) *m rowperp V2)).
  by rewrite subrK; lra.
have k1t : #|S1|%:R <= t.
  have := @card_large_le R n1 e1 t e10.
  rewrite -(spectral_trace Po1 E1) gram_trace_on // => h.
  rewrite -(ler_pM2r (lt_le_trans ltr01 t1)) tt; exact: le_trans h rdR.
have k2t : #|S2|%:R <= t.
  have := @card_large_le R n2 e2 t e20.
  rewrite -(spectral_trace Po2 E2) gram_trace_on // => h.
  rewrite -(ler_pM2r (lt_le_trans ltr01 t1)) tt; exact: le_trans h rdR.
have H1 : opnorm (\sum_k B k *m (B k)^T) <= Num.sqrt d%:R.
  exact: (opnorm_compress_gram (A := A) V2V2 t0 cut1).
have BT k : rowperp V2 *m At k *m rowperp V1 = (B k)^T.
  by rewrite /B !trmx_mul !rowperpT mulmxA.
have H2 : opnorm (\sum_k (B k)^T *m B k) <= Num.sqrt d%:R.
  have := opnorm_compress_gram (A := At) V1V1 t0 cut2.
  by under eq_bigr do rewrite BT trmxK.
have H3 : \tr (\sum_k B k *m (B k)^T) <= d%:R.
  apply: le_trans (trace_compress_gram A V1V1 V2V2) _.
  by rewrite -gram_trace gram_trace_on.
have EM : \int[gauss r]_g opnorm (\sum_k g 0 k *: B k) <=
    5 * d%:R `^ 4^-1 * Num.sqrt (ln (2 + d%:R)).
  have h := gauss_mx_series_opnorm_log d1 H1 H2 H3.
  have iG := integrable_gauss_lipschitz (series_opnorm_lipschitz B).
  by rewrite -(fineK (integrable_fin_num measurableT iG)) lee_fin in h.
have vle Z : frobenius (mxcoef B Z) <= frobenius Z.
  rewrite vE; apply: le_trans (frobenius_mxcoef_le Aon _) _.
  exact: frobenius_rowperp_compress_le.
have T1 a : mxdot (T a) (T a) <= 1.
  rewrite mxdot_tensor -!frobenius_sqr.
  rewrite -[1](mulr1 1); apply: ler_pM; rewrite ?sqr_ge0 //.
    by rewrite exprn_ile1 ?frobenius_ge0.
  by rewrite exprn_ile1 ?frobenius_ge0.
have exT a b : a != b -> ~~ Gx a b -> `|mxdot (T a) (T b)| <= eta.
  move=> ab nG; rewrite mxdot_tensor normrM -[eta]mulr1.
  apply: ler_pM; rewrite ?normr_ge0 //.
    by rewrite leNgt; apply/negP => h; move: nG; rewrite (exx a b ab h).
  apply: le_trans (mxdot_le _ _) _; rewrite -[1](mulr1 1).
  by apply: ler_pM; rewrite ?frobenius_ge0 ?y1.
have cN : #|N|%:R <= #|D1|%:R + #|D2|%:R + #|I|%:R :> R.
  rewrite -!natrD ler_nat.
  apply: leq_trans (_ : #|(D1 :|: D2) :|: I| <= _)%N.
    apply: subset_leq_card; apply/fintype.subsetP => a aN.
    rewrite finset.in_setU finset.in_setD aN andbT.
    by case: (a \in D1 :|: D2).
  rewrite finset.cardsU; apply: leq_trans (leq_subr _ _) _.
  by rewrite leq_add2r finset.cardsU leq_subr.
have cD1 : #|D1|%:R <=
    (2 * expR 1 * (1 + 80 / eps)) ^+ #|S1| * (200 * (1 + L%:R) / eps ^+ 2).
  apply: (large_projection_card (X := fun a => (x a)^T) (G := Gx) V1V1 eps0 eta0
    eta_eps) => [a|//|a b ab nG].
    by rewrite frobenius_trmx.
  rewrite mxdot_trmx leNgt; apply/negP => h; move: nG.
  by rewrite (exx a b ab h).
have cD2 : #|D2|%:R <=
    (2 * expR 1 * (1 + 80 / eps)) ^+ #|S2| * (200 * (1 + L%:R) / eps ^+ 2).
  apply: (large_projection_card (X := fun a => (y a)^T) (G := Gy) V2V2 eps0 eta0
    eta_eps) => [a|//|a b ab nG].
    by rewrite frobenius_trmx.
  rewrite mxdot_trmx leNgt; apply/negP => h; move: nG.
  by rewrite (exy a b ab h).
(* a maximal eps / 8-separated subset J of the remaining indices *)
have e8 : 0 < eps / 8 by rewrite divr_gt0.
have [J [JI Jsep Jcov]] := maximal_separated_subset v e8 I.
pose rho := 27 * eps / 40.
have cI : #|I|%:R <= #|J|%:R * ((1 + L%:R) / (rho ^+ 2 - eta)).
  apply: (card_le_cover
    (C := fun b => [set a in I | frobenius (v a - v b) < eps / 8])).
    move=> a aI; have [b bJ hb] := Jcov a aI.
    by exists b => //; rewrite inE aI hb.
  move=> b bJ.
  apply: (almost_orthogonal_card_le (T := T) (G := Gx) eta0 T1 degx exT).
  - by rewrite /rho divr_ge0 // mulr_ge0 // ltW.
  - by apply: le_lt_trans eta_eps _; rewrite /rho; nra.
  set C := [set a in I | _].
  have hvb := vfar b (fintype.subsetP JI b bJ).
  have hC : forall a, a \in C -> frobenius (v a - v b) <= eps / 8.
    by move=> a; rewrite inE => /andP[_ /ltW].
  have h' := frobenius_sum_near hC.
  have sv : \sum_(a in C) v a = mxcoef B (\sum_(a in C) T a).
    by rewrite mxcoef_sum.
  rewrite sv in h'; apply: le_trans (le_trans _ h') (vle _).
  apply: ler_wpM2r; first exact: ler0n.
  by rewrite /rho; lra.
have cJ : #|J|%:R <= expR (25648 * t * ln (2 + d%:R) / eps ^+ 2).
  apply: (tensor_packing_separated eps0 eps1 d1).
  by apply: (@separated_card_sudakov _ _ _ _ _ B x y x1 y1 J (eps / 8) _
    (ltW e8)).
(* the final count *)
have L'0 : 0 <= ln (2 + d%:R) :> R by rewrite ln_ge0 //; lra.
have X0 : 0 <= t * ln (2 + d%:R) / eps ^+ 2.
  by rewrite divr_ge0 ?mulr_ge0 ?exprn_ge0 // ltW.
have u0 : 0 <= 1 + L%:R :> R by rewrite addr_ge0 ?ler0n.
have F0 : 0 <= (1 + L%:R) / eps ^+ 2 by rewrite divr_ge0 ?exprn_ge0 // ltW.
have eX (c : R) :
    c * t * ln (2 + d%:R) / eps ^+ 2 = c * (t * ln (2 + d%:R) / eps ^+ 2).
  by rewrite !mulrA.
have eF (c : R) : c * (1 + L%:R) / eps ^+ 2 = c * ((1 + L%:R) / eps ^+ 2).
  by rewrite mulrA.
have q := tensor_packing_cluster eps0 eta0 eta_eps u0; rewrite -/rho in q.
have Q0 : 0 <= (1 + L%:R) / (rho ^+ 2 - eta).
  apply: divr_ge0 => //; apply: le_trans (_ : 0 <= eps ^+ 2 / 3) _.
    by rewrite divr_ge0 ?exprn_ge0 // ltW.
  have r2 : rho ^+ 2 = 729 / 1600 * eps ^+ 2 by rewrite /rho; field.
  have epsq : 0 <= eps ^+ 2 by rewrite exprn_ge0 // ltW.
  by rewrite r2; move: eta_eps epsq; clear; lra.
rewrite eF in cD1; rewrite eF in cD2; rewrite eF eX; rewrite eX in cJ.
have k1 := tensor_packing_net eps0 eps1 d1 k1t; rewrite eX in k1.
have k2 := tensor_packing_net eps0 eps1 d1 k2t; rewrite eX in k2.
exact: (tensor_packing_count F0 X0 (ler0n _ _) Q0 cN cD1 cD2 cI k1 k2 cJ q).
Qed.

End tensor_packing.
