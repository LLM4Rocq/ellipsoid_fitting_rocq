From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation gauss_moments.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets.
From GaussianAnalysis.comparison Require Import gauss_concentration slepian.
From GaussianAnalysis.comparison Require Import gauss_smoothing gordon.
From GaussianAnalysis.comparison Require Import escape.
From GaussianAnalysis.convex Require Import moreau.

(**md**************************************************************************)
(* # The convex Gaussian min-max theorem, in mean and concentration form      *)
(*                                                                            *)
(* Theorem 5.3 of Koehler and Sohn (arXiv 2608.27372, lines 4972-4990;        *)
(* Thrampoulidis, Oymak and Hassibi, Theorem 3), in a self-contained form     *)
(* that suffices for the paper's limits. Let A be an N x M matrix of          *)
(* independent standard normal entries (A = vec_mx a, a of law gauss (N * M)) *)
(* and g, h independent with laws gauss N and gauss M (g = lsubmx z and       *)
(* h = rsubmx z, z of law gauss (N + M)). For a nonempty set K of 'cV[R]_M    *)
(* with |x| <= rho on K, let                                                  *)
(*   Phi(K) = inf_(x in K) |A x|                  (escape_inf K A, escape.v), *)
(*   phi(K) = inf_(x in K) (|g| |x| - <h, x>)_+   (cgmt_aux K g h).           *)
(* Then:                                                                      *)
(* - cgmt_lower: for N > 0, E Phi(K) >= E phi(K) - rho;                       *)
(* - cgmt_upper: for K closed and convex, E Phi(K) <= E phi(K) + rho;         *)
(* - cgmt_escape_tail and cgmt_aux_tail: Phi(K) and phi(K) are at least u     *)
(*   away from their means with probability at most 2 exp (- u^2 / (2 rho^2)) *)
(*   and 2 exp (- u^2 / (4 rho^2)) (gauss_concentration.v);                   *)
(* - cgmt_tail: for N > 0 and K closed and convex, Phi(K) is at least rho + u *)
(*   away from E phi(K) with probability at most 2 exp (- u^2 / (2 rho^2)).   *)
(* In the paper's application rho is O(d) while Phi and phi are normalized by *)
(* d^(3/2), so the error rho vanishes: the normalized Phi and phi have the    *)
(* same limit in probability, which is what the comparisons                   *)
(* (eq:cgmt-comparisons) of the paper are used for.                           *)
(*                                                                            *)
(* The proofs. gordon_gamma is Gordon's inequality (gordon.v) for finite      *)
(* families rs u and cs t: the min-max over u and t of                        *)
(* |rs u| <g, cs t> + |cs t| <h, rs u> is in mean at most that of the         *)
(* bilinear process plus gamma |rs u| |cs t|, gamma an independent standard   *)
(* normal. infsup_compare extends it to bounded index sets by eps-nets        *)
(* (nets.v). The lower bound takes the index sets K and the unit ball, where  *)
(* sup_(|y| <= 1) (|x| <g, y> + |y| <h, x>) = (|g| |x| + <h, x>)_+; the term  *)
(* in gamma costs at most E |gamma| rho <= rho, and the sign of h changes by  *)
(* the symmetry of gauss. The upper bound exchanges the index sets and uses   *)
(* the minimax exchange escape_inf_minimax: for K closed and convex,          *)
(* inf_(x in K) |A x| <= sup_(|y| <= 1) inf_(x in K) <y, A x>, by the         *)
(* variational inequality at a minimizer of |A x| on the compact set K        *)
(* (closed_bounded_compact_cV).                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*  cgmt_aux K g h == inf_(x in K) (|g| |x| - <h, x>)_+                       *)
(*    infsup S T F == inf_(s in S) sup_(t in T) F s t                         *)
(*   auxg_mx rs cs == the matrix C such that vec_mx (z *m C) u t is           *)
(*                    |rs u| <lsubmx z, cs t> + |cs t| <rsubmx z, rs u>       *)
(*  auxgT_mx rs cs == the same with the two blocks of z exchanged             *)
(* bilg_mx rs cs B == the matrix C such that vec_mx (w *m C) u t is           *)
(*                    vec_mx (lsubmx w *m B) u t + rsubmx w 0 0 |rs u| |cs t| *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section gordon_gamma.
Context {R : realType} {P Q k l : nat}.
Variables (rs : 'I_k.+1 -> 'cV[R]_P) (cs : 'I_l.+1 -> 'cV[R]_Q).
Local Notation idx := (@mxvec_index k.+1 l.+1).

(* The row of the term gamma |rs u| |cs t|. *)
Definition nrm_mx : 'M[R]_(1, k.+1 * l.+1) :=
  \matrix_(i, c) (frobenius (rs (unvec c).1) * frobenius (cs (unvec c).2)).

(* For z of law gauss (Q + P), the Gaussian matrix whose entry (u, t) is
   |rs u| <lsubmx z, cs t> + |cs t| <rsubmx z, rs u>. *)
Definition auxg_mx : 'M[R]_(Q + P, k.+1 * l.+1) :=
  col_mx (\matrix_(i, c) (frobenius (rs (unvec c).1) * cs (unvec c).2 i 0))
         (\matrix_(j, c) (frobenius (cs (unvec c).2) * rs (unvec c).1 j 0)).

Lemma auxg_mxE (z : 'rV[R]_(Q + P)) u t :
  vec_mx (z *m auxg_mx) u t =
  frobenius (rs u) * mxdot (lsubmx z)^T (cs t) +
  frobenius (cs t) * mxdot (rsubmx z)^T (rs u).
Proof.
rewrite -[z]hsubmxK /auxg_mx mul_row_col row_mxKl row_mxKr mxE !mxE /mxdot.
congr (_ + _).
  rewrite mulr_sumr; apply: eq_bigr => i _.
  by rewrite big_ord1 !mxE unvecK /=; ring.
rewrite mulr_sumr; apply: eq_bigr => j _.
by rewrite big_ord1 !mxE unvecK /=; ring.
Qed.

Lemma auxg_cov u t v s :
  (auxg_mx^T *m auxg_mx) (idx u t) (idx v s) =
  frobenius (rs u) * frobenius (rs v) * mxdot (cs t) (cs s) +
  frobenius (cs t) * frobenius (cs s) * mxdot (rs u) (rs v).
Proof.
rewrite /auxg_mx tr_col_mx mul_row_col mxE !mxE /mxdot.
congr (_ + _).
  rewrite !mulr_sumr; apply: eq_bigr => i _.
  by rewrite big_ord1 !mxE !unvecK /=; ring.
rewrite !mulr_sumr; apply: eq_bigr => j _.
by rewrite big_ord1 !mxE !unvecK /=; ring.
Qed.

(* The same process with the blocks of z in the other order: for z of law
   gauss (P + Q), the entry (u, t) is
   |cs t| <lsubmx z, rs u> + |rs u| <rsubmx z, cs t>. *)
Definition auxgT_mx : 'M[R]_(P + Q, k.+1 * l.+1) :=
  col_mx (\matrix_(j, c) (frobenius (cs (unvec c).2) * rs (unvec c).1 j 0))
         (\matrix_(i, c) (frobenius (rs (unvec c).1) * cs (unvec c).2 i 0)).

Lemma auxgT_mxE (z : 'rV[R]_(P + Q)) u t :
  vec_mx (z *m auxgT_mx) u t =
  frobenius (cs t) * mxdot (lsubmx z)^T (rs u) +
  frobenius (rs u) * mxdot (rsubmx z)^T (cs t).
Proof.
rewrite -[z]hsubmxK /auxgT_mx mul_row_col row_mxKl row_mxKr mxE !mxE /mxdot.
congr (_ + _).
  rewrite mulr_sumr; apply: eq_bigr => j _.
  by rewrite big_ord1 !mxE unvecK /=; ring.
rewrite mulr_sumr; apply: eq_bigr => i _.
by rewrite big_ord1 !mxE unvecK /=; ring.
Qed.

Lemma auxgT_cov u t v s :
  (auxgT_mx^T *m auxgT_mx) (idx u t) (idx v s) =
  frobenius (rs u) * frobenius (rs v) * mxdot (cs t) (cs s) +
  frobenius (cs t) * frobenius (cs s) * mxdot (rs u) (rs v).
Proof.
rewrite /auxgT_mx tr_col_mx mul_row_col mxE !mxE /mxdot addrC.
congr (_ + _).
  rewrite !mulr_sumr; apply: eq_bigr => i _.
  by rewrite big_ord1 !mxE !unvecK /=; ring.
rewrite !mulr_sumr; apply: eq_bigr => j _.
by rewrite big_ord1 !mxE !unvecK /=; ring.
Qed.

Lemma nrm_cov u t v s :
  (nrm_mx^T *m nrm_mx) (idx u t) (idx v s) =
  frobenius (rs u) * frobenius (cs t) * (frobenius (rs v) * frobenius (cs s)).
Proof. by rewrite mxE big_ord1 !mxE !unvecK. Qed.

Variables (n : nat) (Bm : 'M[R]_(n, k.+1 * l.+1)).
Hypothesis Bcov : forall u t v s,
  (Bm^T *m Bm) (idx u t) (idx v s) = mxdot (rs u) (rs v) * mxdot (cs t) (cs s).

(* The bilinear process plus gamma |rs u| |cs t|, gamma the last coordinate
   of a vector of law gauss (n + 1). *)
Definition bilg_mx : 'M[R]_(n + 1, k.+1 * l.+1) := col_mx Bm nrm_mx.

Lemma bilg_mxE (w : 'rV[R]_(n + 1)) u t :
  vec_mx (w *m bilg_mx) u t = vec_mx (lsubmx w *m Bm) u t +
    rsubmx w 0 0 * (frobenius (rs u) * frobenius (cs t)).
Proof.
rewrite -[w]hsubmxK /bilg_mx mul_row_col row_mxKl row_mxKr.
rewrite [in LHS]raddfD /= mxE; congr (_ + _).
by rewrite !mxE big_ord1 !mxE unvecK.
Qed.

(* C is auxg_mx or auxgT_mx: only its covariance matters. *)
Variables (m : nat) (C : 'M[R]_(m, k.+1 * l.+1)).
Hypothesis Ccov : forall u t v s,
  (C^T *m C) (idx u t) (idx v s) =
  frobenius (rs u) * frobenius (rs v) * mxdot (cs t) (cs s) +
  frobenius (cs t) * frobenius (cs s) * mxdot (rs u) (rs v).

Lemma incr_var_gamma u t v s :
  incr_var C (idx u t) (idx v s) - incr_var bilg_mx (idx u t) (idx v s) =
  2 * (frobenius (rs u) * frobenius (rs v) - mxdot (rs u) (rs v)) *
      (frobenius (cs t) * frobenius (cs s) - mxdot (cs t) (cs s)).
Proof.
have eB j j' : (bilg_mx^T *m bilg_mx) j j' =
    (Bm^T *m Bm) j j' + (nrm_mx^T *m nrm_mx) j j'.
  by rewrite /bilg_mx tr_col_mx mul_row_col mxE.
rewrite /incr_var !eB !Bcov !nrm_cov !Ccov -!frobenius_sqr.
by ring.
Qed.

(* Gordon's comparison of the auxiliary process with the bilinear process
   plus gamma |rs u| |cs t|. *)
Lemma gordon_gamma :
  (\int[gauss m]_z (minmax (vec_mx (z *m C)))%:E <=
   \int[gauss (n + 1)]_w (minmax (vec_mx (w *m bilg_mx)))%:E)%E.
Proof.
apply: gordon.
  by move=> u t s; rewrite -subr_le0 incr_var_gamma -frobenius_sqr expr2 subrr
    mulr0 mul0r.
move=> u v t s _; rewrite -subr_ge0 incr_var_gamma.
by rewrite !mulr_ge0 // subr_ge0 ler_mxdot.
Qed.

End gordon_gamma.

Section infsup.
Context {R : realType} {P Q : nat}.
Variables (S : set 'cV[R]_P) (T : set 'cV[R]_Q).
Hypotheses (S0 : S !=set0) (T0 : T !=set0).
Implicit Types (F G : 'cV[R]_P -> 'cV[R]_Q -> R) (B L e : R).

(* inf_(s in S) sup_(t in T) F s t. *)
Definition infsup F : R := inf [set sup [set F s t | t in T] | s in S].

Section bounded.
Variables (F : 'cV[R]_P -> 'cV[R]_Q -> R) (B : R).
Hypothesis FB : forall s t, S s -> T t -> `|F s t| <= B.

Lemma sup_row_ub s t : S s -> T t -> F s t <= sup [set F s t | t in T].
Proof.
move=> Ss Tt; apply: ub_le_sup; last by exists t.
by exists B => _ [t' Tt' <-]; exact: le_trans (ler_norm _) (FB Ss Tt').
Qed.

Lemma sup_row_le s c : S s -> (forall t, T t -> F s t <= c) ->
  sup [set F s t | t in T] <= c.
Proof.
move=> Ss hc; have [t Tt] := T0.
by apply: ge_sup; [exists (F s t), t|move=> _ [t' Tt' <-]; exact: hc].
Qed.

Lemma sup_row_bound s : S s -> `|sup [set F s t | t in T]| <= B.
Proof.
move=> Ss; have [t Tt] := T0.
rewrite ler_norml; apply/andP; split.
  apply: le_trans (sup_row_ub Ss Tt).
  by have := FB Ss Tt; rewrite ler_norml => /andP[].
by apply: sup_row_le => // t' Tt'; exact: le_trans (ler_norm _) (FB Ss Tt').
Qed.

Lemma infsup_le s : S s -> infsup F <= sup [set F s t | t in T].
Proof.
move=> Ss; apply: ge_inf; last by exists s.
exists (- B) => _ [s' Ss' <-].
by have := sup_row_bound Ss'; rewrite ler_norml => /andP[].
Qed.

Lemma le_infsup c : (forall s, S s -> c <= sup [set F s t | t in T]) ->
  c <= infsup F.
Proof.
move=> hc; have [s Ss] := S0.
apply: lb_le_inf; first by exists (sup [set F s t | t in T]), s.
by move=> _ [s' Ss' <-]; exact: hc.
Qed.

Lemma infsup_bound : `|infsup F| <= B.
Proof.
have [s Ss] := S0.
rewrite ler_norml; apply/andP; split.
  apply: le_infsup => s' Ss'.
  by have := sup_row_bound Ss'; rewrite ler_norml => /andP[].
apply: le_trans (infsup_le Ss) _.
exact: le_trans (ler_norm _) (sup_row_bound Ss).
Qed.

End bounded.

(* infsup is 1-Lipschitz for the uniform distance on S x T. *)
Lemma infsup_lipschitz F G B c :
  (forall s t, S s -> T t -> `|F s t| <= B) ->
  (forall s t, S s -> T t -> `|G s t| <= B) ->
  (forall s t, S s -> T t -> `|F s t - G s t| <= c) ->
  `|infsup F - infsup G| <= c.
Proof.
move=> FB GB FG.
have h (F1 F2 : 'cV[R]_P -> 'cV[R]_Q -> R) :
    (forall s t, S s -> T t -> `|F1 s t| <= B) ->
    (forall s t, S s -> T t -> `|F2 s t| <= B) ->
    (forall s t, S s -> T t -> F1 s t <= F2 s t + c) ->
    infsup F1 - c <= infsup F2.
  move=> B1 B2 h12; apply: le_infsup => s Ss.
  rewrite lerBlDr; apply: le_trans (infsup_le B1 Ss) _.
  apply: (sup_row_le Ss) => t Tt.
  by have := h12 s t Ss Tt; have := sup_row_ub B2 Ss Tt; lra.
have h1 : infsup F - c <= infsup G.
  apply: h => // s t Ss Tt.
  by have := FG s t Ss Tt; rewrite ler_norml => /andP[_]; lra.
have h2 : infsup G - c <= infsup F.
  apply: h => // s t Ss Tt.
  by have := FG s t Ss Tt; rewrite ler_norml => /andP[]; lra.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(* Nets: if every point of S is within e of some rs u, every point of T
   within e of some cs t, and F is L-Lipschitz in each variable, the finite
   min-max is within L e of infsup F. *)
Lemma infsup_net k l (rs : 'I_k.+1 -> 'cV[R]_P) (cs : 'I_l.+1 -> 'cV[R]_Q)
    F B L e : 0 <= L ->
  (forall s t, S s -> T t -> `|F s t| <= B) ->
  (forall u, S (rs u)) -> (forall t, T (cs t)) ->
  (forall s, S s -> exists u, frobenius (s - rs u) <= e) ->
  (forall t, T t -> exists v, frobenius (t - cs v) <= e) ->
  (forall s s' t, S s -> S s' -> T t ->
     `|F s t - F s' t| <= L * frobenius (s - s')) ->
  (forall s t t', S s -> T t -> T t' ->
     `|F s t - F s t'| <= L * frobenius (t - t')) ->
  `|minmax (\matrix_(u, v) F (rs u) (cs v)) - infsup F| <= L * e.
Proof.
move=> L0 FB rsS csT rsnet csnet Ls Lt.
set M := \matrix_(u, v) F (rs u) (cs v).
have rowE u v : (row u M) 0 v = F (rs u) (cs v) by rewrite !mxE.
(* the finite min-max is at most infsup F + L e *)
have h1 : minmax M - L * e <= infsup F.
  apply: le_infsup => s Ss; have [u su] := rsnet s Ss.
  rewrite lerBlDr; apply: le_trans (minmax_le M u) _.
  apply: rmax_le => v; rewrite rowE.
  apply: le_trans (_ : F s (cs v) + L * e <= _); last first.
    by rewrite lerD2r; exact: (sup_row_ub FB Ss (csT v)).
  have := Ls _ _ _ (rsS u) Ss (csT v).
  rewrite -frobeniusN opprB => hL.
  have hLe : L * frobenius (s - rs u) <= L * e by rewrite ler_wpM2l.
  have := ler_norm (F (rs u) (cs v) - F s (cs v)).
  lra.
(* and at least infsup F - L e *)
have h2 : infsup F - L * e <= minmax M.
  apply: le_minmax => u.
  rewrite lerBlDr; apply: le_trans (infsup_le FB (rsS u)) _.
  apply: (sup_row_le (rsS u)) => t Tt; have [v tv] := csnet t Tt.
  apply: le_trans (_ : F (rs u) (cs v) + L * e <= _); last first.
    by rewrite lerD2r; have := le_rmax (row u M) v; rewrite rowE.
  have := Lt _ _ _ (rsS u) Tt (csT v).
  have hLe : L * frobenius (t - cs v) <= L * e by rewrite ler_wpM2l.
  have := ler_norm (F (rs u) t - F (rs u) (cs v)).
  lra.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

End infsup.

Section infsup_compare.
Context {R : realType} {P Q m1 m2 : nat}.
Variables (S : set 'cV[R]_P) (T : set 'cV[R]_Q) (rhoS rhoT c : R).
Hypotheses (S0 : S !=set0) (T0 : T !=set0).
Hypotheses (Sb : forall s, S s -> frobenius s <= rhoS)
  (Tb : forall t, T t -> frobenius t <= rhoT).
Variables (X : 'rV[R]_m1 -> 'cV[R]_P -> 'cV[R]_Q -> R)
  (Y : 'rV[R]_m2 -> 'cV[R]_P -> 'cV[R]_Q -> R).
Hypothesis c0 : 0 <= c.
(* X and Y are bounded, Lipschitz in the index and in the Gaussian vector *)
Hypothesis Xb : forall w s t, S s -> T t -> `|X w s t| <= c * frobenius w.
Hypothesis Yb : forall z s t, S s -> T t -> `|Y z s t| <= c * frobenius z.
Hypothesis Xs : forall w s s' t, S s -> S s' -> T t ->
  `|X w s t - X w s' t| <= c * frobenius w * frobenius (s - s').
Hypothesis Xt : forall w s t t', S s -> T t -> T t' ->
  `|X w s t - X w s t'| <= c * frobenius w * frobenius (t - t').
Hypothesis Ys : forall z s s' t, S s -> S s' -> T t ->
  `|Y z s t - Y z s' t| <= c * frobenius z * frobenius (s - s').
Hypothesis Yt : forall z s t t', S s -> T t -> T t' ->
  `|Y z s t - Y z s t'| <= c * frobenius z * frobenius (t - t').
Hypothesis Xw : forall w w' s t, S s -> T t ->
  `|X w s t - X w' s t| <= c * frobenius (w - w').
Hypothesis Yz : forall z z' s t, S s -> T t ->
  `|Y z s t - Y z' s t| <= c * frobenius (z - z').
(* the comparison for finite families *)
Hypothesis XY : forall k l (rs : 'I_k.+1 -> 'cV[R]_P)
    (cs : 'I_l.+1 -> 'cV[R]_Q), (forall u, S (rs u)) -> (forall t, T (cs t)) ->
  (\int[gauss m2]_z (minmax (\matrix_(u, t) Y z (rs u) (cs t)))%:E <=
   \int[gauss m1]_w (minmax (\matrix_(u, t) X w (rs u) (cs t)))%:E)%E.

Lemma integrable_infsupX :
  (gauss m1).-integrable setT (EFin \o (fun w => infsup S T (X w))).
Proof.
apply: (@integrable_gauss_lipschitz _ _ _ c) => w w'.
apply: (@infsup_lipschitz _ _ _ S T S0 T0 _ _
  (c * (frobenius w + frobenius w'))).
- move=> s t Ss Tt; apply: le_trans (Xb w Ss Tt) _.
  by rewrite ler_wpM2l // lerDl frobenius_ge0.
- move=> s t Ss Tt; apply: le_trans (Xb w' Ss Tt) _.
  by rewrite ler_wpM2l // lerDr frobenius_ge0.
- by move=> s t Ss Tt; exact: Xw.
Qed.

Lemma integrable_infsupY :
  (gauss m2).-integrable setT (EFin \o (fun z => infsup S T (Y z))).
Proof.
apply: (@integrable_gauss_lipschitz _ _ _ c) => z z'.
apply: (@infsup_lipschitz _ _ _ S T S0 T0 _ _
  (c * (frobenius z + frobenius z'))).
- move=> s t Ss Tt; apply: le_trans (Yb z Ss Tt) _.
  by rewrite ler_wpM2l // lerDl frobenius_ge0.
- move=> s t Ss Tt; apply: le_trans (Yb z' Ss Tt) _.
  by rewrite ler_wpM2l // lerDr frobenius_ge0.
- by move=> s t Ss Tt; exact: Yz.
Qed.

(* Gordon's comparison for bounded index sets. *)
Theorem infsup_compare :
  \int[gauss m2]_z infsup S T (Y z) <= \int[gauss m1]_w infsup S T (X w).
Proof.
have iX := integrable_infsupX; have iY := integrable_infsupY.
have iFX := @integrable_gauss_frobenius R m1.
have iFZ := @integrable_gauss_frobenius R m2.
pose EX : R := \int[gauss m1]_w frobenius (w : 'rV[R]_m1).
pose EZ : R := \int[gauss m2]_z frobenius (z : 'rV[R]_m2).
have EX0 : 0 <= EX by apply: Rintegral_ge0 => w _; exact: frobenius_ge0.
have EZ0 : 0 <= EZ by apply: Rintegral_ge0 => z _; exact: frobenius_ge0.
have [s0 Ss0] := S0; have [t0 Tt0] := T0.
have rS0 : 0 <= rhoS := le_trans (frobenius_ge0 _) (Sb Ss0).
have rT0 : 0 <= rhoT := le_trans (frobenius_ge0 _) (Tb Tt0).
apply/ler_addgt0Pr => e e0.
have C0 : 0 < c * (EX + EZ) + 1 by rewrite ltr_wpDl // mulr_ge0 // addr_ge0.
pose eps := e / (c * (EX + EZ) + 1).
have eps0 : 0 < eps by rewrite divr_gt0.
have epsC : c * eps * (EX + EZ) <= e.
  have -> : c * eps * (EX + EZ) = e * (c * (EX + EZ) / (c * (EX + EZ) + 1)).
    have Cne : c * (EX + EZ) + 1 != 0 by rewrite gt_eqF.
    by rewrite /eps; field.
  rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; first exact: ltW.
  by rewrite ler_pdivrMr // mul1r lerDl.
(* eps-nets of S and of T *)
have [Ns [NsS Nsnet _]] := @net_exists R P S rhoS eps rS0 eps0 Sb.
case: Ns NsS Nsnet => [|x0 Ns] NsS Nsnet; first by have [y] := Nsnet _ Ss0.
have [Nt [NtT Ntnet _]] := @net_exists R Q T rhoT eps rT0 eps0 Tb.
case: Nt NtT Ntnet => [|y0 Nt] NtT Ntnet; first by have [y] := Ntnet _ Tt0.
pose rs (u : 'I_(size Ns).+1) := nth 0 (x0 :: Ns) u.
pose cs (t : 'I_(size Nt).+1) := nth 0 (y0 :: Nt) t.
have rsS u : S (rs u) by apply: NsS; rewrite mem_nth.
have csT t : T (cs t) by apply: NtT; rewrite mem_nth.
have rsnet s : S s -> exists u, frobenius (s - rs u) <= eps.
  move=> Ss; have [y yN sy] := Nsnet s Ss.
  have yi : (index y (x0 :: Ns) < (size Ns).+1)%N.
    by rewrite -[X in (_ < X)%N]/(size (x0 :: Ns)) index_mem.
  by exists (Ordinal yi); rewrite /rs /= nth_index.
have csnet t : T t -> exists v, frobenius (t - cs v) <= eps.
  move=> Tt; have [y yN ty] := Ntnet t Tt.
  have yi : (index y (y0 :: Nt) < (size Nt).+1)%N.
    by rewrite -[X in (_ < X)%N]/(size (y0 :: Nt)) index_mem.
  by exists (Ordinal yi); rewrite /cs /= nth_index.
(* the finite min-max functionals are c-Lipschitz, hence integrable *)
pose MX w := minmax (\matrix_(u, t) X w (rs u) (cs t)).
pose MY z := minmax (\matrix_(u, t) Y z (rs u) (cs t)).
have MXlip w w' : `|MX w - MX w'| <= c * frobenius (w - w').
  apply: le_trans (minmax_lipschitz _ _) _.
  set Z := _ - _.
  have -> : `|Z| = \big[maxr/0]_ij `|Z ij.1 ij.2| by rewrite -mx_normrE.
  apply: bigmax_le => [|ij _]; first by rewrite mulr_ge0 // frobenius_ge0.
  by rewrite /Z !mxE; exact: Xw.
have MYlip z z' : `|MY z - MY z'| <= c * frobenius (z - z').
  apply: le_trans (minmax_lipschitz _ _) _.
  set Z := _ - _.
  have -> : `|Z| = \big[maxr/0]_ij `|Z ij.1 ij.2| by rewrite -mx_normrE.
  apply: bigmax_le => [|ij _]; first by rewrite mulr_ge0 // frobenius_ge0.
  by rewrite /Z !mxE; exact: Yz.
have iMX := integrable_gauss_lipschitz MXlip.
have iMY := integrable_gauss_lipschitz MYlip.
(* pointwise comparisons with the nets *)
have hY z : infsup S T (Y z) <= MY z + c * eps * frobenius z.
  have := @infsup_net _ _ _ S T S0 T0 _ _ rs cs (Y z) (c * frobenius z)
    (c * frobenius z) eps (mulr_ge0 c0 (frobenius_ge0 _)) (Yb z) rsS csT
    rsnet csnet (Ys z) (Yt z).
  rewrite ler_norml => /andP[h _].
  by rewrite -/(MY z) mulrAC; lra.
have hX w : MX w <= infsup S T (X w) + c * eps * frobenius w.
  have := @infsup_net _ _ _ S T S0 T0 _ _ rs cs (X w) (c * frobenius w)
    (c * frobenius w) eps (mulr_ge0 c0 (frobenius_ge0 _)) (Xb w) rsS csT
    rsnet csnet (Xs w) (Xt w).
  rewrite ler_norml => /andP[_ h].
  by rewrite -/(MX w) mulrAC; lra.
(* integrate *)
have iZ : (gauss m2).-integrable setT
    (EFin \o (fun z : 'rV[R]_m2 => c * eps * frobenius z)).
  have := integrableZl measurableT (c * eps) iFZ.
  by apply: eq_integrable => // z _.
have iW : (gauss m1).-integrable setT
    (EFin \o (fun w : 'rV[R]_m1 => c * eps * frobenius w)).
  have := integrableZl measurableT (c * eps) iFX.
  by apply: eq_integrable => // w _.
have iS1 : (gauss m2).-integrable setT
    (EFin \o (fun z => MY z + c * eps * frobenius z)).
  have := integrableD measurableT iMY iZ.
  by apply: eq_integrable => // z _; rewrite /= EFinD.
have h1 : \int[gauss m2]_z infsup S T (Y z) <=
    \int[gauss m2]_z MY z + c * eps * EZ.
  rewrite /EZ -RintegralZl // -RintegralD //.
  by apply: le_Rintegral => // z _; exact: hY.
have h2 : \int[gauss m2]_z MY z <= \int[gauss m1]_w MX w.
  apply: fine_le; [exact: integrable_fin_num|exact: integrable_fin_num|].
  exact: XY.
have iS3 : (gauss m1).-integrable setT
    (EFin \o (fun w => infsup S T (X w) + c * eps * frobenius w)).
  have := integrableD measurableT iX iW.
  by apply: eq_integrable => // w _; rewrite /= EFinD.
have h3 : \int[gauss m1]_w MX w <=
    \int[gauss m1]_w infsup S T (X w) + c * eps * EX.
  rewrite /EX -RintegralZl // -RintegralD //.
  by apply: le_Rintegral => // w _; exact: hX.
by have := mulr_ge0 (mulr_ge0 c0 (ltW eps0)) EX0; lra.
Qed.

End infsup_compare.

Section block_norms.
Context {R : realType}.

Lemma frobenius_hsub_sqr m n1 n2 (w : 'M[R]_(m, n1 + n2)) :
  frobenius w ^+ 2 = frobenius (lsubmx w) ^+ 2 + frobenius (rsubmx w) ^+ 2.
Proof.
by rewrite !frobenius_sqr -[in LHS](hsubmxK w) !mxdot_trace tr_row_mx
  mul_row_col mxtraceD.
Qed.

Lemma frobenius_lsubmx_le m n1 n2 (w : 'M[R]_(m, n1 + n2)) :
  frobenius (lsubmx w) <= frobenius w.
Proof.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 // (frobenius_hsub_sqr w).
by rewrite lerDl sqr_ge0.
Qed.

Lemma frobenius_rsubmx_le m n1 n2 (w : 'M[R]_(m, n1 + n2)) :
  frobenius (rsubmx w) <= frobenius w.
Proof.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 // (frobenius_hsub_sqr w).
by rewrite lerDr sqr_ge0.
Qed.

Lemma frobenius_hsub_add m n1 n2 (w : 'M[R]_(m, n1 + n2)) :
  frobenius (lsubmx w) + frobenius (rsubmx w) <= Num.sqrt 2 * frobenius w.
Proof.
have p0 := frobenius_ge0 (lsubmx w); have q0 := frobenius_ge0 (rsubmx w).
rewrite -ler_sqr ?nnegrE ?addr_ge0 ?mulr_ge0 ?sqrtr_ge0 ?frobenius_ge0 //.
rewrite exprMn sqr_sqrtr ?ler0n // (frobenius_hsub_sqr w).
have := sqr_ge0 (frobenius (lsubmx w) - frobenius (rsubmx w)).
by nra.
Qed.

Lemma mxdot_mulmx_le n m (A : 'M[R]_(n, m)) (x : 'cV[R]_m) (y : 'cV[R]_n) :
  `|mxdot y (A *m x)| <= frobenius y * (frobenius A * frobenius x).
Proof.
apply: le_trans (mxdot_le _ _) _.
by rewrite ler_wpM2l ?frobenius_ge0 // frobenius_mulmx.
Qed.

(* A unit vector of 'cV[R]_n on which <g, y> = |g|. *)
Lemma unit_dir n (g : 'rV[R]_n) : (0 < n)%N ->
  exists y : 'cV[R]_n, frobenius y = 1 /\ mxdot g^T y = frobenius g.
Proof.
move=> n0; have [->|g0] := eqVneq g 0.
  exists (delta_mx (Ordinal n0) 0); split.
    by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1.
  by rewrite trmx0 mxdot0l frobenius0.
have fg : 0 < frobenius g by rewrite frobenius_gt0.
exists ((frobenius g)^-1 *: g^T); split.
  rewrite frobeniusZ frobenius_trmx ger0_norm ?invr_ge0 ?(ltW fg) //.
  by rewrite mulVf // gt_eqF.
rewrite mxdotZr -frobenius_sqr frobenius_trmx expr2 mulrA mulVf ?mul1r //.
by rewrite gt_eqF.
Qed.

(* max (0, a) <= max (0, b) + c when a <= b + c and c >= 0. *)
Lemma max0_leD (a b c : R) : 0 <= c -> a <= b + c ->
  Num.max 0 a <= Num.max 0 b + c.
Proof.
move=> c0 h; rewrite ge_max; apply/andP; split.
  by rewrite addr_ge0 // le_max lexx.
by apply: le_trans h _; rewrite lerD2r le_max lexx orbT.
Qed.

End block_norms.

Section cgmt_aux.
Context {R : realType} {N M : nat}.
Variable K : set 'cV[R]_M.
Hypothesis K0 : K !=set0.

(* phi(K) at g and h: inf_(x in K) (|g| |x| - <h, x>)_+. *)
Definition cgmt_aux (g : 'rV[R]_N) (h : 'rV[R]_M) : R :=
  inf [set Num.max 0 (frobenius g * frobenius x - mxdot h^T x) | x in K].

Lemma cgmt_aux_le g h x : K x ->
  cgmt_aux g h <= Num.max 0 (frobenius g * frobenius x - mxdot h^T x).
Proof.
move=> Kx; apply: ge_inf; last by exists x.
by exists 0 => _ [y Ky <-]; rewrite le_max lexx.
Qed.

Lemma cgmt_aux_ge g h c :
  (forall x, K x -> c <= Num.max 0 (frobenius g * frobenius x - mxdot h^T x)) ->
  c <= cgmt_aux g h.
Proof.
move=> hc; apply: lb_le_inf.
  case: K0 => x Kx.
  by exists (Num.max 0 (frobenius g * frobenius x - mxdot h^T x)), x.
by move=> _ [x Kx <-]; exact: hc.
Qed.

Lemma cgmt_aux_ge0 g h : 0 <= cgmt_aux g h.
Proof. by apply: cgmt_aux_ge => x _; rewrite le_max lexx. Qed.

(* phi(K) does not change when (g, h) is replaced by (- g, h). *)
Lemma cgmt_auxNl g h : cgmt_aux (- g) h = cgmt_aux g h.
Proof. by rewrite /cgmt_aux frobeniusN. Qed.

Variable rho : R.
Hypothesis Kb : forall x, K x -> frobenius x <= rho.

Lemma cgmt_aux_lipschitz (z z' : 'rV[R]_(N + M)) :
  `|cgmt_aux (lsubmx z) (rsubmx z) - cgmt_aux (lsubmx z') (rsubmx z')| <=
  Num.sqrt 2 * rho * frobenius (z - z').
Proof.
have rho0 : 0 <= rho.
  by case: K0 => x Kx; exact: le_trans (frobenius_ge0 _) (Kb Kx).
have key (u v : 'rV[R]_(N + M)) :
    cgmt_aux (lsubmx u) (rsubmx u) <=
    cgmt_aux (lsubmx v) (rsubmx v) + Num.sqrt 2 * rho * frobenius (u - v).
  rewrite -lerBlDr; apply: cgmt_aux_ge => x Kx; rewrite lerBlDr.
  apply: le_trans (cgmt_aux_le _ _ Kx) _.
  apply: max0_leD; first by rewrite !mulr_ge0 // ?sqrtr_ge0 ?frobenius_ge0.
  have hx := Kb Kx; have x0 := frobenius_ge0 x.
  have hg := ler_frobeniusB (lsubmx u) (lsubmx v).
  have hh := mxdot_le (rsubmx u - rsubmx v)^T x.
  have e1 : (frobenius (lsubmx u) - frobenius (lsubmx v)) * frobenius x <=
      frobenius (lsubmx u - lsubmx v) * rho.
    apply: le_trans (ler_norm _) _; rewrite normrM (ger0_norm x0).
    by apply: ler_pM => //; exact: normr_ge0.
  have e2 : - mxdot (rsubmx u - rsubmx v)^T x <=
      frobenius (rsubmx u - rsubmx v) * rho.
    apply: le_trans (_ : _ <= `|mxdot (rsubmx u - rsubmx v)^T x|) _.
      by rewrite -normrN ler_norm.
    apply: le_trans hh _; rewrite frobenius_trmx.
    by apply: ler_wpM2l => //; exact: frobenius_ge0.
  have e3 := frobenius_hsub_add (u - v).
  rewrite !linearB /= in e3.
  have e4 : (frobenius (lsubmx u - lsubmx v) + frobenius (rsubmx u - rsubmx v))
      * rho <= Num.sqrt 2 * frobenius (u - v) * rho.
    by apply: ler_wpM2r.
  rewrite linearB mxdotBl /= in e2.
  have -> : Num.sqrt 2 * rho * frobenius (u - v) =
      Num.sqrt 2 * frobenius (u - v) * rho by rewrite mulrAC.
  by lra.
rewrite ler_norml; have := key z z'; have := key z' z.
rewrite -frobeniusN opprB; lra.
Qed.

End cgmt_aux.

Section cV_compact.
Context {R : realType}.

Lemma mx_norm_frobenius m n (B : 'M[R]_(m, n)) : `|B| <= frobenius B.
Proof.
have -> : `|B| = \big[maxr/0]_ij `|B ij.1 ij.2| by rewrite -mx_normrE.
apply: bigmax_le => [|ij _]; first exact: frobenius_ge0.
exact: frobenius_entry.
Qed.

Lemma continuous_trmx m n : continuous (fun B : 'M[R]_(m, n) => B^T).
Proof.
move=> B A /nbhs_ballP [d d0 dA]; apply/nbhs_ballP; exists d => // C.
rewrite /= -ball_normE /= => BC; apply: dA; rewrite /= -ball_normE /=.
apply: le_lt_trans BC.
have -> : B^T - C^T = (B - C)^T by rewrite linearB.
have -> : `|(B - C)^T| = \big[maxr/0]_ij `|(B - C)^T ij.1 ij.2|.
  by rewrite -mx_normrE.
apply: bigmax_le => [|ij _]; first exact: normr_ge0.
by rewrite mxE; exact: mx_norm_entry_le.
Qed.

(* A closed and bounded set of column vectors is compact. *)
Lemma closed_bounded_compact_cV n (A : set 'cV[R]_n) (r : R) :
  closed A -> (forall x, A x -> frobenius x <= r) -> compact A.
Proof.
move=> Ac Ab.
have A'c : closed [set w : 'rV[R]_n | A w^T].
  exact: (continuous_closedP _).1 (@continuous_trmx 1 n) _ Ac.
have A'b : bounded_set [set w : 'rV[R]_n | A w^T].
  exists r; split; first exact: num_real.
  move=> s hs w Aw; apply: ltW; apply: le_lt_trans hs.
  apply: le_trans (mx_norm_frobenius w) _.
  by rewrite -frobenius_trmx; exact: Ab.
have := continuous_compact (continuous_subspaceT (@continuous_trmx 1 n))
  (bounded_closed_compact A'b A'c).
congr compact; apply/seteqP; split => [_ [w Aw <-] //|x Ax].
by exists x^T; rewrite /= trmxK.
Qed.

End cV_compact.

Section minimax.
Context {R : realType} {N M : nat}.
Variables (K : set 'cV[R]_M) (rho : R).
Hypotheses (K0 : K !=set0) (Kb : forall x, K x -> frobenius x <= rho).

Lemma continuous_frobenius_mulmx (A : 'M[R]_(N, M)) :
  continuous (fun x : 'cV[R]_M => frobenius (A *m x)).
Proof.
move=> x.
pose c := (frobenius A + 1) * ((M * 1)%:R + 1).
have c0 : 0 < c by rewrite mulr_gt0 // ltr_wpDl // ?frobenius_ge0 ?ler0n.
have Fc y : `|frobenius (A *m x) - frobenius (A *m y)| <= c * `|x - y|.
  apply: le_trans (ler_frobeniusB _ _) _.
  rewrite -mulmxBr; apply: le_trans (frobenius_mulmx _ _) _.
  rewrite /c -mulrA; apply: ler_pM; rewrite ?frobenius_ge0 ?lerDl //.
  apply: le_trans (frobenius_le_mx_norm _) _.
  by rewrite ler_wpM2r // lerDl.
move=> B /nbhs_ballP [d d0 dB]; apply/nbhs_ballP.
exists (d / c); first by rewrite /= divr_gt0.
move=> y; rewrite /= -ball_normE /= => xy; apply: dB; rewrite -ball_normE /=.
by rewrite (le_lt_trans (Fc y)) // mulrC -ltr_pdivlMr.
Qed.

(* inf_(x in K) |A x| is rho-Lipschitz in A. *)
Lemma escape_inf_lip (A A' : 'M[R]_(N, M)) :
  `|escape_inf K A - escape_inf K A'| <= rho * frobenius (A - A').
Proof.
have key (A1 A2 : 'M[R]_(N, M)) :
    escape_inf K A1 <= escape_inf K A2 + rho * frobenius (A1 - A2).
  rewrite -lerBlDr; apply: (escape_inf_ge K0) => x Kx; rewrite lerBlDr.
  apply: (le_trans (escape_inf_le A1 Kx)).
  have -> : A1 *m x = A2 *m x + (A1 - A2) *m x by rewrite mulmxBl addrC subrK.
  rewrite (le_trans (frobeniusD _ _)) // lerD2l.
  rewrite (le_trans (frobenius_mulmx _ _)) // mulrC.
  by apply: ler_wpM2r; [exact: frobenius_ge0|exact: Kb].
rewrite ler_norml; have := key A A'; have := key A' A.
rewrite -frobeniusN opprB; lra.
Qed.

Hypothesis Kc : closed K.
Hypothesis Kcvx : forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
  K (x + t *: (y - x)).

(* The minimax exchange: for K convex and compact,
   inf_(x in K) |A x| <= sup_(|y| <= 1) inf_(x in K) <y, A x>, written as
   - inf_(|y| <= 1) sup_(x in K) <y, A x> since the unit ball is symmetric.
   The y is the direction of the point of A K nearest to 0. *)
Lemma escape_inf_minimax (A : 'M[R]_(N, M)) :
  escape_inf K A <= - infsup (@unit_ball R N) K (fun y x => mxdot y (A *m x)).
Proof.
have Kcp := closed_bounded_compact_cV Kc Kb.
have cf := @continuous_frobenius_mulmx A.
have [x0 Kx0 xmin] := compact_EVT_min K0 Kcp (continuous_subspaceT cf).
move: Kx0; rewrite inE => Kx0.
set p := A *m x0.
(* the variational inequality at the minimizer *)
have hvar x : K x -> mxdot p p <= mxdot p (A *m x).
  move=> Kx; set d := A *m (x - x0).
  have h0 : - mxdot p d <= 0.
    apply: (@le0_small _ _ (mxdot d d / 2)) => t /andP[t0 t1].
    have Kt : K (x0 + t *: (x - x0)) by apply: Kcvx => //; rewrite (ltW t0).
    have hle : frobenius p <= frobenius (A *m (x0 + t *: (x - x0))).
      by apply: xmin; rewrite inE.
    have hsq : mxdot p p <=
        mxdot (A *m (x0 + t *: (x - x0))) (A *m (x0 + t *: (x - x0))).
      by rewrite -!frobenius_sqr; apply: ler_pM; rewrite ?frobenius_ge0.
    rewrite mulmxDr -scalemxAr -/p -/d in hsq.
    rewrite !mxdotDl !mxdotDr !mxdotZl !mxdotZr (mxdotC d p) in hsq.
    have h2 : 2 * t * (- mxdot p d) <= t ^+ 2 * mxdot d d by nra.
    have t2 : 0 < 2 * t by rewrite mulr_gt0.
    rewrite -(ler_pM2l t2); apply: le_trans h2 _.
    by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
  by move: h0; rewrite /d mulmxBr mxdotBr -/p; lra.
(* the direction of p *)
set ys := (frobenius p)^-1 *: p.
have ys1 : (@unit_ball R N) (- ys).
  rewrite /unit_ball /= frobeniusN frobeniusZ ger0_norm ?invr_ge0
    ?frobenius_ge0 //.
  have [->|p0] := eqVneq (frobenius p) 0; first by rewrite invr0 mul0r ler01.
  by rewrite mulVf.
have hys x : K x -> frobenius p <= mxdot ys (A *m x).
  move=> Kx; have [p0|p0] := eqVneq (frobenius p) 0.
    by rewrite /ys p0 invr0 scale0r mxdot0l.
  have fp : 0 < frobenius p by rewrite lt_def p0 frobenius_ge0.
  rewrite /ys mxdotZl -(ler_pM2l fp) mulrA mulfV // mul1r -expr2.
  by rewrite frobenius_sqr; exact: hvar.
have FB y x : (@unit_ball R N) y -> K x ->
    `|mxdot y (A *m x)| <= frobenius A * rho.
  move=> By Kx; apply: le_trans (mxdot_mulmx_le _ _ _) _.
  rewrite -[X in _ <= X]mul1r; apply: ler_pM; rewrite ?frobenius_ge0 //.
    by rewrite mulr_ge0 // frobenius_ge0.
  by apply: ler_wpM2l; [exact: frobenius_ge0|exact: Kb].
have h1 := infsup_le K0 FB ys1.
have h2 : sup [set mxdot (- ys) (A *m x) | x in K] <= - frobenius p.
  apply: (@sup_row_le _ _ _ (@unit_ball R N) K K0
    (fun y x => mxdot y (A *m x)) (- ys) _ ys1) => x Kx.
  by rewrite mxdotNl lerN2; exact: hys.
have h3 := escape_inf_le A Kx0.
by rewrite -/p in h3; lra.
Qed.

End minimax.

Section cgmt_mean.
Context {R : realType} {N M : nat}.
Variables (K : set 'cV[R]_M) (rho : R).
Hypotheses (K0 : K !=set0) (Kb : forall x, K x -> frobenius x <= rho).
Local Notation B := (@unit_ball R N).

Let rho0 : 0 <= rho.
Proof. by case: K0 => x Kx; exact: le_trans (frobenius_ge0 _) (Kb Kx). Qed.

Let B0 : B !=set0.
Proof. by exists 0; exact: unit_ball0. Qed.

Let Bb y : B y -> frobenius y <= 1.
Proof. by []. Qed.

(* y^T A x + gamma |x| |y|, for w = (a, gamma) and A = vec_mx a. *)
Let Xp (w : 'rV[R]_(N * M + 1)) (x : 'cV[R]_M) (y : 'cV[R]_N) : R :=
  mxdot y ((vec_mx (lsubmx w) : 'M[R]_(N, M)) *m x) +
  rsubmx w 0 0 * (frobenius x * frobenius y).

(* |x| <g, y> + |y| <h, x>, for z = (g, h). *)
Let Yp (z : 'rV[R]_(N + M)) (x : 'cV[R]_M) (y : 'cV[R]_N) : R :=
  frobenius x * mxdot (lsubmx z)^T y + frobenius y * mxdot (rsubmx z)^T x.

Let c := 2 * (rho + 1).

Let c0 : 0 <= c.
Proof. by rewrite /c; apply: mulr_ge0 => //; apply: addr_ge0 => //; exact: rho0.
Qed.

Let le3 (a b d a' b' d' : R) : 0 <= a -> 0 <= b -> 0 <= d ->
  a <= a' -> b <= b' -> d <= d' -> a * (b * d) <= a' * (b' * d').
Proof.
move=> a0 b0 d0 aa bb dd; apply: ler_pM => //; first exact: mulr_ge0.
exact: ler_pM.
Qed.

Let nA (w : 'rV[R]_(N * M + 1)) :
  frobenius (vec_mx (lsubmx w) : 'M[R]_(N, M)) <= frobenius w.
Proof. by rewrite frobenius_vec_mx frobenius_lsubmx_le. Qed.

Let ng (w : 'rV[R]_(N * M + 1)) : `|rsubmx w 0 0| <= frobenius w.
Proof. exact: le_trans (frobenius_entry _ _ _) (frobenius_rsubmx_le _). Qed.

Let dotg (z : 'rV[R]_(N + M)) (y : 'cV[R]_N) :
  `|mxdot (lsubmx z)^T y| <= frobenius z * frobenius y.
Proof.
apply: le_trans (mxdot_le _ _) _; rewrite frobenius_trmx.
by apply: ler_wpM2r; [exact: frobenius_ge0|exact: frobenius_lsubmx_le].
Qed.

Let doth (z : 'rV[R]_(N + M)) (x : 'cV[R]_M) :
  `|mxdot (rsubmx z)^T x| <= frobenius z * frobenius x.
Proof.
apply: le_trans (mxdot_le _ _) _; rewrite frobenius_trmx.
by apply: ler_wpM2r; [exact: frobenius_ge0|exact: frobenius_rsubmx_le].
Qed.

Let Xp_b w x y : K x -> B y -> `|Xp w x y| <= c * frobenius w.
Proof.
move=> Kx By; have hx := Kb Kx; have hy := Bb By.
have x0 := frobenius_ge0 x; have y0 := frobenius_ge0 y.
have w0 := frobenius_ge0 w; have hA := nA w; have hg := ng w.
have A0 := frobenius_ge0 (vec_mx (lsubmx w) : 'M[R]_(N, M)).
have g0 := normr_ge0 (rsubmx w 0 0).
have e1 : `|mxdot y ((vec_mx (lsubmx w) : 'M[R]_(N, M)) *m x)| <=
    1 * (frobenius w * rho).
  by apply: le_trans (mxdot_mulmx_le _ _ _) _; apply: le3.
have e2 : `|rsubmx w 0 0 * (frobenius x * frobenius y)| <=
    frobenius w * (rho * 1).
  by rewrite normrM (ger0_norm (mulr_ge0 x0 y0)); apply: le3.
have := ler_normD (mxdot y ((vec_mx (lsubmx w) : 'M[R]_(N, M)) *m x))
  (rsubmx w 0 0 * (frobenius x * frobenius y)).
rewrite /Xp /c; have := mulr_ge0 w0 rho0; lra.
Qed.

Let Xp_x w x x' y : K x -> K x' -> B y ->
  `|Xp w x y - Xp w x' y| <= c * frobenius w * frobenius (x - x').
Proof.
move=> Kx Kx' By; have hy := Bb By.
have y0 := frobenius_ge0 y; have w0 := frobenius_ge0 w.
have d0 := frobenius_ge0 (x - x'); have hA := nA w; have hg := ng w.
have g0 := normr_ge0 (rsubmx w 0 0).
have hd := ler_frobeniusB x x'.
have d1 := normr_ge0 (frobenius x - frobenius x').
set A : 'M[R]_(N, M) := vec_mx (lsubmx w).
have A0 := frobenius_ge0 A.
have -> : Xp w x y - Xp w x' y = mxdot y (A *m (x - x')) +
    rsubmx w 0 0 * ((frobenius x - frobenius x') * frobenius y).
  by rewrite /Xp -/A mulmxBr mxdotBr; ring.
have e1 : `|mxdot y (A *m (x - x'))| <=
    1 * (frobenius w * frobenius (x - x')).
  by apply: le_trans (mxdot_mulmx_le _ _ _) _; apply: le3.
have e2 : `|rsubmx w 0 0 * ((frobenius x - frobenius x') * frobenius y)| <=
    frobenius w * (frobenius (x - x') * 1).
  by rewrite normrM normrM (ger0_norm y0); apply: le3.
have := ler_normD (mxdot y (A *m (x - x')))
  (rsubmx w 0 0 * ((frobenius x - frobenius x') * frobenius y)).
rewrite /c; have := mulr_ge0 (mulr_ge0 rho0 w0) d0; lra.
Qed.

Let Xp_y w x y y' : K x -> B y -> B y' ->
  `|Xp w x y - Xp w x y'| <= c * frobenius w * frobenius (y - y').
Proof.
move=> Kx By By'; have hx := Kb Kx.
have x0 := frobenius_ge0 x; have w0 := frobenius_ge0 w.
have d0 := frobenius_ge0 (y - y'); have hA := nA w; have hg := ng w.
have g0 := normr_ge0 (rsubmx w 0 0).
have hd := ler_frobeniusB y y'.
have d1 := normr_ge0 (frobenius y - frobenius y').
set A : 'M[R]_(N, M) := vec_mx (lsubmx w).
have A0 := frobenius_ge0 A.
have -> : Xp w x y - Xp w x y' = mxdot (y - y') (A *m x) +
    rsubmx w 0 0 * (frobenius x * (frobenius y - frobenius y')).
  by rewrite /Xp -/A mxdotBl; ring.
have e1 : `|mxdot (y - y') (A *m x)| <=
    frobenius (y - y') * (frobenius w * rho).
  by apply: le_trans (mxdot_mulmx_le _ _ _) _; apply: le3.
have e2 : `|rsubmx w 0 0 * (frobenius x * (frobenius y - frobenius y'))| <=
    frobenius w * (rho * frobenius (y - y')).
  by rewrite normrM normrM (ger0_norm x0); apply: le3.
have := ler_normD (mxdot (y - y') (A *m x))
  (rsubmx w 0 0 * (frobenius x * (frobenius y - frobenius y'))).
rewrite /c; have := mulr_ge0 w0 d0; lra.
Qed.

Let Xp_w w w' x y : K x -> B y ->
  `|Xp w x y - Xp w' x y| <= c * frobenius (w - w').
Proof.
move=> Kx By; have hx := Kb Kx; have hy := Bb By.
have x0 := frobenius_ge0 x; have y0 := frobenius_ge0 y.
have d0 := frobenius_ge0 (w - w'); have hA := nA (w - w').
have hg := ng (w - w'); have g0 := normr_ge0 (rsubmx (w - w') 0 0).
have A0 := frobenius_ge0 (vec_mx (lsubmx (w - w')) : 'M[R]_(N, M)).
have -> : Xp w x y - Xp w' x y =
    mxdot y ((vec_mx (lsubmx (w - w')) : 'M[R]_(N, M)) *m x) +
    rsubmx (w - w') 0 0 * (frobenius x * frobenius y).
  rewrite /Xp !linearB /= mulmxBl mxdotBr !mxE; ring.
have e1 : `|mxdot y ((vec_mx (lsubmx (w - w')) : 'M[R]_(N, M)) *m x)| <=
    1 * (frobenius (w - w') * rho).
  by apply: le_trans (mxdot_mulmx_le _ _ _) _; apply: le3.
have e2 : `|rsubmx (w - w') 0 0 * (frobenius x * frobenius y)| <=
    frobenius (w - w') * (rho * 1).
  by rewrite normrM (ger0_norm (mulr_ge0 x0 y0)); apply: le3.
have := ler_normD
  (mxdot y ((vec_mx (lsubmx (w - w')) : 'M[R]_(N, M)) *m x))
  (rsubmx (w - w') 0 0 * (frobenius x * frobenius y)).
rewrite /c; have := mulr_ge0 d0 rho0; lra.
Qed.

Let Yp_b z x y : K x -> B y -> `|Yp z x y| <= c * frobenius z.
Proof.
move=> Kx By; have hx := Kb Kx; have hy := Bb By.
have x0 := frobenius_ge0 x; have y0 := frobenius_ge0 y.
have z0 := frobenius_ge0 z.
have hg : `|mxdot (lsubmx z)^T y| <= frobenius z * 1.
  exact: le_trans (dotg z y) (ler_wpM2l z0 hy).
have hh : `|mxdot (rsubmx z)^T x| <= frobenius z * rho.
  exact: le_trans (doth z x) (ler_wpM2l z0 hx).
have e1 : `|frobenius x * mxdot (lsubmx z)^T y| <= rho * (frobenius z * 1).
  by rewrite normrM (ger0_norm x0); apply: ler_pM => //; exact: normr_ge0.
have e2 : `|frobenius y * mxdot (rsubmx z)^T x| <= 1 * (frobenius z * rho).
  by rewrite normrM (ger0_norm y0); apply: ler_pM => //; exact: normr_ge0.
have := ler_normD (frobenius x * mxdot (lsubmx z)^T y)
  (frobenius y * mxdot (rsubmx z)^T x).
rewrite /Yp /c; have := mulr_ge0 z0 rho0; lra.
Qed.

Let Yp_x z x x' y : K x -> K x' -> B y ->
  `|Yp z x y - Yp z x' y| <= c * frobenius z * frobenius (x - x').
Proof.
move=> Kx Kx' By; have hy := Bb By.
have y0 := frobenius_ge0 y; have z0 := frobenius_ge0 z.
have d0 := frobenius_ge0 (x - x'); have hd := ler_frobeniusB x x'.
have -> : Yp z x y - Yp z x' y =
    (frobenius x - frobenius x') * mxdot (lsubmx z)^T y +
    frobenius y * mxdot (rsubmx z)^T (x - x').
  by rewrite /Yp mxdotBr; ring.
have hg : `|mxdot (lsubmx z)^T y| <= frobenius z * 1.
  exact: le_trans (dotg z y) (ler_wpM2l z0 hy).
have hh := doth z (x - x').
have e1 : `|(frobenius x - frobenius x') * mxdot (lsubmx z)^T y| <=
    frobenius (x - x') * (frobenius z * 1).
  by rewrite normrM; apply: ler_pM => //; exact: normr_ge0.
have e2 : `|frobenius y * mxdot (rsubmx z)^T (x - x')| <=
    1 * (frobenius z * frobenius (x - x')).
  by rewrite normrM (ger0_norm y0); apply: ler_pM => //; exact: normr_ge0.
have := ler_normD ((frobenius x - frobenius x') * mxdot (lsubmx z)^T y)
  (frobenius y * mxdot (rsubmx z)^T (x - x')).
rewrite /c; have := mulr_ge0 (mulr_ge0 rho0 z0) d0; lra.
Qed.

Let Yp_y z x y y' : K x -> B y -> B y' ->
  `|Yp z x y - Yp z x y'| <= c * frobenius z * frobenius (y - y').
Proof.
move=> Kx By By'; have hx := Kb Kx.
have x0 := frobenius_ge0 x; have z0 := frobenius_ge0 z.
have d0 := frobenius_ge0 (y - y'); have hd := ler_frobeniusB y y'.
have -> : Yp z x y - Yp z x y' =
    frobenius x * mxdot (lsubmx z)^T (y - y') +
    (frobenius y - frobenius y') * mxdot (rsubmx z)^T x.
  by rewrite /Yp mxdotBr; ring.
have hg := dotg z (y - y').
have hh : `|mxdot (rsubmx z)^T x| <= frobenius z * rho.
  exact: le_trans (doth z x) (ler_wpM2l z0 hx).
have e1 : `|frobenius x * mxdot (lsubmx z)^T (y - y')| <=
    rho * (frobenius z * frobenius (y - y')).
  by rewrite normrM (ger0_norm x0); apply: ler_pM => //; exact: normr_ge0.
have e2 : `|(frobenius y - frobenius y') * mxdot (rsubmx z)^T x| <=
    frobenius (y - y') * (frobenius z * rho).
  by rewrite normrM; apply: ler_pM => //; exact: normr_ge0.
have := ler_normD (frobenius x * mxdot (lsubmx z)^T (y - y'))
  ((frobenius y - frobenius y') * mxdot (rsubmx z)^T x).
rewrite /c; have := mulr_ge0 z0 d0; lra.
Qed.

Let Yp_z z z' x y : K x -> B y ->
  `|Yp z x y - Yp z' x y| <= c * frobenius (z - z').
Proof.
move=> Kx By; have hx := Kb Kx; have hy := Bb By.
have x0 := frobenius_ge0 x; have y0 := frobenius_ge0 y.
have d0 := frobenius_ge0 (z - z').
have -> : Yp z x y - Yp z' x y =
    frobenius x * mxdot (lsubmx (z - z'))^T y +
    frobenius y * mxdot (rsubmx (z - z'))^T x.
  by rewrite /Yp !linearB /= ?linearB /= !mxdotBl; ring.
have hg : `|mxdot (lsubmx (z - z'))^T y| <= frobenius (z - z') * 1.
  exact: le_trans (dotg (z - z') y) (ler_wpM2l d0 hy).
have hh : `|mxdot (rsubmx (z - z'))^T x| <= frobenius (z - z') * rho.
  exact: le_trans (doth (z - z') x) (ler_wpM2l d0 hx).
have e1 : `|frobenius x * mxdot (lsubmx (z - z'))^T y| <=
    rho * (frobenius (z - z') * 1).
  by rewrite normrM (ger0_norm x0); apply: ler_pM => //; exact: normr_ge0.
have e2 : `|frobenius y * mxdot (rsubmx (z - z'))^T x| <=
    1 * (frobenius (z - z') * rho).
  by rewrite normrM (ger0_norm y0); apply: ler_pM => //; exact: normr_ge0.
have := ler_normD (frobenius x * mxdot (lsubmx (z - z'))^T y)
  (frobenius y * mxdot (rsubmx (z - z'))^T x).
rewrite /c; have := mulr_ge0 d0 rho0; lra.
Qed.

(* The finite comparisons, from gordon_gamma. *)
Let XY_low k l (rs : 'I_k.+1 -> 'cV[R]_M) (cs : 'I_l.+1 -> 'cV[R]_N) :
  (forall u, K (rs u)) -> (forall t, B (cs t)) ->
  (\int[gauss (N + M)]_z (minmax (\matrix_(u, t) Yp z (rs u) (cs t)))%:E <=
   \int[gauss (N * M + 1)]_w (minmax (\matrix_(u, t) Xp w (rs u) (cs t)))%:E)%E.
Proof.
move=> _ _.
have Bcov u t v s : ((bil_mx rs cs)^T *m bil_mx rs cs)
    (mxvec_index u t) (mxvec_index v s) =
    mxdot (rs u) (rs v) * mxdot (cs t) (cs s).
  by rewrite bil_cov mulrC.
have eY z : \matrix_(u, t) Yp z (rs u) (cs t) = vec_mx (z *m auxg_mx rs cs).
  by apply/matrixP => u t; rewrite mxE auxg_mxE.
have eX w : \matrix_(u, t) Xp w (rs u) (cs t) =
    vec_mx (w *m bilg_mx rs cs (bil_mx rs cs)).
  by apply/matrixP => u t; rewrite mxE bilg_mxE bil_mxE.
have g := gordon_gamma Bcov (auxg_cov rs cs).
under eq_integral do rewrite eY.
by under [X in (_ <= X)%E]eq_integral do rewrite eX.
Qed.

Let XY_up k l (rs : 'I_k.+1 -> 'cV[R]_N) (cs : 'I_l.+1 -> 'cV[R]_M) :
  (forall u, B (rs u)) -> (forall t, K (cs t)) ->
  (\int[gauss (N + M)]_z (minmax (\matrix_(u, t) Yp z (cs t) (rs u)))%:E <=
   \int[gauss (N * M + 1)]_w (minmax (\matrix_(u, t) Xp w (cs t) (rs u)))%:E)%E.
Proof.
move=> _ _.
have eY z : \matrix_(u, t) Yp z (cs t) (rs u) = vec_mx (z *m auxgT_mx rs cs).
  by apply/matrixP => u t; rewrite mxE auxgT_mxE.
have eX w : \matrix_(u, t) Xp w (cs t) (rs u) =
    vec_mx (w *m bilg_mx rs cs (bilT_mx rs cs)).
  apply/matrixP => u t; rewrite mxE bilg_mxE bilT_mxE /Xp.
  by rewrite (mulrC (frobenius (cs t))).
have g := gordon_gamma (bilT_cov rs cs) (auxgT_cov rs cs).
under eq_integral do rewrite eY.
by under [X in (_ <= X)%E]eq_integral do rewrite eX.
Qed.

(* The pointwise bounds of the lower bound. *)
Let low_aux z : (0 < N)%N ->
  cgmt_aux K (lsubmx (- z)) (rsubmx (- z)) <= infsup K B (Yp z).
Proof.
move=> N0; apply: (le_infsup K0) => x Kx.
apply: le_trans (cgmt_aux_le _ _ Kx) _.
rewrite !linearN /= frobeniusN mxdotNl opprK.
have [ys [ys1 ysg]] := unit_dir (lsubmx z) N0.
have Bys : B ys by rewrite /unit_ball /= ys1.
rewrite ge_max; apply/andP; split.
  have := sup_row_ub (Yp_b z) Kx (unit_ball0 R N).
  by rewrite /Yp mxdot0r frobenius0 mulr0 mul0r addr0.
have := sup_row_ub (Yp_b z) Kx Bys.
by rewrite /Yp ysg ys1 mul1r (mulrC (frobenius x)).
Qed.

Let low_X w : infsup K B (Xp w) <=
  escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) +
  rho * frobenius (rsubmx w).
Proof.
rewrite -lerBlDr; apply: (escape_inf_ge K0) => x Kx; rewrite lerBlDr.
apply: le_trans (infsup_le B0 (Xp_b w) Kx) _.
apply: (sup_row_le B0 Kx) => y By.
have hy := Bb By; have hx := Kb Kx.
have x0 := frobenius_ge0 x; have y0 := frobenius_ge0 y.
set A : 'M[R]_(N, M) := vec_mx (lsubmx w).
have h1 : mxdot y (A *m x) <= frobenius (A *m x).
  apply: le_trans (ler_mxdot _ _) _.
  by rewrite -[X in _ <= X]mul1r ler_wpM2r // frobenius_ge0.
have h2 : rsubmx w 0 0 * (frobenius x * frobenius y) <=
    frobenius (rsubmx w) * (rho * 1).
  apply: le_trans (ler_norm _) _.
  rewrite normrM (ger0_norm (mulr_ge0 x0 y0)).
  apply: ler_pM; rewrite ?normr_ge0 ?mulr_ge0 //; first exact: frobenius_entry.
  exact: ler_pM.
by rewrite /Xp -/A; lra.
Qed.

(* The lower bound of the convex Gaussian min-max theorem. *)
Theorem cgmt_lower : (0 < N)%N ->
  \int[gauss (N + M)]_z cgmt_aux K (lsubmx z) (rsubmx z) - rho <=
  \int[gauss (N * M)]_a escape_inf K (vec_mx a : 'M[R]_(N, M)).
Proof.
move=> N0.
have hc := infsup_compare K0 B0 Kb Bb c0 Xp_b Yp_b Xp_x Xp_y Yp_x Yp_y
  Xp_w Yp_z XY_low.
have iX := integrable_infsupX K0 B0 c0 Xp_b Xp_w.
have iY := integrable_infsupY K0 B0 c0 Yp_b Yp_z.
have iphi := integrable_gauss_lipschitz (@cgmt_aux_lipschitz R N M K K0 rho Kb).
have iphiN : (gauss (N + M)).-integrable setT
    (EFin \o (fun z => cgmt_aux K (lsubmx (- z)) (rsubmx (- z)))).
  apply: (@integrable_gauss_lipschitz _ _ _ (Num.sqrt 2 * rho)) => z z'.
  have := cgmt_aux_lipschitz K0 Kb (- z) (- z').
  have -> : - z - - z' = - (z - z') by rewrite opprD.
  by rewrite frobeniusN.
have iPhi : (gauss (N * M)).-integrable setT
    (EFin \o (fun a : 'rV[R]_(N * M) =>
      escape_inf K (vec_mx a : 'M[R]_(N, M)))).
  apply: (@integrable_gauss_lipschitz _ _ _ rho) => a a'.
  by rewrite (le_trans (escape_inf_lip K0 Kb _ _)) // -linearB /=
    frobenius_vec_mx.
have iPhiW : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) =>
      escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)))).
  apply: (@integrable_gauss_lipschitz _ _ _ rho) => w w'.
  rewrite (le_trans (escape_inf_lip K0 Kb _ _)) // -!linearB /=.
  rewrite frobenius_vec_mx.
  by apply: ler_wpM2l; [exact: rho0|exact: frobenius_lsubmx_le].
have iF1 := @integrable_gauss_frobenius R 1.
have iFr : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) => frobenius (rsubmx w))).
  apply: (@integrable_gauss_lipschitz _ _ _ 1) => w w'.
  rewrite mul1r (le_trans (ler_frobeniusB _ _)) // -linearB /=.
  exact: frobenius_rsubmx_le.
have iFrZ : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) => rho * frobenius (rsubmx w))).
  have := integrableZl measurableT rho iFr.
  by apply: eq_integrable => // w _.
have e1 : \int[gauss (N + M)]_z cgmt_aux K (lsubmx (- z)) (rsubmx (- z)) =
    \int[gauss (N + M)]_z cgmt_aux K (lsubmx z) (rsubmx z).
  by rewrite /Rintegral; congr fine; exact: (integral_gauss_opp iphi).
have h2 : \int[gauss (N + M)]_z cgmt_aux K (lsubmx (- z)) (rsubmx (- z)) <=
    \int[gauss (N + M)]_z infsup K B (Yp z).
  by apply: le_Rintegral => // z _; exact: low_aux.
have iS : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) =>
      escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) +
      rho * frobenius (rsubmx w))).
  have := integrableD measurableT iPhiW iFrZ.
  by apply: eq_integrable => // w _; rewrite /= EFinD.
have h4 : \int[gauss (N * M + 1)]_w infsup K B (Xp w) <=
    \int[gauss (N * M + 1)]_w
      (escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) +
       rho * frobenius (rsubmx w)).
  by apply: le_Rintegral => // w _; exact: low_X.
have e5 : \int[gauss (N * M + 1)]_w
      (escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) +
       rho * frobenius (rsubmx w)) =
    \int[gauss (N * M)]_a escape_inf K (vec_mx a : 'M[R]_(N, M)) +
    rho * \int[gauss 1]_g frobenius (g : 'rV[R]_1).
  rewrite RintegralD // RintegralZl //; congr (_ + _ * _).
    by rewrite /Rintegral; congr fine; exact: (integral_gauss_lsubmx 1 iPhi).
  by rewrite /Rintegral; congr fine; exact: (integral_gauss_rsubmx (N * M) iF1).
have e6 : \int[gauss 1]_g frobenius (g : 'rV[R]_1) <= 1.
  by have := @gauss_frobenius_mean_le R 1; rewrite sqrtr1.
have := ler_wpM2l rho0 e6.
lra.
Qed.

Section upper.
Hypothesis Kc : closed K.
Hypothesis Kcvx : forall x y (t : R), K x -> K y -> 0 <= t <= 1 ->
  K (x + t *: (y - x)).

(* The pointwise bounds of the upper bound. *)
Let up_X w : escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) +
  infsup B K (fun y x => Xp w x y) <= rho * frobenius (rsubmx w).
Proof.
set A : 'M[R]_(N, M) := vec_mx (lsubmx w).
have hm := escape_inf_minimax K0 Kb Kc Kcvx A.
have FB1 y x : B y -> K x -> `|Xp w x y| <= c * frobenius w.
  by move=> By Kx; exact: Xp_b.
have FB2 y x : B y -> K x -> `|mxdot y (A *m x)| <= c * frobenius w.
  move=> By Kx; have hy := Bb By; have hx := Kb Kx.
  have w0 := frobenius_ge0 w; have hA := nA w.
  apply: le_trans (mxdot_mulmx_le _ _ _) _.
  have h : frobenius y * (frobenius A * frobenius x) <=
      1 * (frobenius w * rho).
    by apply: le3; rewrite ?frobenius_ge0.
  rewrite /c; have := mulr_ge0 w0 rho0; lra.
have FD y x : B y -> K x ->
    `|Xp w x y - mxdot y (A *m x)| <= rho * frobenius (rsubmx w).
  move=> By Kx; have hy := Bb By; have hx := Kb Kx.
  have -> : Xp w x y - mxdot y (A *m x) =
      rsubmx w 0 0 * (frobenius x * frobenius y).
    by rewrite /Xp -/A addrAC subrr add0r.
  rewrite normrM (ger0_norm (mulr_ge0 (frobenius_ge0 _) (frobenius_ge0 _))).
  apply: le_trans (_ : _ <= frobenius (rsubmx w) * (rho * 1)) _.
    by apply: le3; rewrite ?normr_ge0 ?frobenius_ge0 //; exact: frobenius_entry.
  by rewrite mulr1 mulrC.
have := infsup_lipschitz B0 K0 FB1 FB2 FD.
rewrite ler_norml => /andP[_ hl].
lra.
Qed.

Let up_Y z :
  0 <= cgmt_aux K (lsubmx z) (rsubmx z) + infsup B K (fun y x => Yp z x y).
Proof.
suff h : - cgmt_aux K (lsubmx z) (rsubmx z) <=
    infsup B K (fun y x => Yp z x y) by lra.
apply: (le_infsup B0) => y By.
rewrite lerNl; apply: (cgmt_aux_ge K0) => x Kx.
have FB y' x' : B y' -> K x' -> `|Yp z x' y'| <= c * frobenius z.
  by move=> By' Kx'; exact: Yp_b.
have hs := sup_row_ub FB By Kx.
have hy := Bb By; have y0 := frobenius_ge0 y; have x0 := frobenius_ge0 x.
have hg : - mxdot (lsubmx z)^T y <= frobenius (lsubmx z) * frobenius y.
  apply: le_trans (_ : _ <= `|mxdot (lsubmx z)^T y|) _.
    by rewrite -normrN ler_norm.
  by apply: le_trans (mxdot_le _ _) _; rewrite frobenius_trmx.
set v := frobenius (lsubmx z) * frobenius x - mxdot (rsubmx z)^T x.
have key : - Yp z x y <= frobenius y * v.
  by rewrite /Yp /v; have := ler_wpM2l x0 hg; lra.
have hv : frobenius y * v <= Num.max 0 v.
  have [v0|v0] := leP 0 v; first exact: ler_piMl.
  by apply: mulr_ge0_le0 => //; exact: ltW.
lra.
Qed.

(* The upper bound of the convex Gaussian min-max theorem, for K convex. *)
Theorem cgmt_upper :
  \int[gauss (N * M)]_a escape_inf K (vec_mx a : 'M[R]_(N, M)) <=
  \int[gauss (N + M)]_z cgmt_aux K (lsubmx z) (rsubmx z) + rho.
Proof.
pose X w y x := Xp w x y.
pose Y z y x := Yp z x y.
have Xb w y x : B y -> K x -> `|X w y x| <= c * frobenius w.
  by move=> By Kx; exact: Xp_b.
have Yb z y x : B y -> K x -> `|Y z y x| <= c * frobenius z.
  by move=> By Kx; exact: Yp_b.
have Xs w y y' x : B y -> B y' -> K x ->
    `|X w y x - X w y' x| <= c * frobenius w * frobenius (y - y').
  by move=> By By' Kx; exact: Xp_y.
have Xt w y x x' : B y -> K x -> K x' ->
    `|X w y x - X w y x'| <= c * frobenius w * frobenius (x - x').
  by move=> By Kx Kx'; exact: Xp_x.
have Ys z y y' x : B y -> B y' -> K x ->
    `|Y z y x - Y z y' x| <= c * frobenius z * frobenius (y - y').
  by move=> By By' Kx; exact: Yp_y.
have Yt z y x x' : B y -> K x -> K x' ->
    `|Y z y x - Y z y x'| <= c * frobenius z * frobenius (x - x').
  by move=> By Kx Kx'; exact: Yp_x.
have Xw w w' y x : B y -> K x ->
    `|X w y x - X w' y x| <= c * frobenius (w - w').
  by move=> By Kx; exact: Xp_w.
have Yz z z' y x : B y -> K x ->
    `|Y z y x - Y z' y x| <= c * frobenius (z - z').
  by move=> By Kx; exact: Yp_z.
have hc := infsup_compare B0 K0 Bb Kb c0 Xb Yb Xs Xt Ys Yt Xw Yz XY_up.
have iX := integrable_infsupX B0 K0 c0 Xb Xw.
have iY := integrable_infsupY B0 K0 c0 Yb Yz.
have iphi := integrable_gauss_lipschitz (@cgmt_aux_lipschitz R N M K K0 rho Kb).
have iPhi : (gauss (N * M)).-integrable setT
    (EFin \o (fun a : 'rV[R]_(N * M) =>
      escape_inf K (vec_mx a : 'M[R]_(N, M)))).
  apply: (@integrable_gauss_lipschitz _ _ _ rho) => a a'.
  by rewrite (le_trans (escape_inf_lip K0 Kb _ _)) // -linearB /=
    frobenius_vec_mx.
have iPhiW : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) =>
      escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)))).
  apply: (@integrable_gauss_lipschitz _ _ _ rho) => w w'.
  rewrite (le_trans (escape_inf_lip K0 Kb _ _)) // -!linearB /=.
  rewrite frobenius_vec_mx.
  by apply: ler_wpM2l; [exact: rho0|exact: frobenius_lsubmx_le].
have iF1 := @integrable_gauss_frobenius R 1.
have iFr : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) => frobenius (rsubmx w))).
  apply: (@integrable_gauss_lipschitz _ _ _ 1) => w w'.
  rewrite mul1r (le_trans (ler_frobeniusB _ _)) // -linearB /=.
  exact: frobenius_rsubmx_le.
have iFrZ : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) => rho * frobenius (rsubmx w))).
  have := integrableZl measurableT rho iFr.
  by apply: eq_integrable => // w _.
have iU1 : (gauss (N * M + 1)).-integrable setT
    (EFin \o (fun w : 'rV[R]_(N * M + 1) =>
      escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) + infsup B K (X w))).
  have := integrableD measurableT iPhiW iX.
  by apply: eq_integrable => // w _; rewrite /= EFinD.
have h1 : \int[gauss (N * M + 1)]_w
      (escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) + infsup B K (X w)) <=
    \int[gauss (N * M + 1)]_w (rho * frobenius (rsubmx w)).
  by apply: le_Rintegral => // w _; exact: up_X.
rewrite RintegralD // RintegralZl // in h1.
have iU2 : (gauss (N + M)).-integrable setT
    (EFin \o (fun z : 'rV[R]_(N + M) =>
      cgmt_aux K (lsubmx z) (rsubmx z) + infsup B K (Y z))).
  have := integrableD measurableT iphi iY.
  by apply: eq_integrable => // z _; rewrite /= EFinD.
have h2 : 0 <= \int[gauss (N + M)]_z
    (cgmt_aux K (lsubmx z) (rsubmx z) + infsup B K (Y z)).
  by apply: Rintegral_ge0 => // z _; exact: up_Y.
rewrite RintegralD // in h2.
have e3 : \int[gauss (N * M + 1)]_w
      escape_inf K (vec_mx (lsubmx w) : 'M[R]_(N, M)) =
    \int[gauss (N * M)]_a escape_inf K (vec_mx a : 'M[R]_(N, M)).
  by rewrite /Rintegral; congr fine; exact: (integral_gauss_lsubmx 1 iPhi).
have e4 : \int[gauss (N * M + 1)]_w frobenius (rsubmx w) =
    \int[gauss 1]_g frobenius (g : 'rV[R]_1).
  by rewrite /Rintegral; congr fine; exact: (integral_gauss_rsubmx (N * M) iF1).
have e6 : \int[gauss 1]_g frobenius (g : 'rV[R]_1) <= 1.
  by have := @gauss_frobenius_mean_le R 1; rewrite sqrtr1.
have := ler_wpM2l rho0 e6.
rewrite e3 e4 in h1; lra.
Qed.

End upper.

(* Concentration: Phi(K) is rho-Lipschitz in a, and phi(K) is
   (sqrt 2 rho)-Lipschitz in z. *)
Theorem cgmt_escape_tail (u : R) : 0 <= u ->
  (gauss (N * M) [set a | u <= `|escape_inf K (vec_mx a : 'M[R]_(N, M)) -
     \int[gauss (N * M)]_b escape_inf K (vec_mx b : 'M[R]_(N, M))|]%R <=
   (2 * expR (- u ^+ 2 / (2 * rho ^+ 2)))%:E)%E.
Proof.
move=> u0.
have FL (a a' : 'rV[R]_(N * M)) :
    `|escape_inf K (vec_mx a : 'M[R]_(N, M)) -
      escape_inf K (vec_mx a' : 'M[R]_(N, M))| <= rho * frobenius (a - a').
  by rewrite (le_trans (escape_inf_lip K0 Kb _ _)) // -linearB /=
    frobenius_vec_mx.
by have := gauss_concentration_abs_tail FL u0.
Qed.

Theorem cgmt_aux_tail (u : R) : 0 <= u ->
  (gauss (N + M) [set z | u <= `|cgmt_aux K (lsubmx z) (rsubmx z) -
     \int[gauss (N + M)]_y cgmt_aux K (lsubmx y) (rsubmx y)|]%R <=
   (2 * expR (- u ^+ 2 / (4 * rho ^+ 2)))%:E)%E.
Proof.
move=> u0.
have := gauss_concentration_abs_tail
  (@cgmt_aux_lipschitz R N M K K0 rho Kb) u0.
by rewrite exprMn sqr_sqrtr // mulrA -natrM.
Qed.

(* Phi(K) concentrates around the mean of phi(K): for K closed and convex and
   N > 0, Phi(K) is farther than rho + u from E phi(K) with probability at
   most 2 exp (- u^2 / (2 rho^2)). *)
Corollary cgmt_tail (u : R) : (0 < N)%N -> closed K ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 -> K (x + t *: (y - x))) ->
  0 <= u ->
  (gauss (N * M) [set a | rho + u <= `|escape_inf K (vec_mx a : 'M[R]_(N, M)) -
     \int[gauss (N + M)]_z cgmt_aux K (lsubmx z) (rsubmx z)|]%R <=
   (2 * expR (- u ^+ 2 / (2 * rho ^+ 2)))%:E)%E.
Proof.
move=> N0 Kc Kcvx u0.
have hl := cgmt_lower N0; have hu := cgmt_upper Kc Kcvx.
set E1 := \int[gauss (N * M)]_b escape_inf K (vec_mx b : 'M[R]_(N, M))
  in hl hu *.
set E2 := \int[gauss (N + M)]_z cgmt_aux K (lsubmx z) (rsubmx z) in hl hu *.
have FL (a a' : 'rV[R]_(N * M)) :
    `|escape_inf K (vec_mx a : 'M[R]_(N, M)) -
      escape_inf K (vec_mx a' : 'M[R]_(N, M))| <= rho * frobenius (a - a').
  by rewrite (le_trans (escape_inf_lip K0 Kb _ _)) // -linearB /=
    frobenius_vec_mx.
have mPhi := continuous_measurable_mx (lipschitz_frobenius_continuous FL).
have mF (e : R) : measurable_fun setT
    (fun a : 'rV[R]_(N * M) => `|escape_inf K (vec_mx a : 'M[R]_(N, M)) - e|).
  by apply: measurableT_comp => //; apply: measurable_funB.
have mS (e r : R) : measurable [set a : 'rV[R]_(N * M) |
    r <= `|escape_inf K (vec_mx a : 'M[R]_(N, M)) - e|].
  have -> : [set a : 'rV[R]_(N * M) |
      r <= `|escape_inf K (vec_mx a : 'M[R]_(N, M)) - e|] =
      (fun a => `|escape_inf K (vec_mx a : 'M[R]_(N, M)) - e|) @^-1`
      `[r, +oo[%classic.
    by apply/seteqP; split => a /=; rewrite in_itv /= andbT.
  by rewrite -[X in measurable X]setTI; apply: mF => //; exact: measurable_itv.
apply: le_trans (cgmt_escape_tail u0).
apply: le_measure; rewrite ?inE; [exact: mS|exact: mS|].
move=> a /= h; rewrite -/E1.
have hE : `|E1 - E2| <= rho by rewrite ler_norml; apply/andP; split; lra.
have := ler_distD E1 (escape_inf K (vec_mx a : 'M[R]_(N, M))) E2.
lra.
Qed.

End cgmt_mean.
