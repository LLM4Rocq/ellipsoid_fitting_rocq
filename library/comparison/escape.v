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
From GaussianAnalysis.gaussian Require Import gauss_interpolation gauss_moments.
From GaussianAnalysis.probability Require Import moments.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets.
From GaussianAnalysis.comparison Require Import gauss_rotation gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_concentration slepian gordon.

(**md**************************************************************************)
(* # Escape through a mesh and norms of Gaussian matrices                     *)
(*                                                                            *)
(* Let a have law gauss (N * M), so that G = vec_mx a is an N x M matrix of   *)
(* independent standard normal entries, and let g and h have laws gauss N and *)
(* gauss M. Vectors x of R^M are column vectors 'cV[R]_M, and |x| is          *)
(* frobenius x.                                                               *)
(*                                                                            *)
(* For a nonempty set T of unit vectors of 'cV[R]_M and N > 0, gordon_escape  *)
(* is Gordon's escape theorem: E[inf_(x in T) |G x|] >= E[|g|] - w(T), where  *)
(* w(T) = E[sup_(x in T) <h, x>] is the Gaussian width of T. By Gaussian      *)
(* concentration, inf_(x in T) |G x| is at most E[|g|] - w(T) - u with        *)
(* probability at most expR (- u^2 / 2) (gordon_escape_tail). So when         *)
(* w(T) < E[|g|], the kernel of G misses T with high probability: escape      *)
(* through a mesh. For T the unit sphere, w(T) = E[|h|] (gwidth_sphere),      *)
(* which bounds the smallest singular value of G (gauss_min_singular_mean).   *)
(*                                                                            *)
(* For N, M > 0, E[opnorm G] <= E[|g|] + E[|h|] <= sqrt N + sqrt M            *)
(* (gauss_opnorm_mean, gauss_frobenius_mean_le, gauss_opnorm_mean_sqrt), and  *)
(* opnorm G exceeds E[|g|] + E[|h|] + u with probability at most              *)
(* expR (- u^2 / 2) (gauss_opnorm_tail).                                      *)
(*                                                                            *)
(* The proofs compare, for finite families xs of unit vectors of 'cV[R]_M and *)
(* ys of unit vectors of 'cV[R]_N, the matrix process ys t^T *m G *m xs u     *)
(* with the process <g, ys t> + <h, xs u>: by Gordon's inequality for the     *)
(* min-max over u and t (aux_bil_minmax), and by the Sudakov-Fernique         *)
(* inequality for the maximum (bil_aux_max). Nets of T and of the unit        *)
(* spheres (net_exists, unit_sphere_net) pass from finite families to T and   *)
(* to the spheres. The file also proves that gauss n is invariant under       *)
(* x |-> - x (integral_gauss_opp).                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*             unvec k == the pair (i, j) such that mxvec_index i j = k       *)
(*           fam_mx xs == the matrix whose columns are the vectors xs u       *)
(*        bil_mx xs ys == the matrix B such that vec_mx (a *m B) u t is       *)
(*                        ys t ^T *m vec_mx a *m xs u                         *)
(*        aux_mx xs ys == the matrix C such that vec_mx (z *m C) u t is       *)
(*                        <lsubmx z, ys t> + <rsubmx z, xs u>                 *)
(*      gwidth_fun T h == sup_(x in T) <h, x>, for h : 'rV[R]_M               *)
(*      escape_inf T G == inf_(x in T) |G *m x|                               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section unvec.
Context {m n : nat}.

(* The inverse of mxvec_index. *)
Definition unvec (k : 'I_(m * n)) : 'I_m * 'I_n :=
  enum_val (cast_ord (esym (mxvec_cast m n)) k).

Lemma unvecK i j : unvec (mxvec_index i j) = (i, j).
Proof. by rewrite /unvec /mxvec_index cast_ordK enum_rankK. Qed.

End unvec.

Section rmax_minmax_sums.
Context {R : realType}.

Lemma rmax_addr q (z : 'rV[R]_q.+1) c : rmax (\row_j (z 0 j + c)) = rmax z + c.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: rmax_leD => j; rewrite mxE.
rewrite -lerBrDr; apply: rmax_leD => j; rewrite mxE; lra.
Qed.

(* min_u max_t (c u + a t) = max_t a t + min_u c u. *)
Lemma minmax_add p q (a : 'rV[R]_q.+1) (c : 'rV[R]_p.+1) :
  minmax (\matrix_(u, t) (c 0 u + a 0 t)) = rmax a - rmax (- c).
Proof.
rewrite /minmax.
have -> : \row_u (- rmax (row u (\matrix_(u, t) (c 0 u + a 0 t)))) =
    \row_u ((- c) 0 u + - rmax a).
  apply/rowP => u; rewrite !mxE.
  have -> : row u (\matrix_(u, t) (c 0 u + a 0 t)) = \row_t (a 0 t + c 0 u).
    by apply/rowP => t; rewrite !mxE addrC.
  by rewrite rmax_addr opprD addrC.
by rewrite (rmax_addr (- c) (- rmax a)); lra.
Qed.

(* The largest coordinate of the vector of the c u + a t over all pairs. *)
Lemma rmax_vec_add p q (w : 'rV[R]_(p.+1 * q.+1)) (a : 'rV[R]_q.+1)
    (c : 'rV[R]_p.+1) :
  (forall u t, w 0 (mxvec_index u t) = c 0 u + a 0 t) ->
  rmax w = rmax c + rmax a.
Proof.
move=> wE; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: rmax_le => j; move: j; change (forall j : 'I_(p.+1 * q.+1),
    w 0 j <= rmax c + rmax a).
  by move=> j; case/mxvec_indexP: j => u t; rewrite wE lerD// le_rmax.
have [u ->] := rmax_eq c; have [t ->] := rmax_eq a; rewrite -wE.
exact: le_rmax.
Qed.

End rmax_minmax_sums.

Section gauss_opp.
Context {R : realType} {n : nat}.

Lemma ge0_integral_gauss_opp (f : 'rV[R]_n -> \bar R) :
  measurable_fun setT f -> (forall x, 0 <= f x)%E ->
  (\int[gauss n]_x f (- x)%R = \int[gauss n]_x f x)%E.
Proof.
move=> mf f0.
have mfo : measurable_fun setT (fun x : 'rV[R]_n => f (- x)).
  by apply: measurableT_comp mf _; apply: measurable_oppmx; exact: measurable_id.
have c1 : ((-1 : R) ^+ 2 + 0 ^+ 2 = 1)%R by rewrite expr0n addr0 sqrrN expr1n.
have c2 : ((1 : R) ^+ 2 + 0 ^+ 2 = 1)%R by rewrite expr0n addr0 expr1n.
rewrite -(ge0_integral_gauss_lincomb c2 mfo (fun x => f0 _)).
rewrite -(ge0_integral_gauss_lincomb c1 mf f0).
by apply: eq_integral => p _; rewrite !scale0r !addr0 scaleN1r scale1r.
Qed.

Lemma integrable_gauss_opp (f : 'rV[R]_n -> \bar R) :
  (gauss n).-integrable setT f -> (gauss n).-integrable setT (fun x => f (- x)%R).
Proof.
move=> fi; have mf := measurable_int _ fi.
have mfo : measurable_fun setT (fun x : 'rV[R]_n => f (- x)).
  by apply: measurableT_comp mf _; apply: measurable_oppmx; exact: measurable_id.
apply/integrableP; split => //.
rewrite (ge0_integral_gauss_opp (f := fun x => `|f x|)%E)//.
  exact: measurableT_comp.
by case/integrableP: fi.
Qed.

Lemma integral_gauss_opp (f : 'rV[R]_n -> \bar R) :
  (gauss n).-integrable setT f ->
  (\int[gauss n]_x f (- x)%R = \int[gauss n]_x f x)%E.
Proof.
move=> fi; have mf := measurable_int _ fi.
rewrite integralE [RHS]integralE; congr (_ - _)%E.
  rewrite -(ge0_integral_gauss_opp (measurable_funepos mf) (funepos_ge0 f)).
  by apply: eq_integral => x _; rewrite !funeposE.
rewrite -(ge0_integral_gauss_opp (measurable_funeneg mf) (funeneg_ge0 f)).
by apply: eq_integral => x _; rewrite !funenegE.
Qed.

End gauss_opp.

Section frobenius_vec_mx.
Context {R : realType}.

Lemma frobenius_vec_mx m n (z : 'rV[R]_(m * n)) :
  frobenius (vec_mx z) = frobenius z.
Proof.
rewrite /frobenius /mxdot big_ord1 sum_mxvec_index; congr Num.sqrt.
by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite mxE.
Qed.

End frobenius_vec_mx.

Section fam_mx.
Context {R : realType} {n k : nat}.

(* The matrix whose columns are the xs u. *)
Definition fam_mx (xs : 'I_k -> 'cV[R]_n) : 'M[R]_(n, k) := \matrix_(j, u) xs u j 0.

Lemma fam_mxE (xs : 'I_k -> 'cV[R]_n) (h : 'rV[R]_n) u :
  (h *m fam_mx xs) 0 u = mxdot h^T (xs u).
Proof. by rewrite !mxE /mxdot; apply: eq_bigr => i _; rewrite big_ord1 !mxE. Qed.

End fam_mx.

Section bilinear_process.
Context {R : realType} {N M k l : nat}.
Variables (xs : 'I_k.+1 -> 'cV[R]_M) (ys : 'I_l.+1 -> 'cV[R]_N).
Local Notation idx := (@mxvec_index k.+1 l.+1).

(* For a of law gauss (N * M), the Gaussian matrix with rows indexed by xs
   and columns by ys whose entry (u, t) is ys t ^T *m vec_mx a *m xs u. *)
Definition bil_mx : 'M[R]_(N * M, k.+1 * l.+1) :=
  \matrix_(r, c) (ys (unvec c).2 (unvec r).1 0 * xs (unvec c).1 (unvec r).2 0).

(* For z of law gauss (N + M), the Gaussian matrix whose entry (u, t) is
   <lsubmx z, ys t> + <rsubmx z, xs u>. *)
Definition aux_mx : 'M[R]_(N + M, k.+1 * l.+1) :=
  col_mx (\matrix_(i, c) ys (unvec c).2 i 0) (\matrix_(j, c) xs (unvec c).1 j 0).

Lemma bil_mxE (a : 'rV[R]_(N * M)) u t :
  vec_mx (a *m bil_mx) u t = mxdot (ys t) (vec_mx a *m xs u).
Proof.
rewrite mxE !mxE sum_mxvec_index /mxdot; apply: eq_bigr => i _.
rewrite big_ord1 !mxE mulr_sumr; apply: eq_bigr => j _.
by rewrite !mxE !unvecK /=; ring.
Qed.

Lemma aux_mxE (z : 'rV[R]_(N + M)) u t :
  vec_mx (z *m aux_mx) u t =
  mxdot (lsubmx z)^T (ys t) + mxdot (rsubmx z)^T (xs u).
Proof.
rewrite -[z]hsubmxK /aux_mx mul_row_col row_mxKl row_mxKr mxE !mxE /mxdot.
by congr (_ + _); apply: eq_bigr => i _; rewrite big_ord1 !mxE unvecK.
Qed.

Lemma bil_cov u t v s :
  (bil_mx^T *m bil_mx) (idx u t) (idx v s) =
  mxdot (ys t) (ys s) * mxdot (xs u) (xs v).
Proof.
rewrite mxE sum_mxvec_index /mxdot mulr_suml; apply: eq_bigr => i _.
rewrite !big_ord1 mulr_sumr; apply: eq_bigr => j _.
by rewrite !mxE !unvecK /= big_ord1; ring.
Qed.

Lemma aux_cov u t v s :
  (aux_mx^T *m aux_mx) (idx u t) (idx v s) =
  mxdot (ys t) (ys s) + mxdot (xs u) (xs v).
Proof.
rewrite /aux_mx tr_col_mx mul_row_col mxE !mxE /mxdot.
congr (_ + _); apply: eq_bigr => i _; rewrite big_ord1 !mxE !unvecK //.
Qed.

Lemma minmax_aux (z : 'rV[R]_(N + M)) :
  minmax (vec_mx (z *m aux_mx)) =
  rmax (lsubmx z *m fam_mx ys) - rmax ((- rsubmx z) *m fam_mx xs).
Proof.
have -> : vec_mx (z *m aux_mx) = \matrix_(u, t)
    ((rsubmx z *m fam_mx xs) 0 u + (lsubmx z *m fam_mx ys) 0 t).
  by apply/matrixP => u t; rewrite aux_mxE [RHS]mxE !fam_mxE addrC.
by rewrite minmax_add mulNmx.
Qed.

Lemma rmax_aux (z : 'rV[R]_(N + M)) :
  rmax (z *m aux_mx) =
  rmax (rsubmx z *m fam_mx xs) + rmax (lsubmx z *m fam_mx ys).
Proof.
apply: rmax_vec_add => u t.
have := aux_mxE z u t; rewrite mxE => ->.
by rewrite !fam_mxE addrC.
Qed.

Let lsub_fam (z : 'rV[R]_(N + M)) :
  lsubmx z *m fam_mx ys = z *m col_mx (fam_mx ys) 0.
Proof. by rewrite -[in RHS](hsubmxK z) mul_row_col mulmx0 addr0. Qed.

Let rsub_fam (z : 'rV[R]_(N + M)) :
  (- rsubmx z) *m fam_mx xs = z *m col_mx 0 (- fam_mx xs).
Proof.
by rewrite -[in RHS](hsubmxK z) mul_row_col mulmx0 add0r mulNmx mulmxN.
Qed.

Lemma integral_minmax_aux :
  \int[gauss (N + M)]_z minmax (vec_mx (z *m aux_mx)) =
  \int[gauss N]_g rmax (g *m fam_mx ys) - \int[gauss M]_h rmax (h *m fam_mx xs).
Proof.
have iY := integrable_gauss_rmax (fam_mx ys).
have iX := integrable_gauss_rmax (fam_mx xs).
have iY' : (gauss (N + M)).-integrable setT
    (EFin \o (fun z => rmax (lsubmx z *m fam_mx ys))).
  by under eq_fun do rewrite lsub_fam; exact: integrable_gauss_rmax.
have iX' : (gauss (N + M)).-integrable setT
    (EFin \o (fun z => rmax ((- rsubmx z) *m fam_mx xs))).
  by under eq_fun do rewrite rsub_fam; exact: integrable_gauss_rmax.
under eq_Rintegral do rewrite minmax_aux.
rewrite RintegralB//; congr (_ - _).
  by rewrite /Rintegral (integral_gauss_lsubmx M iY).
rewrite /Rintegral (integral_gauss_rsubmx N (integrable_gauss_opp iX)).
by rewrite (integral_gauss_opp iX).
Qed.

Let rsub_fam' (z : 'rV[R]_(N + M)) :
  rsubmx z *m fam_mx xs = z *m col_mx 0 (fam_mx xs).
Proof. by rewrite -[in RHS](hsubmxK z) mul_row_col mulmx0 add0r. Qed.

Lemma integral_rmax_aux :
  \int[gauss (N + M)]_z rmax (z *m aux_mx) =
  \int[gauss M]_h rmax (h *m fam_mx xs) + \int[gauss N]_g rmax (g *m fam_mx ys).
Proof.
have iY := integrable_gauss_rmax (fam_mx ys).
have iX := integrable_gauss_rmax (fam_mx xs).
have iY' : (gauss (N + M)).-integrable setT
    (EFin \o (fun z => rmax (lsubmx z *m fam_mx ys))).
  by under eq_fun do rewrite lsub_fam; exact: integrable_gauss_rmax.
have iX' : (gauss (N + M)).-integrable setT
    (EFin \o (fun z => rmax (rsubmx z *m fam_mx xs))).
  by under eq_fun do rewrite rsub_fam'; exact: integrable_gauss_rmax.
under eq_Rintegral do rewrite rmax_aux.
rewrite RintegralD//; congr (_ + _).
  by rewrite /Rintegral (integral_gauss_rsubmx N iX).
by rewrite /Rintegral (integral_gauss_lsubmx M iY).
Qed.

Hypothesis xs1 : forall u, frobenius (xs u) = 1.
Hypothesis ys1 : forall t, frobenius (ys t) = 1.

Let dot1 n (x y : 'cV[R]_n) : frobenius x = 1 -> frobenius y = 1 ->
  mxdot x y <= 1.
Proof. by move=> x1 y1; rewrite (le_trans (ler_mxdot x y))// x1 y1 mulr1. Qed.

Let sq1 n (x : 'cV[R]_n) : frobenius x = 1 -> mxdot x x = 1.
Proof. by move=> x1; rewrite -frobenius_sqr x1 expr1n. Qed.

Lemma incr_var_bil_aux u t v s :
  incr_var aux_mx (idx u t) (idx v s) - incr_var bil_mx (idx u t) (idx v s) =
  2 * (1 - mxdot (ys t) (ys s)) * (1 - mxdot (xs u) (xs v)).
Proof. by rewrite /incr_var !aux_cov !bil_cov !sq1//; ring. Qed.

(* The Sudakov-Fernique comparison of the two processes. *)
Lemma bil_aux_max :
  (\int[gauss (N * M)]_a (rmax (a *m bil_mx))%:E <=
   \int[gauss (N + M)]_z (rmax (z *m aux_mx))%:E)%E.
Proof.
apply: sudakov_fernique => j j'; move: j j'.
change (forall j j' : 'I_(k.+1 * l.+1),
  incr_var bil_mx j j' <= incr_var aux_mx j j').
move=> j j'; case/mxvec_indexP: j => u t; case/mxvec_indexP: j' => v s.
by rewrite -subr_ge0 incr_var_bil_aux !mulr_ge0// subr_ge0; exact: dot1.
Qed.

(* Gordon's comparison of the two processes. *)
Lemma aux_bil_minmax :
  (\int[gauss (N + M)]_z (minmax (vec_mx (z *m aux_mx)))%:E <=
   \int[gauss (N * M)]_a (minmax (vec_mx (a *m bil_mx)))%:E)%E.
Proof.
apply: gordon.
  by move=> u t s; rewrite -subr_le0 incr_var_bil_aux sq1// subrr mulr0.
move=> u v t s _; rewrite -subr_ge0 incr_var_bil_aux.
by rewrite !mulr_ge0// subr_ge0; exact: dot1.
Qed.

End bilinear_process.

Section bilinear_processT.
Context {R : realType} {N M k l : nat}.
Variables (zs : 'I_k.+1 -> 'cV[R]_N) (vs : 'I_l.+1 -> 'cV[R]_M).
Local Notation idx := (@mxvec_index k.+1 l.+1).

(* The process (u, t) |-> zs u ^T *m vec_mx a *m vs t, with the minimum over
   the left factor, and its auxiliary process. *)
Definition bilT_mx : 'M[R]_(N * M, k.+1 * l.+1) :=
  \matrix_(r, c) (zs (unvec c).1 (unvec r).1 0 * vs (unvec c).2 (unvec r).2 0).

Definition auxT_mx : 'M[R]_(N + M, k.+1 * l.+1) :=
  col_mx (\matrix_(i, c) zs (unvec c).1 i 0) (\matrix_(j, c) vs (unvec c).2 j 0).

Lemma bilT_mxE (a : 'rV[R]_(N * M)) u t :
  vec_mx (a *m bilT_mx) u t = mxdot (zs u) (vec_mx a *m vs t).
Proof.
rewrite mxE !mxE sum_mxvec_index /mxdot; apply: eq_bigr => i _.
rewrite big_ord1 !mxE mulr_sumr; apply: eq_bigr => j _.
by rewrite !mxE !unvecK /=; ring.
Qed.

Lemma auxT_mxE (z : 'rV[R]_(N + M)) u t :
  vec_mx (z *m auxT_mx) u t =
  mxdot (lsubmx z)^T (zs u) + mxdot (rsubmx z)^T (vs t).
Proof.
rewrite -[z]hsubmxK /auxT_mx mul_row_col row_mxKl row_mxKr mxE !mxE /mxdot.
by congr (_ + _); apply: eq_bigr => i _; rewrite big_ord1 !mxE unvecK.
Qed.

Lemma bilT_cov u t v s :
  (bilT_mx^T *m bilT_mx) (idx u t) (idx v s) =
  mxdot (zs u) (zs v) * mxdot (vs t) (vs s).
Proof.
rewrite mxE sum_mxvec_index /mxdot mulr_suml; apply: eq_bigr => i _.
rewrite !big_ord1 mulr_sumr; apply: eq_bigr => j _.
by rewrite !mxE !unvecK /= big_ord1; ring.
Qed.

Lemma auxT_cov u t v s :
  (auxT_mx^T *m auxT_mx) (idx u t) (idx v s) =
  mxdot (zs u) (zs v) + mxdot (vs t) (vs s).
Proof.
rewrite /auxT_mx tr_col_mx mul_row_col mxE !mxE /mxdot.
congr (_ + _); apply: eq_bigr => i _; rewrite big_ord1 !mxE !unvecK //.
Qed.

Hypothesis zs1 : forall u, frobenius (zs u) = 1.
Hypothesis vs1 : forall t, frobenius (vs t) = 1.

Let dot1 n (x y : 'cV[R]_n) : frobenius x = 1 -> frobenius y = 1 ->
  mxdot x y <= 1.
Proof. by move=> x1 y1; rewrite (le_trans (ler_mxdot x y))// x1 y1 mulr1. Qed.

Let sq1 n (x : 'cV[R]_n) : frobenius x = 1 -> mxdot x x = 1.
Proof. by move=> x1; rewrite -frobenius_sqr x1 expr1n. Qed.

Lemma incr_var_bilT_auxT u t v s :
  incr_var auxT_mx (idx u t) (idx v s) - incr_var bilT_mx (idx u t) (idx v s) =
  2 * (1 - mxdot (zs u) (zs v)) * (1 - mxdot (vs t) (vs s)).
Proof. by rewrite /incr_var !auxT_cov !bilT_cov !sq1//; ring. Qed.

(* Gordon's comparison of the two processes, with the minimum over u. *)
Lemma auxT_bilT_minmax :
  (\int[gauss (N + M)]_z (minmax (vec_mx (z *m auxT_mx)))%:E <=
   \int[gauss (N * M)]_a (minmax (vec_mx (a *m bilT_mx)))%:E)%E.
Proof.
apply: gordon.
  by move=> u t s; rewrite -subr_le0 incr_var_bilT_auxT sq1// subrr mulr0 mul0r.
move=> u v t s _; rewrite -subr_ge0 incr_var_bilT_auxT.
by rewrite !mulr_ge0// subr_ge0; exact: dot1.
Qed.

End bilinear_processT.

Section width_escape.
Context {R : realType} {M : nat}.
Variable T : set 'cV[R]_M.
Hypothesis T1 : forall x, T x -> frobenius x = 1.
Hypothesis T0 : T !=set0.

(* sup_(x in T) <h, x>, whose mean for h of law gauss M is the Gaussian
   width of T. *)
Definition gwidth_fun (h : 'rV[R]_M) : R := sup [set mxdot h^T x | x in T].

Let dot_le (h : 'rV[R]_M) x : T x -> mxdot h^T x <= frobenius h.
Proof.
by move=> Tx; rewrite (le_trans (ler_mxdot _ _))// frobenius_trmx T1// mulr1.
Qed.

Lemma gwidth_ge h x : T x -> mxdot h^T x <= gwidth_fun h.
Proof.
move=> Tx; apply: ub_le_sup; last by exists x.
by exists (frobenius h) => _ [y Ty <-]; exact: dot_le.
Qed.

Lemma gwidth_le h c : (forall x, T x -> mxdot h^T x <= c) -> gwidth_fun h <= c.
Proof.
move=> hc; apply: ge_sup; first by case: T0 => x Tx; exists (mxdot h^T x), x.
by move=> _ [x Tx <-]; exact: hc.
Qed.

Lemma gwidth_lipschitz h h' :
  `|gwidth_fun h - gwidth_fun h'| <= 1 * frobenius (h - h').
Proof.
rewrite mul1r.
have key (a b : 'rV[R]_M) : gwidth_fun a <= gwidth_fun b + frobenius (a - b).
  apply: gwidth_le => x Tx.
  have -> : mxdot a^T x = mxdot b^T x + mxdot (a - b)^T x.
    by rewrite linearB /= mxdotBl; ring.
  by apply: lerD; [exact: gwidth_ge|exact: dot_le].
rewrite ler_norml; have := key h h'; have := key h' h.
rewrite -frobeniusN opprB; lra.
Qed.

Lemma gwidth_norm h : `|gwidth_fun h| <= frobenius h.
Proof.
case: T0 => x0 Tx0; rewrite ler_norml; apply/andP; split.
  have := gwidth_ge h Tx0; have := dot_le (- h) Tx0.
  by rewrite linearN /= mxdotNl frobeniusN; lra.
by apply: gwidth_le => x Tx; exact: dot_le.
Qed.

(* inf_(x in T) |G x|. *)
Definition escape_inf N (G : 'M[R]_(N, M)) : R :=
  inf [set frobenius (G *m x) | x in T].

Lemma escape_inf_le N (G : 'M[R]_(N, M)) x :
  T x -> escape_inf G <= frobenius (G *m x).
Proof.
move=> Tx; apply: ge_inf; last by exists x.
by exists 0 => _ [y Ty <-]; exact: frobenius_ge0.
Qed.

Lemma escape_inf_ge N (G : 'M[R]_(N, M)) c :
  (forall x, T x -> c <= frobenius (G *m x)) -> c <= escape_inf G.
Proof.
move=> hc; apply: lb_le_inf.
  by case: T0 => x Tx; exists (frobenius (G *m x)), x.
by move=> _ [x Tx <-]; exact: hc.
Qed.

Lemma escape_inf_lipschitz N (G G' : 'M[R]_(N, M)) :
  `|escape_inf G - escape_inf G'| <= 1 * frobenius (G - G').
Proof.
rewrite mul1r.
have key (A B : 'M[R]_(N, M)) : escape_inf A <= escape_inf B + frobenius (A - B).
  rewrite -lerBlDr; apply: escape_inf_ge => x Tx; rewrite lerBlDr.
  apply: (le_trans (escape_inf_le A Tx)).
  have -> : A *m x = B *m x + (A - B) *m x by rewrite mulmxBl addrC subrK.
  rewrite (le_trans (frobeniusD _ _))// lerD2l.
  by rewrite (le_trans (frobenius_mulmx _ _))// T1// mulr1.
rewrite ler_norml; have := key G G'; have := key G' G.
rewrite -frobeniusN opprB; lra.
Qed.

Lemma escape_inf_ge0 N (G : 'M[R]_(N, M)) : 0 <= escape_inf G.
Proof. by apply: escape_inf_ge => x _; exact: frobenius_ge0. Qed.

Lemma escape_inf_norm N (G : 'M[R]_(N, M)) : `|escape_inf G| <= frobenius G.
Proof.
case: T0 => x0 Tx0; rewrite ger0_norm ?escape_inf_ge0//.
rewrite (le_trans (escape_inf_le G Tx0))//.
by rewrite (le_trans (frobenius_mulmx _ _))// T1// mulr1.
Qed.

End width_escape.

Section net_max.
Context {R : realType} {N : nat}.

(* If the family ys meets every ball of radius eta centered on the unit
   sphere, the largest of the <v, ys t> is at least (1 - eta) |v|. *)
Lemma rmax_net_ge l (ys : 'I_l.+1 -> 'cV[R]_N) (eta : R) (v : 'cV[R]_N) :
  (forall y, frobenius y = 1 -> exists t, frobenius (y - ys t) <= eta) ->
  (1 - eta) * frobenius v <= rmax (\row_t mxdot v (ys t)).
Proof.
move=> net; have [->|v0] := eqVneq v 0.
  rewrite frobenius0 mulr0.
  have [t ->] := rmax_eq (\row_t mxdot (0 : 'cV[R]_N) (ys t)).
  by rewrite mxE mxdot0l.
have fv : 0 < frobenius v by rewrite frobenius_gt0.
set y := (frobenius v)^-1 *: v.
have y1 : frobenius y = 1.
  by rewrite frobeniusZ ger0_norm ?invr_ge0 ?(ltW fv)// mulVf// gt_eqF.
have [t yt] := net y y1.
apply: (le_trans _ (le_rmax _ t)); rewrite mxE.
have -> : mxdot v (ys t) = mxdot v y - mxdot v (y - ys t).
  by rewrite mxdotBr; ring.
have -> : mxdot v y = frobenius v.
  rewrite mxdotZr -frobenius_sqr expr2 mulrA mulVf ?mul1r//.
  by rewrite gt_eqF.
have := ler_mxdot v (y - ys t); have := frobenius_ge0 (y - ys t); nra.
Qed.

(* An eta-net of the unit sphere, as a family indexed by an ordinal. *)
Lemma net_family (Ns : seq 'cV[R]_N) (y0 : 'cV[R]_N) (eta : R) :
  is_net (@unit_sphere R N) (y0 :: Ns) eta ->
  forall y, frobenius y = 1 ->
    exists t : 'I_(size Ns).+1, frobenius (y - nth 0 (y0 :: Ns) t) <= eta.
Proof.
move=> net y y1; have [z zN yz] := net y y1.
have zi : (index z (y0 :: Ns) < (size Ns).+1)%N by rewrite -[X in (_ < X)%N]/(size (y0 :: Ns)) index_mem.
by exists (Ordinal zi); rewrite /= nth_index.
Qed.

End net_max.

Section gordon_escape.
Context {R : realType} {N M : nat}.
Variable T : set 'cV[R]_M.
Hypothesis T1 : forall x, T x -> frobenius x = 1.
Hypothesis T0 : T !=set0.

Lemma integrable_gwidth :
  (gauss M).-integrable [set: 'rV[R]_M] (EFin \o gwidth_fun T).
Proof.
by apply: (@integrable_gauss_lipschitz _ _ _ 1) => h h'; exact: gwidth_lipschitz.
Qed.

Lemma integrable_escape_inf :
  (gauss (N * M)).-integrable [set: 'rV[R]_(N * M)]
    (EFin \o (fun a => escape_inf T (vec_mx a : 'M[R]_(N, M)))).
Proof.
apply: (@integrable_gauss_lipschitz _ _ _ 1) => a a'.
by rewrite (le_trans (escape_inf_lipschitz T1 T0 _ _))// -linearB /= frobenius_vec_mx.
Qed.

Lemma minmax_bil_le k l (xs : 'I_k.+1 -> 'cV[R]_M) (ys : 'I_l.+1 -> 'cV[R]_N)
    (delta : R) (a : 'rV[R]_(N * M)) :
  (forall t, frobenius (ys t) = 1) ->
  (forall x, T x -> exists u, frobenius (x - xs u) <= delta) ->
  minmax (vec_mx (a *m bil_mx xs ys)) <=
  escape_inf T (vec_mx a : 'M[R]_(N, M)) + delta * frobenius a.
Proof.
move=> ys1 net; rewrite -lerBlDr; apply: escape_inf_ge => // x Tx.
rewrite lerBlDr; have [u xu] := net x Tx.
apply: (le_trans (minmax_le _ u)).
have h1 : rmax (row u (vec_mx (a *m bil_mx xs ys))) <=
    frobenius ((vec_mx a : 'M[R]_(N, M)) *m xs u).
  apply: rmax_le => t; rewrite mxE bil_mxE.
  by rewrite (le_trans (ler_mxdot _ _))// ys1 mul1r.
apply: (le_trans h1).
have -> : (vec_mx a : 'M[R]_(N, M)) *m xs u =
    vec_mx a *m x + vec_mx a *m (xs u - x).
  by rewrite mulmxBr addrC subrK.
rewrite (le_trans (frobeniusD _ _))// lerD2l.
rewrite (le_trans (frobenius_mulmx _ _))// frobenius_vec_mx mulrC.
by rewrite -frobeniusN opprB ler_wpM2r// frobenius_ge0.
Qed.

Lemma rmax_fam_width k (xs : 'I_k.+1 -> 'cV[R]_M) (h : 'rV[R]_M) :
  (forall u, T (xs u)) -> rmax (h *m fam_mx xs) <= gwidth_fun T h.
Proof. by move=> xsT; apply: rmax_le => u; rewrite fam_mxE; exact: gwidth_ge. Qed.

(* Gordon's escape theorem: for the Gaussian matrix vec_mx a of size N x M,
   E[inf_(x in T) |vec_mx a *m x|] >= E[|g|] - E[sup_(x in T) <h, x>]. *)
Theorem gordon_escape : (0 < N)%N ->
  \int[gauss N]_g frobenius g - \int[gauss M]_h gwidth_fun T h <=
  \int[gauss (N * M)]_a escape_inf T (vec_mx a : 'M[R]_(N, M)).
Proof.
move=> N0.
have iG := @integrable_gauss_frobenius R N.
have iGG := @integrable_gauss_frobenius R (N * M).
set Eg := \int[gauss N]_g frobenius g.
pose EG : R := \int[gauss (N * M)]_a frobenius (a : 'rV[R]_(N * M)).
have Eg0 : 0 <= Eg by apply: Rintegral_ge0 => // g _; exact: frobenius_ge0.
have EG0 : 0 <= EG by apply: Rintegral_ge0 => // a _; exact: frobenius_ge0.
apply/ler_addgt0Pr => e e0.
pose eps := e / (Eg + EG + 1).
have C0 : 0 < Eg + EG + 1 by rewrite ltr_wpDl// addr_ge0.
have eps0 : 0 < eps by rewrite divr_gt0.
have epsC : eps * (Eg + EG) <= e.
  by rewrite /eps mulrAC ler_pdivrMr// ler_wpM2l ?(ltW e0)//; lra.
(* An eps-net xs of T and an eps-net ys of the unit sphere of 'cV[R]_N. *)
have Tr x : T x -> frobenius x <= 1 by move=> Tx; rewrite T1.
have [Ts [TsT Tsnet _]] := @net_exists R M T 1 eps ler01 eps0 Tr.
case: Ts TsT Tsnet => [|x0 Ts] TsT Tsnet; first by case: T0 => x /Tsnet [y].
have [Ns [Ns1 Nsnet _]] := @unit_sphere_net R N eps eps0.
case: Ns Ns1 Nsnet => [|y0 Ns] Ns1 Nsnet.
  have e1 : (@unit_sphere R N) (delta_mx (Ordinal N0) 0).
    by rewrite /unit_sphere /= /frobenius mxdot_delta mxE !eqxx sqrtr1.
  by have [y] := Nsnet _ e1.
pose xs (u : 'I_(size Ts).+1) := nth 0 (x0 :: Ts) u.
pose ys (t : 'I_(size Ns).+1) := nth 0 (y0 :: Ns) t.
have xsT u : T (xs u) by apply: TsT; rewrite mem_nth.
have xs1 u : frobenius (xs u) = 1 by apply: T1.
have ys1 t : frobenius (ys t) = 1 by apply: Ns1; rewrite mem_nth.
have xsnet x : T x -> exists u, frobenius (x - xs u) <= eps.
  move=> Tx; have [z zT xz] := Tsnet x Tx.
  have zi : (index z (x0 :: Ts) < (size Ts).+1)%N.
    by rewrite -[X in (_ < X)%N]/(size (x0 :: Ts)) index_mem.
  by exists (Ordinal zi); rewrite /xs /= nth_index.
(* Gordon's comparison of the auxiliary and the matrix processes. *)
have iA := integrable_gauss_minmax (aux_mx xs ys).
have iB := integrable_gauss_minmax (bil_mx xs ys).
have h12 : \int[gauss (N + M)]_z minmax (vec_mx (z *m aux_mx xs ys)) <=
    \int[gauss (N * M)]_a minmax (vec_mx (a *m bil_mx xs ys)).
  apply: fine_le; [exact: integrable_fin_num|exact: integrable_fin_num|].
  exact: aux_bil_minmax.
rewrite integral_minmax_aux in h12.
(* The mean of the soft parts. *)
have hY : (1 - eps) * Eg <= \int[gauss N]_g rmax (g *m fam_mx ys).
  have iGe : (gauss N).-integrable setT
      (EFin \o (fun g : 'rV[R]_N => (1 - eps) * frobenius g)).
    have := integrableZl measurableT (1 - eps) iG.
    by apply: eq_integrable => // g _.
  rewrite /Eg -RintegralZl//.
  apply: le_Rintegral => //; first exact: integrable_gauss_rmax.
  move=> g _; have := rmax_net_ge g^T (net_family Nsnet).
  rewrite frobenius_trmx.
  suff -> : \row_t mxdot g^T (nth 0 (y0 :: Ns) t) = g *m fam_mx ys by [].
  by apply/rowP => t; rewrite mxE fam_mxE.
have hX : \int[gauss M]_h rmax (h *m fam_mx xs) <= \int[gauss M]_h gwidth_fun T h.
  apply: le_Rintegral => //; first exact: integrable_gauss_rmax.
    exact: integrable_gwidth.
  by move=> h _; exact: rmax_fam_width.
have hB : \int[gauss (N * M)]_a minmax (vec_mx (a *m bil_mx xs ys)) <=
    \int[gauss (N * M)]_a escape_inf T (vec_mx a : 'M[R]_(N, M)) + eps * EG.
  have iFe : (gauss (N * M)).-integrable setT
      (EFin \o (fun a : 'rV[R]_(N * M) => eps * frobenius a)).
    have := integrableZl measurableT eps iGG.
    by apply: eq_integrable => // a _.
  have iS : (gauss (N * M)).-integrable setT (EFin \o (fun a : 'rV[R]_(N * M) =>
      escape_inf T (vec_mx a : 'M[R]_(N, M)) + eps * frobenius a)).
    rewrite (_ : EFin \o _ =
      (EFin \o (fun a => escape_inf T (vec_mx a : 'M[R]_(N, M)))) \+
      (EFin \o (fun a : 'rV[R]_(N * M) => eps * frobenius a)))//.
    by apply: integrableD => //; exact: integrable_escape_inf.
  have iI := integrable_escape_inf.
  rewrite /EG -RintegralZl// -RintegralD//.
  by apply: le_Rintegral => // a _; exact: minmax_bil_le.
have := ltW eps0; lra.
Qed.

(* Escape through a mesh: inf_(x in T) |G x| falls below
   E[|g|] - E[sup_(x in T) <h, x>] - u with probability at most
   expR (- u^2 / 2). *)
Theorem gordon_escape_tail (u : R) : (0 < N)%N -> 0 <= u ->
  (gauss (N * M) [set a | escape_inf T (vec_mx a : 'M[R]_(N, M)) <=
     \int[gauss N]_g frobenius g - \int[gauss M]_h gwidth_fun T h - u]%R <=
   (expR (- u ^+ 2 / 2))%:E)%E.
Proof.
move=> N0 u0.
have FL (a a' : 'rV[R]_(N * M)) : `|escape_inf T (vec_mx a : 'M[R]_(N, M)) -
    escape_inf T (vec_mx a' : 'M[R]_(N, M))| <= 1 * frobenius (a - a').
  by rewrite (le_trans (escape_inf_lipschitz T1 T0 _ _))// -linearB /= frobenius_vec_mx.
have mF := continuous_measurable_mx (lipschitz_frobenius_continuous FL).
have mI (A : set R) : measurable A ->
    measurable ((fun a : 'rV[R]_(N * M) => escape_inf T (vec_mx a : 'M[R]_(N, M))) @^-1` A).
  by move=> mA; rewrite -[X in measurable X]setTI; exact: mF.
have := gauss_concentration_lower_tail FL u0.
rewrite expr1n mulr1; apply: le_trans; apply: le_measure; rewrite ?inE.
- by rewrite -preimage_itvNyc; apply: mI; exact: measurable_itv.
- by rewrite -preimage_itvNyc; apply: mI; exact: measurable_itv.
- by move=> a /=; have := gordon_escape N0; lra.
Qed.

End gordon_escape.

Section seq_index.

Lemma seq_index (T : eqType) (d x0 : T) (s : seq T) y : y \in x0 :: s ->
  exists t : 'I_(size s).+1, nth d (x0 :: s) t = y.
Proof.
move=> ys; have yi : (index y (x0 :: s) < (size s).+1)%N.
  by rewrite -[X in (_ < X)%N]/(size (x0 :: s)) index_mem.
by exists (Ordinal yi); rewrite /= nth_index.
Qed.

End seq_index.

Section symmetric_net.
Context {R : realType} {n : nat}.

(* A symmetric eps-net of the unit sphere of 'cV[R]_n, as a family. *)
Lemma sym_sphere_net (eps : R) : 0 < eps -> (0 < n)%N ->
  exists (k : nat) (ys : 'I_k.+1 -> 'cV[R]_n),
    [/\ forall t, frobenius (ys t) = 1,
        forall t, exists t', ys t' = - ys t &
        forall y, frobenius y = 1 -> exists t, frobenius (y - ys t) <= eps].
Proof.
move=> eps0 n0.
have [Ns [Ns1 Nsnet _]] := @unit_sphere_net R n eps eps0.
case: Ns Ns1 Nsnet => [|y0 Ns] Ns1 Nsnet.
  have e1 : (@unit_sphere R n) (delta_mx (Ordinal n0) 0).
    by rewrite /unit_sphere /= /frobenius mxdot_delta mxE !eqxx sqrtr1.
  by have [y] := Nsnet _ e1.
pose S := Ns ++ map -%R (y0 :: Ns).
have memS y : y \in y0 :: S = (y \in y0 :: Ns) || (- y \in y0 :: Ns).
  rewrite /S -cat_cons mem_cat; congr orb.
  apply/mapP/idP => [[z zN ->]|yN]; first by rewrite opprK.
  by exists (- y); rewrite ?opprK.
have memt (t : 'I_(size S).+1) : nth 0 (y0 :: S) t \in y0 :: S.
  by apply: mem_nth.
exists (size S), (fun t => nth 0 (y0 :: S) t); split.
- move=> t; have := memt t; rewrite memS => /orP[/Ns1//|/Ns1].
  by rewrite frobeniusN.
- move=> t; have : - nth 0 (y0 :: S) t \in y0 :: S.
    by have := memt t; rewrite !memS opprK orbC.
  by move=> /(seq_index 0) [t' t'E]; exists t'.
- move=> y y1; have [z zN yz] := Nsnet y y1.
  have : z \in y0 :: S by rewrite memS zN.
  by move=> /(seq_index 0) [t zt]; exists t; rewrite zt.
Qed.

End symmetric_net.

Section gauss_opnorm.
Context {R : realType} {N M : nat}.

Lemma opnorm_lipschitz (A B : 'M[R]_(N, M)) :
  `|opnorm A - opnorm B| <= frobenius (A - B).
Proof.
have h (X Y : 'M[R]_(N, M)) : opnorm X <= opnorm Y + frobenius (X - Y).
  have -> : opnorm X = opnorm (Y + (X - Y)) by rewrite addrC subrK.
  by rewrite (le_trans (opnormD _ _))// lerD2l opnorm_le_frobenius.
rewrite ler_norml; have := h A B; have := h B A.
rewrite -frobeniusN opprB; lra.
Qed.

Lemma integrable_gauss_opnorm :
  (gauss (N * M)).-integrable [set: 'rV[R]_(N * M)]
    (EFin \o (fun a => opnorm (vec_mx a : 'M[R]_(N, M)))).
Proof.
apply: (@integrable_gauss_lipschitz _ _ _ 1) => a a'.
by rewrite mul1r (le_trans (opnorm_lipschitz _ _))// -linearB /= frobenius_vec_mx.
Qed.

(* The operator norm of the N x M standard Gaussian matrix vec_mx a has
   mean at most E[|g|] + E[|h|], for g of law gauss N and h of law
   gauss M. *)
Theorem gauss_opnorm_mean : (0 < N)%N -> (0 < M)%N ->
  \int[gauss (N * M)]_a opnorm (vec_mx a : 'M[R]_(N, M)) <=
  \int[gauss N]_g frobenius g + \int[gauss M]_h frobenius h.
Proof.
move=> N0 M0.
have iG := @integrable_gauss_frobenius R N.
have iH := @integrable_gauss_frobenius R M.
set S := \int[gauss N]_g frobenius g + \int[gauss M]_h frobenius h.
have S0 : 0 <= S.
  by rewrite addr_ge0// Rintegral_ge0// => x _; exact: frobenius_ge0.
apply/ler_addgt0Pr => e e0.
pose eps := Num.min (4^-1) (e / (4 * S + 1)).
have C0 : 0 < 4 * S + 1 by rewrite ltr_wpDl// mulr_ge0.
have eps0 : 0 < eps by rewrite lt_min invr_gt0 ltr0n divr_gt0.
have eps4 : eps <= 4^-1 by rewrite ge_min lexx.
have epsS : 4 * eps * S <= e.
  have : eps <= e / (4 * S + 1) by rewrite ge_min lexx orbT.
  rewrite ler_pdivlMr// => h; nra.
have e2 : 0 < 1 - 2 * eps by lra.
have [l [ys [ys1 ysym ysnet]]] := @sym_sphere_net R N eps eps0 N0.
have [k [xs [xs1 xsym xsnet]]] := @sym_sphere_net R M eps eps0 M0.
(* The operator norm and the largest entry of the bilinear process. *)
have entry a u t : mxdot (ys t) ((vec_mx a : 'M[R]_(N, M)) *m xs u) <=
    rmax (a *m bil_mx xs ys).
  by rewrite -bil_mxE mxE; exact: le_rmax.
have hop a : opnorm (vec_mx a : 'M[R]_(N, M)) <=
    rmax (a *m bil_mx xs ys) / (1 - 2 * eps).
  apply: (@opnorm_net_sphere R N M (vec_mx a) [seq ys t | t <- enum 'I_l.+1]
    [seq xs u | u <- enum 'I_k.+1] eps); first exact: ltW.
  - lra.
  - have [t' t'E] := ysym ord0.
    have := entry a ord0 ord0; have := entry a ord0 t'.
    by rewrite t'E mxdotNl; lra.
  - move=> y y1; have [t yt] := ysnet y y1.
    by exists (ys t) => //; apply/mapP; exists t; rewrite ?mem_enum.
  - by move=> _ /mapP[t _ ->]; rewrite ys1.
  - move=> x x1; have [u xu] := xsnet x x1.
    by exists (xs u) => //; apply/mapP; exists u; rewrite ?mem_enum.
  - move=> _ _ /mapP[t _ ->] /mapP[u _ ->]; rewrite ler_norml entry andbT.
    have [t' t'E] := ysym t; have := entry a u t'.
    by rewrite t'E mxdotNl lerNl.
(* Integrate, compare the processes and bound the auxiliary one. *)
have iO := @integrable_gauss_opnorm.
have iB := integrable_gauss_rmax (bil_mx xs ys).
have iA := integrable_gauss_rmax (aux_mx xs ys).
have iBe : (gauss (N * M)).-integrable setT (EFin \o
    (fun a : 'rV[R]_(N * M) => rmax (a *m bil_mx xs ys) / (1 - 2 * eps))).
  have := integrableZr measurableT (1 - 2 * eps)^-1 iB.
  by apply: eq_integrable => // a _.
have h1 : \int[gauss (N * M)]_a opnorm (vec_mx a : 'M[R]_(N, M)) <=
    \int[gauss (N * M)]_a rmax (a *m bil_mx xs ys) / (1 - 2 * eps).
  rewrite -RintegralZr//; apply: le_Rintegral => // a _; exact: hop.
have h2 : \int[gauss (N * M)]_a rmax (a *m bil_mx xs ys) <=
    \int[gauss (N + M)]_z rmax (z *m aux_mx xs ys).
  apply: fine_le; [exact: integrable_fin_num|exact: integrable_fin_num|].
  exact: bil_aux_max.
have h3 : \int[gauss (N + M)]_z rmax (z *m aux_mx xs ys) <= S.
  rewrite integral_rmax_aux addrC; apply: lerD.
    apply: le_Rintegral => //; first exact: integrable_gauss_rmax.
    move=> g _; apply: rmax_le => t; rewrite fam_mxE.
    by rewrite (le_trans (ler_mxdot _ _))// frobenius_trmx ys1 mulr1.
  apply: le_Rintegral => //; first exact: integrable_gauss_rmax.
  move=> h _; apply: rmax_le => u; rewrite fam_mxE.
  by rewrite (le_trans (ler_mxdot _ _))// frobenius_trmx xs1 mulr1.
apply: (le_trans h1); rewrite ler_pdivrMr//.
have : \int[gauss (N * M)]_a rmax (a *m bil_mx xs ys) <= S by lra.
nra.
Qed.

Theorem gauss_opnorm_tail (u : R) : (0 < N)%N -> (0 < M)%N -> 0 <= u ->
  (gauss (N * M) [set a | \int[gauss N]_g frobenius g +
     \int[gauss M]_h frobenius h + u <= opnorm (vec_mx a : 'M[R]_(N, M))]%R <=
   (expR (- u ^+ 2 / 2))%:E)%E.
Proof.
move=> N0 M0 u0.
have FL (a a' : 'rV[R]_(N * M)) : `|opnorm (vec_mx a : 'M[R]_(N, M)) -
    opnorm (vec_mx a' : 'M[R]_(N, M))| <= 1 * frobenius (a - a').
  by rewrite mul1r (le_trans (opnorm_lipschitz _ _))// -linearB /= frobenius_vec_mx.
have mF := continuous_measurable_mx (lipschitz_frobenius_continuous FL).
have mI (A : set R) : measurable A ->
    measurable ((fun a : 'rV[R]_(N * M) => opnorm (vec_mx a : 'M[R]_(N, M))) @^-1` A).
  by move=> mA; rewrite -[X in measurable X]setTI; exact: mF.
have := gauss_concentration_upper_tail FL u0.
rewrite expr1n mulr1; apply: le_trans; apply: le_measure; rewrite ?inE.
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by move=> a /=; have := gauss_opnorm_mean N0 M0; lra.
Qed.

End gauss_opnorm.

Section gauss_frobenius_mean.
Context {R : realType}.

(* The mean Euclidean norm of a standard Gaussian vector of 'rV[R]_n is at
   most sqrt n. *)
Lemma gauss_frobenius_mean_le n :
  \int[gauss n]_g frobenius (g : 'rV[R]_n) <= Num.sqrt n%:R.
Proof.
have F2 (g : 'rV[R]_n) : frobenius g ^+ 2 = \sum_i g 0 i * g 0 i.
  by rewrite frobenius_sqr /mxdot big_ord1.
have cF : continuous (fun g : 'rV[R]_n => frobenius g).
  apply: (@lipschitz_frobenius_continuous _ _ _ 1) => x y.
  by rewrite mul1r ler_frobeniusB.
have mF := continuous_measurable_mx cF.
have ic (i : 'I_n) : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun g : 'rV[R]_n => g 0 i * g 0 i)).
  have cc : continuous (fun g : 'rV[R]_n => g 0 i * g 0 i).
    move=> g; apply: (@cvgM _ _ _ _ (fun g : 'rV[R]_n => g 0 i)
      (fun g : 'rV[R]_n => g 0 i)); first exact: nbhs_filter.
      exact: coord_continuous.
    exact: coord_continuous.
  apply: (integrable_gauss_poly (continuous_measurable_mx cc) (C := 1) (k := 2)).
  move=> g; rewrite mul1r normrM -expr2.
  by have := mx_norm_entry_le g 0 i; have := normr_ge0 (g 0 i); nra.
have i2 : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun g : 'rV[R]_n => frobenius g ^+ 2)).
  have -> : EFin \o (fun g : 'rV[R]_n => frobenius g ^+ 2) =
      (fun x => \sum_i (EFin \o (fun g : 'rV[R]_n => g 0 i * g 0 i)) x).
    by apply/funext => g; rewrite /= F2 sumEFin.
  by apply: integrable_sum => // i _; exact: ic.
have E2 : \int[gauss n]_g frobenius (g : 'rV[R]_n) ^+ 2 = n%:R.
  under eq_Rintegral do rewrite F2.
  rewrite Rintegral_sum//; under eq_bigr do rewrite /Rintegral gauss_cov eqxx.
  by rewrite sumr_const card_ord /= mulr1n.
have := expectation_sqr_le (integrable_sqr_Lfun2 mF i2).
rewrite !unlock /= [X in _ <= X -> _](_ : _ = n%:R); last first.
  have E0 : 0 <= \int[gauss n]_g frobenius (g : 'rV[R]_n).
    by apply: Rintegral_ge0 => // g _; exact: frobenius_ge0.
  by move=> h; rewrite -(ger0_norm E0) -sqrtr_sqr ler_wsqrtr.
by rewrite -E2; apply: congr1; apply: eq_integral => w _; rewrite exprfctE.
Qed.

End gauss_frobenius_mean.


Section gauss_matrix_bounds.
Context {R : realType} {N M : nat}.

Corollary gauss_opnorm_mean_sqrt : (0 < N)%N -> (0 < M)%N ->
  \int[gauss (N * M)]_a opnorm (vec_mx a : 'M[R]_(N, M)) <=
  Num.sqrt N%:R + Num.sqrt M%:R.
Proof.
move=> N0 M0; rewrite (le_trans (gauss_opnorm_mean N0 M0))//.
by apply: lerD; exact: gauss_frobenius_mean_le.
Qed.

(* The Gaussian width of the unit sphere of 'cV[R]_M is E[|h|]. *)
Lemma gwidth_sphere (h : 'rV[R]_M) : (0 < M)%N ->
  gwidth_fun (@unit_sphere R M) h = frobenius h.
Proof.
move=> M0; have S1 x : (@unit_sphere R M) x -> frobenius x = 1 by [].
have S0 : (@unit_sphere R M) !=set0.
  exists (delta_mx (Ordinal M0) 0).
  by rewrite /unit_sphere /= /frobenius mxdot_delta mxE !eqxx sqrtr1.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: (gwidth_le S0) => x x1.
  by rewrite (le_trans (ler_mxdot _ _))// frobenius_trmx S1// mulr1.
have [->|h0] := eqVneq h 0.
  rewrite frobenius0; have [x Sx] := S0.
  by rewrite (le_trans _ (gwidth_ge S1 _ Sx))// trmx0 mxdot0l.
have fh : 0 < frobenius h by rewrite frobenius_gt0.
have x1 : (@unit_sphere R M) ((frobenius h)^-1 *: h^T).
  rewrite /unit_sphere /= frobeniusZ frobenius_trmx ger0_norm ?invr_ge0 ?(ltW fh)//.
  by rewrite mulVf// gt_eqF.
rewrite (le_trans _ (gwidth_ge S1 _ x1))// mxdotZr.
rewrite -frobenius_sqr frobenius_trmx expr2 mulrA mulVf ?mul1r//.
by rewrite gt_eqF.
Qed.

(* The smallest singular value: E[inf_(|x| = 1) |G x|] >= E[|g|] - E[|h|]. *)
Corollary gauss_min_singular_mean : (0 < N)%N -> (0 < M)%N ->
  \int[gauss N]_g frobenius g - \int[gauss M]_h frobenius h <=
  \int[gauss (N * M)]_a escape_inf (@unit_sphere R M) (vec_mx a : 'M[R]_(N, M)).
Proof.
move=> N0 M0.
have S1 x : (@unit_sphere R M) x -> frobenius x = 1 by [].
have S0 : (@unit_sphere R M) !=set0.
  exists (delta_mx (Ordinal M0) 0).
  by rewrite /unit_sphere /= /frobenius mxdot_delta mxE !eqxx sqrtr1.
have := gordon_escape S1 S0 N0.
have -> // : \int[gauss M]_h gwidth_fun (@unit_sphere R M) h =
    \int[gauss M]_h frobenius h.
by apply: eq_Rintegral => h _; rewrite gwidth_sphere.
Qed.

End gauss_matrix_bounds.
