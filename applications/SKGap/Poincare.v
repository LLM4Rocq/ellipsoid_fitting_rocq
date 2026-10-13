From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp reals sequences exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm spectral_gap.
From GaussianAnalysis.random_matrix Require Import goe.
From GaussianApplications Require Import SKGapDefinitions.
From GaussianApplications.SKGap Require Import Ising TwoSpin Spectral.

(**md**************************************************************************)
(* # The spectral gap and the covariance under good disorder                  *)
(*                                                                            *)
(* Part of target T4 of phase 12 (AGENTS.md, section Phase 12). A Rocq        *)
(* formalization of the credited argument of the proposition 'Gap and         *)
(* covariance under scaled interactions and fields' of 'Cutoff throughout the *)
(* high-temperature Sherrington-Kirkpatrick phase' (family 227 of the OpenAI  *)
(* math collection, revision 1581d4cbd, appendices/entropy.tex). The Lean     *)
(* counterpart:                                                               *)
(* Lean: exists_uniform_gap_tolerance (SKRatio/Variational/UniformGap.lean)   *)
(*                                                                            *)
(* - ising_gen_sq_ge, the sum of the two-spin inequality (ising_two_spin of   *)
(*   TwoSpin.v) over the ordered pairs: with T = (tanh A_ij), T2 = (tanh^2    *)
(*   A_ij), opnorm T <= M, 2 opnorm T2 <= M and sum_j |tanh A_ij|^3 <= rho    *)
(*   for every i, and |tanh A_ij| <= 1/1000: nu[(sum_i D_i f)^2] >= (1 - M -  *)
(*   140000 rho) E(f). The two quadratic forms are bounded by operator norms, *)
(*   with v_i^2 (1 + m_i^2) <= v_i, as in the manuscript.                     *)
(* - ising_cov_from_gap: from k Var_nu(f) <= E(f) for every f, opnorm         *)
(*   Cov_nu(x) <= 1 / k, by the linear functions f(x) = <c, x>, for which d_i *)
(*   f = c_i (half_diff_form).                                                *)
(* - sk_gap_deterministic: for 0 <= beta < 1/2, 0 < delta <= sk_gap_tol beta  *)
(*   = min (1/2000) ((1 - 2 beta) / 400000), J symmetric with zero diagonal,  *)
(*   opnorm J <= 2 beta + delta, sum_j J_ij^2 <= beta^2 + delta for every     *)
(*   row, |J_ij| <= delta, and 0 <= s <= 1: kappa Var_nu(f) <= E(f) for every *)
(*   f and opnorm Cov_nu(x) <= 1 / kappa, with kappa = (1 - 2 beta) / 2 and   *)
(*   nu the Ising law of s J with any field. It combines ising_gen_sq_ge, the *)
(*   bounds |tanh u| <= |u| and |tanh u - u| <= |u|^3 with the Schur test     *)
(*   (opnorm_row_sum of library/matrix/spectral_gap.v), and the spectral step *)
(*   ising_gap_from_square of Spectral.v. The manuscript states the gap for   *)
(*   all large n on its good-disorder event; here the tolerance is explicit   *)
(*   and works for every n.                                                   *)
(* - sk_coupling_sym, sk_coupling_diag: the SK coupling is symmetric with     *)
(*   zero diagonal.                                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section pair_sum.
Variables (R : realType) (n : nat) (A : 'M[R]_n) (theta : 'cV[R]_n).
Hypothesis Asym : A \is symmetricmx.
Hypothesis Adiag : forall k, A k k = 0.
Local Notation cube := {ffun 'I_n -> bool}.
Local Notation E := (ising_mean A theta).
Local Notation m := (ising_cond_mean A theta).
Local Notation v := (ising_cond_var A theta).
Local Notation D := (ising_dproj A theta).
Implicit Types (x : cube) (i j : 'I_n) (f : cube -> R).

Definition sk_tanh_mx : 'M[R]_n := \matrix_(i, j) sk_tanh (A i j).
Definition sk_tanh2_mx : 'M[R]_n := \matrix_(i, j) sk_tanh (A i j) ^+ 2.

Lemma sk_tanh_diag i : sk_tanh (A i i) = 0.
Proof. by rewrite Adiag sk_tanh0. Qed.

Lemma A_sym i j : A j i = A i j.
Proof. by move/symmetricmxP: Asym => /(congr1 (fun M : 'M[R]_n => M i j)); rewrite mxE. Qed.

Lemma ising_gen_sq_expand f :
  E (fun x => ising_gen A theta f x ^+ 2) =
  \sum_i (E (fun x => v i x * half_diff i f x ^+ 2) +
          \sum_(j | j != i) E (fun x => D i f x * D j f x)).
Proof.
rewrite /ising_gen.
have -> : E (fun x => (\sum_i D i f x) ^+ 2) =
    E (fun x => \sum_i \sum_j D i f x * D j f x).
  apply: ising_mean_ext => x; rewrite expr2 mulr_suml.
  by apply: eq_bigr => i _; rewrite mulr_sumr.
rewrite ising_mean_sum; apply: eq_bigr => i _.
rewrite ising_mean_sum (bigD1 i) //=; congr (_ + _).
rewrite -ising_energy; apply: ising_mean_ext => x.
by rewrite expr2.
Qed.

(* The quadratic forms of the two-spin inequality, summed over the pairs. *)
Lemma pair_quad_le f x (M : R) :
  opnorm sk_tanh_mx <= M -> 2 * opnorm sk_tanh2_mx <= M ->
  \sum_i \sum_j (sk_tanh (A i j) + 2 * sk_tanh (A i j) ^+ 2 * m i x * m j x) *
     v i x * v j x * half_diff i f x * half_diff j f x <=
  M * \sum_i v i x * half_diff i f x ^+ 2.
Proof.
move=> TM T2M.
pose z : 'cV[R]_n := \col_i (v i x * half_diff i f x).
pose z' : 'cV[R]_n := \col_i (m i x * (v i x * half_diff i f x)).
have M0 : 0 <= M by apply: le_trans (opnorm_ge0 _) TM.
have -> : \sum_i \sum_j (sk_tanh (A i j) + 2 * sk_tanh (A i j) ^+ 2 * m i x * m j x) *
     v i x * v j x * half_diff i f x * half_diff j f x =
    mxdot z (sk_tanh_mx *m z) + 2 * mxdot z' (sk_tanh2_mx *m z').
  rewrite !mxdot_mulmx_sum mulr_sumr -big_split /=; apply: eq_bigr => i _.
  rewrite mulr_sumr -big_split /=; apply: eq_bigr => j _.
  by rewrite /z /z' /sk_tanh_mx /sk_tanh2_mx !mxE; ring.
have q1 : mxdot z (sk_tanh_mx *m z) <= M * mxdot z z.
  apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_opnorm _ _ _) _.
  rewrite -mulrA -expr2 frobenius_sqr; apply: ler_wpM2r => //.
  exact: mxdot_ge0.
have q2 : 2 * mxdot z' (sk_tanh2_mx *m z') <= M * mxdot z' z'.
  have h : mxdot z' (sk_tanh2_mx *m z') <= opnorm sk_tanh2_mx * mxdot z' z'.
    apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_opnorm _ _ _) _.
    by rewrite -mulrA -expr2 frobenius_sqr.
  have h2 := ler_wpM2r (mxdot_ge0 z') T2M.
  by rewrite -mulrA in h2; lra.
have hzz : mxdot z z + mxdot z' z' <= \sum_i v i x * half_diff i f x ^+ 2.
  rewrite /mxdot -big_split /=; apply: ler_sum => i _; rewrite !big_ord1 /z /z' !mxE.
  have v0 := ising_cond_var_ge0 A theta i x.
  have hv : v i x = 1 - m i x ^+ 2 by [].
  have := sqr_ge0 (half_diff i f x); have := sqr_ge0 (m i x).
  move: hv v0; set d := half_diff i f x; set mm := m i x; set vv := v i x.
  move=> hv v0 m0 d0.
  have h1 : vv * (1 + mm ^+ 2) <= 1 by rewrite hv; nra.
  have h2 : vv * vv * (1 + mm ^+ 2) <= vv.
    by rewrite -mulrA; apply: ler_piMr.
  have : vv * vv * (1 + mm ^+ 2) * d ^+ 2 <= vv * d ^+ 2 by apply: ler_wpM2r.
  by rewrite !expr2; lra.
have := ler_wpM2l M0 hzz; rewrite mulrDr.
by lra.
Qed.

Lemma ising_gen_sq_ge f (M rho : R) :
  (forall i j, `|sk_tanh (A i j)| <= 1 / 10 ^+ 3) ->
  opnorm sk_tanh_mx <= M -> 2 * opnorm sk_tanh2_mx <= M ->
  (forall i, \sum_j `|sk_tanh (A i j)| ^+ 3 <= rho) ->
  (1 - M - 14 * 10 ^+ 4 * rho) * ising_dirichlet A theta f <=
  E (fun x => ising_gen A theta f x ^+ 2).
Proof.
move=> tsmall TM T2M Trho.
pose e i := E (fun x => v i x * half_diff i f x ^+ 2).
pose c3 i j := `|sk_tanh (A i j)| ^+ 3.
pose Q i j := E (fun x => (sk_tanh (A i j) + 2 * sk_tanh (A i j) ^+ 2 * m i x * m j x) *
     v i x * v j x * half_diff i f x * half_diff j f x).
have e0 i : 0 <= e i.
  apply: ising_mean_ge0 => x; apply: mulr_ge0; last exact: sqr_ge0.
  exact: ising_cond_var_ge0.
have hpair i j : j != i ->
    - Q i j - 7 * 10 ^+ 4 * c3 i j * (e i + e j) <= E (fun x => D i f x * D j f x).
  move=> ji; have ij : i != j by rewrite eq_sym.
  exact: (ising_two_spin theta Asym Adiag f ij (tsmall i j)).
have H1 : \sum_i (e i + \sum_(j | j != i) (- Q i j - 7 * 10 ^+ 4 * c3 i j * (e i + e j))) <=
    E (fun x => ising_gen A theta f x ^+ 2).
  rewrite ising_gen_sq_expand; apply: ler_sum => i _; rewrite lerD2l.
  by apply: ler_sum => j ji; exact: hpair.
have H2 : \sum_i (e i + \sum_(j | j != i) (- Q i j - 7 * 10 ^+ 4 * c3 i j * (e i + e j))) =
    \sum_i e i + (- (\sum_i \sum_(j | j != i) Q i j) -
      7 * 10 ^+ 4 * \sum_i \sum_(j | j != i) c3 i j * (e i + e j)).
  rewrite big_split /=; congr (_ + _).
  rewrite -sumrN mulr_sumr -sumrB; apply: eq_bigr => i _.
  by rewrite -sumrN mulr_sumr -sumrB; apply: eq_bigr => j _; rewrite mulrA.
have Qdiag i : Q i i = 0.
  rewrite -[RHS](ising_mean_cst A theta 0); apply: ising_mean_ext => x.
  by rewrite sk_tanh_diag; ring.
have H3 : \sum_i \sum_(j | j != i) Q i j <= M * \sum_i e i.
  have -> : \sum_i \sum_(j | j != i) Q i j = \sum_i \sum_j Q i j.
    by apply: eq_bigr => i _; rewrite [in RHS](bigD1 i) //= Qdiag add0r.
  rewrite /Q /=; under eq_bigr do rewrite -ising_mean_sum.
  rewrite -ising_mean_sum /e -ising_mean_sum -ising_meanZ.
  by apply: ising_mean_le => x; exact: (pair_quad_le f x TM T2M).
have c3diag i : c3 i i = 0 by rewrite /c3 sk_tanh_diag normr0 expr0n.
have c3sym i j : c3 j i = c3 i j by rewrite /c3 A_sym.
have H4 : \sum_i \sum_(j | j != i) c3 i j * (e i + e j) <= 2 * rho * \sum_i e i.
  have -> : \sum_i \sum_(j | j != i) c3 i j * (e i + e j) =
      \sum_i \sum_j c3 i j * (e i + e j).
    by apply: eq_bigr => i _; rewrite [in RHS](bigD1 i) //= c3diag mul0r add0r.
  have -> : \sum_i \sum_j c3 i j * (e i + e j) =
      \sum_i \sum_j c3 i j * e i + \sum_i \sum_j c3 i j * e j.
    rewrite -big_split /=; apply: eq_bigr => i _.
    by rewrite -big_split /=; apply: eq_bigr => j _; ring.
  have e1 : \sum_i \sum_j c3 i j * e j = \sum_i \sum_j c3 i j * e i.
    rewrite exchange_big /=; apply: eq_bigr => i _; apply: eq_bigr => j _.
    by rewrite c3sym.
  have h1 : \sum_i \sum_j c3 i j * e i <= rho * \sum_i e i.
    rewrite mulr_sumr; apply: ler_sum => i _; rewrite -mulr_suml.
    by apply: ler_wpM2r; [exact: e0 | exact: Trho].
  by rewrite e1; lra.
have H5 : 0 <= \sum_i e i by rewrite sumr_ge0.
have -> : ising_dirichlet A theta f = \sum_i e i by [].
move: H1 H2 H3 H4 H5; set S := \sum_i e i.
set X := \sum_i (e i + _); set Y := \sum_i \sum_(j | j != i) Q i j.
set W := \sum_i \sum_(j | j != i) c3 i j * (e i + e j).
set G := E (fun x => ising_gen A theta f x ^+ 2).
clearbody S X Y W G => H1 H2 H3 H4 H5.
lra.
Qed.

End pair_sum.

Section covariance.
Variables (R : realType) (n : nat) (A : 'M[R]_n) (theta : 'cV[R]_n).
Local Notation cube := {ffun 'I_n -> bool}.
Local Notation E := (ising_mean A theta).
Implicit Types (x : cube) (c : 'cV[R]_n).

Lemma ising_var_alt (f : cube -> R) :
  ising_var A theta f = E (fun x => f x ^+ 2) - E f ^+ 2.
Proof.
rewrite /ising_var.
have -> : E (fun x => (f x - E f) ^+ 2) =
    E (fun x => f x ^+ 2 + (- 2 * E f) * f x + E f ^+ 2).
  by apply: ising_mean_ext => x; ring.
by rewrite !ising_meanD ising_meanZ ising_mean_cst; ring.
Qed.

Lemma spin_form_sum c x : mxdot c (spin_vec x) = \sum_k c k 0 * spin (x k).
Proof. by rewrite /mxdot; apply: eq_bigr => k _; rewrite big_ord1 mxE. Qed.

Lemma half_diff_form c i x :
  half_diff i (fun y => mxdot c (spin_vec y)) x = c i 0.
Proof.
rewrite /half_diff !spin_form_sum (bigD1 i) //= [X in _ - X](bigD1 i) //=.
rewrite !spin_set_same.
have -> : \sum_(k | k != i) c k 0 * spin (spin_set x i true k) =
    \sum_(k | k != i) c k 0 * spin (spin_set x i false k).
  by apply: eq_bigr => k ki; rewrite !spin_set_other.
by rewrite /spin; field.
Qed.

Lemma ising_dirichlet_form c :
  ising_dirichlet A theta (fun y => mxdot c (spin_vec y)) <= mxdot c c.
Proof.
rewrite /ising_dirichlet /mxdot; apply: ler_sum => i _; rewrite big_ord1.
rewrite -[X in _ <= X](ising_mean_cst A theta) -expr2.
apply: ising_mean_le => x; rewrite half_diff_form.
apply: ler_piMl; first exact: sqr_ge0.
exact: ising_cond_var_le1.
Qed.

Lemma ising_cov_form c :
  mxdot c (ising_cov A theta *m c) = ising_var A theta (fun y => mxdot c (spin_vec y)).
Proof.
rewrite ising_var_alt mxdot_mulmx_sum.
have -> : E (fun y => mxdot c (spin_vec y) ^+ 2) =
    \sum_k \sum_l c k 0 * c l 0 * E (fun y => spin (y k) * spin (y l)).
  have -> : (fun y => mxdot c (spin_vec y) ^+ 2) =
      (fun y => \sum_k \sum_l c k 0 * c l 0 * (spin (y k) * spin (y l))).
    apply/funext => y; rewrite spin_form_sum expr2 mulr_suml.
    apply: eq_bigr => k _; rewrite mulr_sumr; apply: eq_bigr => l _; ring.
  rewrite ising_mean_sum; apply: eq_bigr => k _.
  rewrite ising_mean_sum; apply: eq_bigr => l _.
  by rewrite ising_meanZ.
have -> : E (fun y => mxdot c (spin_vec y)) =
    \sum_k c k 0 * E (fun y => spin (y k)).
  have -> : (fun y => mxdot c (spin_vec y)) =
      (fun y => \sum_k c k 0 * spin (y k)).
    by apply/funext => y; rewrite spin_form_sum.
  by rewrite ising_mean_sum; apply: eq_bigr => k _; rewrite ising_meanZ.
rewrite expr2 mulr_suml -sumrB; apply: eq_bigr => k _.
rewrite mulr_sumr -sumrB; apply: eq_bigr => l _.
by rewrite /ising_cov !mxE; ring.
Qed.

Lemma ising_cov_sym : ising_cov A theta \is symmetricmx.
Proof.
apply/symmetricmxP/matrixP => k l; rewrite !mxE.
have -> : E (fun x => spin (x l) * spin (x k)) = E (fun x => spin (x k) * spin (x l)).
  by apply: ising_mean_ext => x; rewrite mulrC.
by rewrite mulrC.
Qed.

Lemma ising_var_ge0 f : 0 <= ising_var A theta f.
Proof. by apply: ising_mean_ge0 => x; exact: sqr_ge0. Qed.

Lemma ising_cov_from_gap (k : R) : 0 < k ->
  (forall f, k * ising_var A theta f <= ising_dirichlet A theta f) ->
  opnorm (ising_cov A theta) <= k^-1.
Proof.
move=> k0 hgap; have ki : 0 <= k^-1 by rewrite invr_ge0 ltW.
apply/(opnorm_symP ising_cov_sym ki).
move=> c; rewrite ising_cov_form ger0_norm ?ising_var_ge0 //.
have h1 := hgap (fun y => mxdot c (spin_vec y)).
have h2 := ising_dirichlet_form c.
rewrite -(ler_pM2l k0) mulrA mulfV ?mul1r ?gt_eqF //.
exact: le_trans h1 h2.
Qed.

End covariance.

Section deterministic_gap.
Variables (R : realType) (n : nat).
Implicit Types (beta delta s : R) (J A : 'M[R]_n).


Lemma pow_le_norm (k : nat) (x y : R) : `|x| <= `|y| -> `|x| ^+ k <= `|y| ^+ k.
Proof. by move=> h; apply: (lerXn2r k) => //; exact: normr_ge0. Qed.

Lemma sqr_le_abs (x y : R) : `|x| <= `|y| -> x ^+ 2 <= y ^+ 2.
Proof.
move=> h; rewrite -[x ^+ 2]real_normK ?num_real // -[y ^+ 2]real_normK ?num_real //.
exact: pow_le_norm.
Qed.

Definition sk_gap_tol beta : R := Num.min (1 / (2 * 10 ^+ 3)) ((1 - 2 * beta) / (4 * 10 ^+ 5)).

Lemma sk_gap_tol_gt0 beta : beta < 1 / 2 -> 0 < sk_gap_tol beta.
Proof. by move=> b; rewrite /sk_gap_tol lt_min; apply/andP; split; lra. Qed.

Lemma gap_from_bounds beta delta A (theta : 'cV[R]_n) :
  0 <= beta -> beta < 1 / 2 -> 0 < delta -> delta <= sk_gap_tol beta ->
  A \is symmetricmx -> (forall i, A i i = 0) ->
  opnorm A <= 2 * beta + delta ->
  (forall i, \sum_j A i j ^+ 2 <= beta ^+ 2 + delta) ->
  (forall i j, `|A i j| <= delta) ->
  forall f, (1 - 2 * beta) / 2 * ising_var A theta f <= ising_dirichlet A theta f.
Proof.
move=> b0 b1 d0 dtol As A0 hop hrow hent.
have [d1 d2] : delta <= 1 / (2 * 10 ^+ 3) /\ delta <= (1 - 2 * beta) / (4 * 10 ^+ 5).
  by move: dtol; rewrite /sk_gap_tol le_min => /andP[].
have ht i j : `|sk_tanh (A i j)| <= `|A i j| := sk_tanh_norm_le _.
have hsmall i j : `|sk_tanh (A i j)| <= 1 / 10 ^+ 3.
  by apply: le_trans (ht i j) _; apply: le_trans (hent i j) _; lra.
have hcube i j : `|A i j| ^+ 3 <= delta * A i j ^+ 2.
  rewrite -[A i j ^+ 2]real_normK ?num_real // exprS.
  by apply: ler_wpM2r; [exact: exprn_ge0 | exact: hent].
have hrow3 i : \sum_j `|A i j| ^+ 3 <= delta * (beta ^+ 2 + delta).
  apply: (le_trans (y := \sum_j delta * A i j ^+ 2)).
    by apply: ler_sum => j _; exact: hcube.
  by rewrite -mulr_sumr; apply: ler_wpM2l; [exact: ltW | exact: hrow].
have hb2 : beta ^+ 2 <= beta / 2 by rewrite expr2; nra.
have hT : opnorm (sk_tanh_mx A) <= 2 * beta + 4 * delta.
  have -> : sk_tanh_mx A = A + (sk_tanh_mx A - A) by rewrite addrC subrK.
  apply: le_trans (opnormD _ _) _.
  have h2 : opnorm (sk_tanh_mx A - A) <= delta * (beta ^+ 2 + delta).
    apply: opnorm_row_sum.
    - by apply/symmetricmxP/matrixP => i j; rewrite !mxE (A_sym As).
    - by rewrite mulr_ge0 ?addr_ge0 ?sqr_ge0 // ltW.
    - move=> i; apply: le_trans _ (hrow3 i); apply: ler_sum => j _.
      by rewrite !mxE; exact: sk_tanh_sub_le.
  have : delta * (beta ^+ 2 + delta) <= 3 * delta.
    rewrite [delta * _]mulrC; apply: ler_wpM2r; [exact: ltW | lra].
  by lra.
have hT2 : 2 * opnorm (sk_tanh2_mx A) <= 2 * beta + 4 * delta.
  have : opnorm (sk_tanh2_mx A) <= beta ^+ 2 + delta.
    apply: opnorm_row_sum.
    - by apply/symmetricmxP/matrixP => i j; rewrite !mxE (A_sym As).
    - by rewrite addr_ge0 ?sqr_ge0 // ltW.
    - move=> i; apply: le_trans _ (hrow i); apply: ler_sum => j _.
      rewrite !mxE ger0_norm ?sqr_ge0 //.
      exact: sqr_le_abs (ht i j).
  by lra.
have hT3 i : \sum_j `|sk_tanh (A i j)| ^+ 3 <= delta * (beta ^+ 2 + delta).
  apply: le_trans _ (hrow3 i); apply: ler_sum => j _.
  exact: pow_le_norm (ht i j).
have key g : (1 - 2 * beta) / 2 * ising_dirichlet A theta g <=
    ising_mean A theta (fun x => ising_gen A theta g x ^+ 2).
  apply: le_trans _ (ising_gen_sq_ge theta As A0 g hsmall hT hT2 hT3).
  apply: ler_wpM2r; first exact: ising_dirichlet_ge0.
  have : delta * (beta ^+ 2 + delta) <= delta * (5 / 4).
    by apply: ler_wpM2l; [exact: ltW | lra].
  by lra.
exact: ising_gap_from_square key.
Qed.

Lemma scaled_bounds beta delta J s :
  J \is symmetricmx -> (forall i, J i i = 0) ->
  opnorm J <= 2 * beta + delta ->
  (forall i, \sum_j J i j ^+ 2 <= beta ^+ 2 + delta) ->
  (forall i j, `|J i j| <= delta) ->
  0 <= s -> s <= 1 ->
  [/\ s *: J \is symmetricmx, (forall i, (s *: J) i i = 0),
      opnorm (s *: J) <= 2 * beta + delta,
      (forall i, \sum_j (s *: J) i j ^+ 2 <= beta ^+ 2 + delta) &
      (forall i j, `|(s *: J) i j| <= delta)].
Proof.
move=> Js J0 hop hrow hent s0 s1.
have hJs i j : `|(s *: J) i j| <= `|J i j|.
  by rewrite mxE normrM (ger0_norm s0); exact: ler_piMl (normr_ge0 _) s1.
split.
- apply/symmetricmxP/matrixP => i j; rewrite !mxE.
  by move/symmetricmxP: Js => /(congr1 (fun M : 'M[R]_n => M i j)); rewrite mxE => ->.
- by move=> i; rewrite mxE J0 mulr0.
- rewrite opnormZ (ger0_norm s0); apply: le_trans _ hop.
  exact: ler_piMl (opnorm_ge0 _) s1.
- move=> i; apply: le_trans _ (hrow i); apply: ler_sum => j _.
  exact: sqr_le_abs (hJs i j).
- by move=> i j; exact: le_trans (hJs i j) (hent i j).
Qed.

Theorem sk_gap_deterministic beta delta J s (theta : 'cV[R]_n) :
  0 <= beta -> beta < 1 / 2 -> 0 < delta -> delta <= sk_gap_tol beta ->
  J \is symmetricmx -> (forall i, J i i = 0) ->
  opnorm J <= 2 * beta + delta ->
  (forall i, \sum_j J i j ^+ 2 <= beta ^+ 2 + delta) ->
  (forall i j, `|J i j| <= delta) ->
  0 <= s -> s <= 1 ->
  (forall f, (1 - 2 * beta) / 2 * ising_var (s *: J) theta f <=
             ising_dirichlet (s *: J) theta f) /\
  opnorm (ising_cov (s *: J) theta) <= ((1 - 2 * beta) / 2)^-1.
Proof.
move=> b0 b1 d0 dtol Js J0 hop hrow hent s0 s1.
have [As A0 hop' hrow' hent'] := scaled_bounds Js J0 hop hrow hent s0 s1.
have hgap := gap_from_bounds theta b0 b1 d0 dtol As A0 hop' hrow' hent'.
split => //.
by apply: ising_cov_from_gap hgap; apply: divr_gt0; lra.
Qed.

End deterministic_gap.

Section sk_coupling_facts.
Variable R : realType.

Lemma sk_coupling_sym n (beta : R) (a : 'rV[R]_(n * n)) :
  sk_coupling beta a \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite /sk_coupling linearZ /= linearB /= goe_mx_sym.
by rewrite tr_diag_mx.
Qed.

Lemma sk_coupling_diag n (beta : R) (a : 'rV[R]_(n * n)) i :
  sk_coupling beta a i i = 0.
Proof. by rewrite /sk_coupling !mxE eqxx mulr1n subrr mulr0. Qed.

End sk_coupling_facts.
