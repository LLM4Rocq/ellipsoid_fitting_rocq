From Stdlib Require Import Reals Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive realfun exp.
From mathcomp Require Import Rstruct_topology.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Scalar inequalities for the chi-square bounds and the maximum radius.
   - gaussian_log_remainder_bound: - ln (1 - u) - u <= u ^ 2 / (2 (1 - u))
     for 0 <= u < 1.
   - gaussian_centered_log_expression_bound: for d >= 0 and 0 <= t < 1/2,
     d / 2 * (- 2 t - ln (1 - 2 t)) <= d t ^ 2 / (1 - 2 t). The left side
     is the logarithm of E exp (t (|g| ^ 2 - d)) for a standard Gaussian
     vector g of dimension d.
   - gaussian_radius_parameter: for d, L > 0, the parameter
     t = sqrt L / (sqrt d + 2 sqrt L) lies in ]0, 1/2[ and gives
     L / t + d t / (1 - 2 t) = 2 sqrt (d L) + 2 L.

   This module imports MathComp's exp, so a bare ln would denote exp.ln;
   every statement writes Rpower.ln, Stdlib's logarithm. The two agree at
   every point (RlnE of Rstruct_topology) but are different constants, so a
   user that writes a bare ln under the same imports must write Rpower.ln
   too or rewrite with RlnE. The unqualified sqrt is Stdlib's. *)

(* Stdlib's derivative at a point gives MathComp's derivative in the
   direction 1. MathComp's is_derive x 1 f l says that the difference
   quotient (f (h + x) - f x) / h tends to l as h tends to 0 with h <> 0,
   which is what derivable_pt_lim f x l says. *)
Lemma RadiusAlgebra_is_derive_of_Reals {f : R -> R} {x l : R} :
  derivable_pt_lim f x l -> @is_derive R R^o R^o x 1 f l.
Proof.
move=> Hd.
apply: DeriveDef; last apply: cvg_lim;
  [apply/cvg_ex; exists l | exact: norm_hausdorff |].
all: apply/cvgrPdist_lt => e /RltP e0.
all: have [d Hdl] := Hd e e0.
all: rewrite near_withinE; exists (pos d); [by apply/RltP; exact: cond_pos d|].
all: move=> h /= Hh hN0.
all: have hN0' : h <> 0 by move/eqP: hN0.
all: have Hh' : Rabs h < d by move: Hh; rewrite /ball /= sub0r normrN => /RltP.
all: have H := Hdl h hN0' Hh'.
all: apply/RltP; rewrite -RabsE -RminusE Rabs_minus_sym.
all: rewrite [X in Rabs (X - _)](_ : _ = (f (x + h) - f x) / h); [|exact: H].
all: rewrite /GRing.scale /= mulr1 RplusE RminusE RdivE.
all: by rewrite [(h + x)%R]addrC mulrC.
Qed.

(* The derivative of u ^ 2 / (2 (1 - u)) + ln (1 - u) + u on ]-oo, 1[. It
   is nonnegative, and the function vanishes at 0. *)
Lemma gaussian_log_remainder_derivative u :
  u < 1 ->
  @is_derive R R^o R^o u 1 (fun v => v*v / (2*(1-v)) + Rpower.ln (1-v) + v)
    (u*u / (2*(1-u)*(1-u))).
Proof.
move=> Hu.
pose g1 := fun v : R => v*v / (2*(1-v)) + v.
pose g2 := fun v : R => 1 - v.
have H2 : derivable_pt_lim g2 u (0 - 1).
  apply: (derivable_pt_lim_minus (fun _ => 1) id);
    [exact: derivable_pt_lim_const | exact: derivable_pt_lim_id].
have H1 : derivable_pt_lim g1 u
    (((1*u + u*1) * (2*(1-u)) - 2*(0-1) * (u*u)) / Rsqr (2*(1-u)) + 1).
  apply: (derivable_pt_lim_plus (fun v => v*v / (2*(1-v))) id);
    last exact: derivable_pt_lim_id.
  apply: (derivable_pt_lim_div (fun v => v*v) (fun v => 2*(1-v))).
  - apply: (derivable_pt_lim_mult id id); exact: derivable_pt_lim_id.
  - exact: (derivable_pt_lim_scal g2).
  - lra.
have D1 := RadiusAlgebra_is_derive_of_Reals H1.
have D2 := RadiusAlgebra_is_derive_of_Reals H2.
have Hpos : (0 < g2 u)%R.
  by apply/RltP; rewrite /g2 /=; change (0 < 1 - u); lra.
(* The logarithm term is differentiated with MathComp's is_derive1_ln and
   chain rule, then moved back to Stdlib's ln with RlnE. *)
have D3 := is_derive1_comp (@is_derive1_ln R (g2 u) Hpos) D2.
have D := is_deriveD D1 D3.
have -> : (fun v => v*v / (2*(1-v)) + Rpower.ln (1-v) + v) =
    (g1 + ((@exp.ln R) \o g2))%R.
  apply: funext => v; rewrite /g1 /g2 /=.
  change (v*v / (2*(1-v)) + Rpower.ln (1-v) + v =
    (v*v / (2*(1-v)) + v) + @exp.ln R (Rminus 1 v)).
  by rewrite -RlnE; lra.
apply: is_derive_eq D _.
rewrite /g2 /=.
change ((((1*u + u*1) * (2*(1-u)) - 2*(0-1) * (u*u)) / Rsqr (2*(1-u)) + 1)
  + / (1 - u) * (0 - 1) = u*u / (2*(1-u)*(1-u))).
by unfold Rsqr; field; lra.
Qed.

(* The proof applies MathComp's ger0_derive1_ndecr on [0, u] (a function
   with a nonnegative derivative does not decrease), which rests on
   MathComp's mean value theorem. *)
Theorem gaussian_log_remainder_bound u :
  0 <= u < 1 -> - Rpower.ln (1-u) - u <= u*u / (2*(1-u)).
Proof.
move=> [Hu0 Hu1].
pose f := fun v => v*v / (2*(1-v)) + Rpower.ln (1-v) + v.
have Df x : x < 1 -> @is_derive R R^o R^o x 1 f (x*x / (2*(1-x)*(1-x))).
  exact: gaussian_log_remainder_derivative.
have key : f 0 <= f u.
  apply/RleP; apply: (@ger0_derive1_ndecr R f 0 u).
  - move=> x; rewrite in_itv /= => /andP [_ /RltP xu].
    by have [Hd _] := Df x ltac:(lra); exact Hd.
  - move=> x; rewrite in_itv /= => /andP [_ /RltP xu].
    have [_ Hv] := Df x ltac:(lra).
    rewrite derive1E Hv; apply/RleP.
    have Hx : 0 < 1 - x by lra.
    unfold Rdiv; apply: Rmult_le_pos; first nra.
    by apply/Rlt_le/Rinv_0_lt_compat; nra.
  - apply: continuous_in_subspaceT => x /[1!inE].
    rewrite /= in_itv /= => /andP [_ /RleP xu].
    have [Hd _] := Df x ltac:(lra).
    have Hc := differentiable_continuous (iffLR (derivable1_diffP _ _) Hd).
    exact Hc.
  - exact/RleP/Rle_refl.
  - by apply/RleP.
  - exact/RleP/Rle_refl.
move: key; rewrite /f !Rminus_0_r ln_1.
have Hden : 0 < 2 * (1 - u) by lra.
by unfold Rdiv; rewrite Rmult_0_l Rmult_0_l; lra.
Qed.

Theorem gaussian_centered_log_expression_bound d t :
  0 <= d -> 0 <= t < 1/2 ->
  d/2 * (-2*t - Rpower.ln (1-2*t)) <= d*t*t/(1-2*t).
Proof.
intros Hd Ht.
pose proof (gaussian_log_remainder_bound (2*t) ltac:(lra)) as H.
assert (Hmult := Rmult_le_compat_l (d/2) _ _ ltac:(lra) H).
replace (d/2 * ((2*t)*(2*t)/(2*(1-2*t)))) with (d*t*t/(1-2*t)) in Hmult
  by (field; lra).
nra.
Qed.

Theorem gaussian_radius_parameter d L :
  0 < d -> 0 < L ->
  0 < sqrt L / (sqrt d + 2*sqrt L) < 1/2 /\
  L / (sqrt L / (sqrt d + 2*sqrt L)) +
    d * (sqrt L / (sqrt d + 2*sqrt L)) /
      (1-2*(sqrt L / (sqrt d + 2*sqrt L))) =
    2*sqrt (d*L) + 2*L.
Proof.
intros Hd HL.
assert (HdS : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
assert (HLS : 0 < sqrt L) by (apply sqrt_lt_R0; exact HL).
assert (Hd2 := sqrt_def d ltac:(lra)).
assert (HL2 := sqrt_def L ltac:(lra)).
assert (Hden : 0 < sqrt d + 2*sqrt L) by lra.
assert (Hlam : 0 < sqrt L / (sqrt d + 2*sqrt L) < 1/2).
{ split.
  - apply Rdiv_lt_0_compat; lra.
  - apply (Rmult_lt_reg_r (sqrt d+2*sqrt L)); [exact Hden|].
    field_simplify; nra. }
split; [exact Hlam|].
rewrite sqrt_mult; [lra|lra|].
set (a := sqrt d) in *.
set (b := sqrt L) in *.
rewrite <- Hd2, <- HL2.
field; nra.
Qed.
