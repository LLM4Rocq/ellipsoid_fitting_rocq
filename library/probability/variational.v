From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.

(**md**************************************************************************)
(* # A scalar variational problem for a law on the line                       *)
(*                                                                            *)
(* For a law mu on the line with a finite second moment, the upper partial    *)
(* moments m(w) = E (X - w)_+ and s(w) = E (X - w)_+^2 solve the variational  *)
(* problem of Koehler and Sohn (arXiv 2608.27372, Lemmas 5.7 and 5.8): for    *)
(* c > -1 and z real, the equation w + z = c m(w) has a unique solution w,    *)
(* and                                                                        *)
(*   sup { (E (X + z) f(X))_+^2 / (E f(X)^2 + c (E f(X))^2) :                 *)
(*         f >= 0, E f(X)^2 < oo, E f(X) > 0 }  =  s(w) + c m(w)^2,           *)
(* attained at f(x) = (x - w)_+ when the right-hand side is positive.         *)
(*                                                                            *)
(* Main results:                                                              *)
(* - upper_moment1_lipschitz: 0 <= m(w1) - m(w2) <= w2 - w1 for w1 <= w2;     *)
(*   upper_moment1_ge: E X - w <= m(w); upper_moment1_le: m(w) <= E X^2 /     *)
(*   (4 w) for w > 0; upper_moment1_gt0: m(w) > 0 if mu(]b, +oo[) > 0 for     *)
(*   some b > w; upper_moment2_taylor: |s(w + h) - s(w) + 2 h m(w)|           *)
(*   <= h^2, so s' = -2 m; upper_moment2_lipschitz: 0 <= s(a) - s(b) <=       *)
(*   (b - a) (m(a) + m(b)) for a <= b; upper_moment2_eq0: m(w) = 0 forces     *)
(*   s(w) = 0.                                                                *)
(* - Lemma 5.7, first part, for c > -1: upper_cutoffE (w = upper_cutoff mu    *)
(*   c z solves w + z = c m(w)), upper_cutoff_unique (it is the only          *)
(*   solution), upper_cutoff_le (w' + z <= c m(w') if and only if w' <= w);   *)
(*   upper_cutoff_growth: (w2 - c m(w2)) - (w1 - c m(w1)) >= min(1, 1 + c)    *)
(*   (w2 - w1) for w1 <= w2.                                                  *)
(* - upper_energy_decr: E = s + c m^2 is strictly decreasing where m > 0,     *)
(*   E(w1) - E(w2) >= 2 min(1, 1 + c) m(w2) (w2 - w1) for w1 <= w2, hence     *)
(*   upper_energy_lt: E(w2) < E(w1) for w1 < w2 with m(w2) > 0;               *)
(*   upper_energy_lipschitz: |E(a) - E(b)| <= 2 (1 + |c|) m(a) (b - a),       *)
(*   hence upper_energy_continuous; upper_energy_ge: E(w) >= (1 + c) m(w)^2.  *)
(* - Lemma 5.7 (upper_variational): the supremum of upper_ratio mu c z f over *)
(*   f in upper_admissible mu is upper_value mu c z. upper_variational_le:    *)
(*   (E (X + z) f(X))_+^2 <= upper_value mu c z (E f(X)^2 + c (E f(X))^2)     *)
(*   for every measurable f >= 0 with f^2 integrable;                         *)
(*   upper_variational_attained: E (X + z) p(X) = upper_value mu c z for      *)
(*   p(x) = (x - w)_+; upper_admissible_cutoff, upper_ratio_cutoff: p is      *)
(*   admissible and optimal when the value is positive.                       *)
(* - upper_value_nondecr, upper_value_incr: z |-> upper_value mu c z is       *)
(*   nondecreasing, and strictly increasing where it is positive.             *)
(* - Lemma 5.8: upper_cutoff_stability, upper_value_stability bound the       *)
(*   cutoff and the value of mu by those of nu through the values of m and s  *)
(*   at the cutoff of nu only; upper_cutoff_cvg, upper_value_cvg: if          *)
(*   m_{mu_n} and s_{mu_n} converge to m_mu and s_mu at the cutoff of mu,     *)
(*   the cutoffs and the values of mu_n converge to those of mu.              *)
(* - Symmetric laws (the scalar part of Lemma 5.9), mu invariant under        *)
(*   x |-> -x: integrable_sym, Rintegral_sym, Rintegral_id_sym (f(-X) is      *)
(*   integrable with f(X), E f(-X) = E f(X), E X = 0); upper_moment1_sym:     *)
(*   m(-w) = m(w) + w; upper_moment2_sym: s(-w) + s(w) = E X^2 + w^2;         *)
(*   upper_cutoff_dual: the cutoff of (-c/(1 + c), -z/(1 + c)) is minus that  *)
(*   of (c, z); upper_value_dual: the two values add up to                    *)
(*   E X^2 + z^2 / (1 + c); upper_variational_sym_le: at z = 0 the bound of   *)
(*   upper_variational_le holds without the positive part,                    *)
(*   (E X f(X))^2 <= upper_value mu c 0 (E f(X)^2 + c (E f(X))^2)             *)
(*   (Proposition 5.10 (ii)).                                                 *)
(* - The energy of a two-sided clip: clip_energy mu C t = s(-t) + s(C t), the *)
(*   mean squared distance from X to [t, C t] for a symmetric law             *)
(*   (clip_energyE), and clip_value mu C, its infimum over t >= 0.            *)
(*   clip_energy_taylor: its derivative in t is 2 (m(-t) - C m(C t));         *)
(*   clip_value_attained: a point t0 >= 0 where the derivative changes sign   *)
(*   from <= 0 to >= 0 is a minimum; clip_energy_C, clip_value_nincr:         *)
(*   nonincreasing in C, with a Lipschitz bound. taylor_nincr, taylor_ndecr:  *)
(*   a function with a Taylor bound |F(t + h) - F(t) - h g(t)| <= K h^2 is    *)
(*   monotone where g has a sign (a discrete integration).                    *)
(* - Tools: Rintegral_sqr_le ((E g)^2 <= E g^2), discriminant_le (a           *)
(*   quadratic a + 2 b t + k t^2 >= 0 for all t has b^2 <= a k),              *)
(*   upper_form_ge0 (E f^2 + c (E f)^2 >= 0 for c > -1), integrable_of_sqr,   *)
(*   integrable_mul_sqr, integrable_quad_bound, Rintegral_prob_cst.           *)
(* - Finite samples: empirical s is the law of an element of a nonempty       *)
(*   list s drawn uniformly, a probability (the Dirac mass at 0 for the       *)
(*   empty list), with ge0_integral_empirical, integrable_empirical,          *)
(*   Rintegral_empirical: integrals against it are averages over s. For       *)
(*   g : 'I_d -> R, empirical_fun g is the empirical law of its values and    *)
(*   upper_moment_empirical_fun gives m and s as averages.                    *)
(* - empirical_variational_le, the finite form of Lemma 5.7 for c >= 0, with  *)
(*   weights that need not be functions of the values: for r i >= 0,          *)
(*   (1/d) sum_i (g i + z) r i <= sqrt V sqrt ((1/d) sum_i r i^2 +            *)
(*   c ((1/d) sum_i r i)^2), V = upper_value (empirical_fun g) c z;           *)
(*   empirical_variational_attained: equality of (1/d) sum_i (g i + z) p i    *)
(*   with V at p i = (g i - w)_+, w the cutoff.                               *)
(*                                                                            *)
(* Laws on the line are probabilities on measurableTypeR R, as in             *)
(* fourier/charfun.v. A finite second moment is the integrability of x^2.     *)
(*                                                                            *)
(* ```                                                                        *)
(*  upper_moment mu k w == \int[mu]_x ((x - w)_+)^k, the upper partial moment *)
(*                         of order k at w: m(w) for k = 1, s(w) for k = 2    *)
(*  upper_energy mu c w == s(w) + c m(w)^2                                    *)
(*  upper_cutoff mu c z == sup {w | w + z <= c m(w)}, the solution of         *)
(*                         w + z = c m(w) when c > -1                         *)
(*   upper_value mu c z == upper_energy mu c (upper_cutoff mu c z), the value *)
(*                         of the variational problem                         *)
(*    upper_admissible mu == the measurable f >= 0 with f^2 integrable and    *)
(*                         E f > 0                                            *)
(* upper_ratio mu c z f == (E (X + z) f(X))_+^2 / (E f(X)^2 + c (E f(X))^2)   *)
(*         empirical s == the average of the Dirac masses at the elements     *)
(*                        of s                                                *)
(*    empirical_fun g == empirical [seq g i | i <- enum 'I_d]                 *)
(*  clip_energy mu C t == s(-t) + s(C t)                                      *)
(*    clip_value mu C == the infimum of clip_energy mu C t over t >= 0        *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section upper_moments.
Context {R : realType} (mu : probability (measurableTypeR R) R).

Definition upper_moment (k : nat) (w : R) : R :=
  \int[mu]_x (Num.max ((x : R) - w) 0 ^+ k).

Definition upper_energy (c w : R) : R :=
  upper_moment 2 w + c * upper_moment 1 w ^+ 2.

Definition upper_cutoff (c z : R) : R :=
  sup [set w : R | w + z <= c * upper_moment 1 w].

Definition upper_value (c z : R) : R := upper_energy c (upper_cutoff c z).

Definition upper_admissible : set (measurableTypeR R -> R) :=
  [set f : measurableTypeR R -> R |
    [/\ measurable_fun [set: measurableTypeR R] f, (forall x, 0 <= f x),
    mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => f x ^+ 2)) &
    0 < \int[mu]_x f x]].

Definition upper_ratio (c z : R) (f : measurableTypeR R -> R) : R :=
  Num.max (\int[mu]_x (((x : R) + z) * f x)) 0 ^+ 2 /
  (\int[mu]_x (f x ^+ 2) + c * (\int[mu]_x f x) ^+ 2).

End upper_moments.

Section upper_moment_theory.
Context {R : realType} (mu : probability (measurableTypeR R) R).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).

Local Notation m := (upper_moment mu 1).
Local Notation s := (upper_moment mu 2).
Local Notation integrable f :=
  (mu.-integrable [set: measurableTypeR R] (EFin \o f)).

Let mx : measurable_fun [set: measurableTypeR R] (fun x => x : R).
Proof. exact: measurable_id. Qed.

Lemma Rintegral_prob_cst (r : R) : \int[mu]_x r = r.
Proof.
by rewrite Rintegral_cst// -[X in fine X]/(mu setT) probability_setT /= mulr1.
Qed.

Local Lemma integrableZl_R (k : R) (f : measurableTypeR R -> R) :
  integrable f -> integrable (fun x => k * f x).
Proof.
move=> fi; have := integrableZl measurableT k fi.
by apply: eq_integrable => // x _; rewrite /= EFinM.
Qed.

Local Lemma integrableD_R (f g : measurableTypeR R -> R) :
  integrable f -> integrable g -> integrable (fun x => f x + g x).
Proof.
move=> fi gi; have := integrableD measurableT fi gi.
by apply: eq_integrable => // x _; rewrite /= EFinD.
Qed.

Local Lemma integrableB_R (f g : measurableTypeR R -> R) :
  integrable f -> integrable g -> integrable (fun x => f x - g x).
Proof.
move=> fi gi; have := integrableB measurableT fi gi.
by apply: eq_integrable => // x _; rewrite /= EFinB.
Qed.

Local Lemma integrable_norm_R (f : measurableTypeR R -> R) :
  integrable f -> integrable (fun x => `|f x|).
Proof.
move=> fi; have := integrable_abse fi.
by apply: eq_integrable => // x _; rewrite /= abse_EFin.
Qed.

Local Lemma integrable_cst_R (r : R) : integrable (fun _ => r).
Proof. exact: finite_measure_integrable_cst. Qed.

Lemma integrable_quad_bound (f : measurableTypeR R -> R) (a b : R) :
  measurable_fun [set: measurableTypeR R] f ->
  (forall x, `|f x| <= a + b * (x : R) ^+ 2) -> integrable f.
Proof.
move=> mf fb.
have ib : integrable (fun x => a + b * (x : R) ^+ 2).
  by apply: integrableD_R; [exact: integrable_cst_R|exact: integrableZl_R].
apply: (le_integrable measurableT _ _ ib); first exact/measurable_EFinP.
move=> x _; rewrite /comp !abse_EFin lee_fin.
exact: le_trans (fb x) (ler_norm _).
Qed.

Lemma measurable_upper_pow (w : R) k :
  measurable_fun [set: measurableTypeR R]
    (fun x => Num.max ((x : R) - w) 0 ^+ k).
Proof.
apply: measurable_funX; apply: measurable_maxr => //.
by apply: measurable_funB => //; exact: measurable_cst.
Qed.

Lemma integrable_upper_pow (w : R) k : (k <= 2)%N ->
  integrable (fun x => Num.max ((x : R) - w) 0 ^+ k).
Proof.
move=> k2; apply: (integrable_quad_bound (a := 1 + 2 * w ^+ 2) (b := 2)).
  exact: measurable_upper_pow.
move=> x; case: (leP ((x : R) - w) 0) => xw.
  rewrite ger0_norm ?exprn_ge0//.
  by case: k k2 => [_|[_|[_|//]]]; rewrite ?expr0 ?expr1 ?expr0n/=; nra.
rewrite ger0_norm; first by rewrite exprn_ge0// ltW.
case: k k2 => [_|[_|[_|//]]]; rewrite ?expr0 ?expr1.
- by nra.
- have h1 := sqr_ge0 (2 * (x : R) - 1); have h2 := sqr_ge0 (2 * w + 1).
  by nra.
- by have h1 := sqr_ge0 ((x : R) + w); nra.
Qed.

Lemma integrable_idR : integrable (fun x => x : R).
Proof.
apply: (integrable_quad_bound (a := 1) (b := 1)) => // x.
rewrite mul1r -[(x : R) ^+ 2]real_normK ?num_real//.
by have := normr_ge0 (x : R); nra.
Qed.

Lemma upper_moment_ge0 k w : 0 <= upper_moment mu k w.
Proof.
by apply: Rintegral_ge0 => x _; rewrite exprn_ge0// le_max lexx orbT.
Qed.

(* Pointwise facts about the positive part. *)

Lemma upper_part_diff (x w1 w2 : R) : w1 <= w2 ->
  0 <= Num.max (x - w1) 0 - Num.max (x - w2) 0 <= w2 - w1.
Proof.
move=> w12; case: (leP (x - w1) 0) => h1; case: (leP (x - w2) 0) => h2;
  apply/andP; split; lra.
Qed.

Lemma upper_part_sqr_taylor (x w h : R) :
  `|Num.max (x - (w + h)) 0 ^+ 2 - Num.max (x - w) 0 ^+ 2
    + 2 * h * Num.max (x - w) 0| <= h ^+ 2.
Proof.
case: (leP (x - w) 0) => h1; case: (leP (x - (w + h)) 0) => h2.
- by rewrite expr0n/= !subr0 mulr0 addr0 normr0 sqr_ge0.
- rewrite expr0n/= subr0 mulr0 addr0 ger0_norm ?sqr_ge0//; nra.
- rewrite expr0n/= sub0r.
  have -> : - (x - w) ^+ 2 + 2 * h * (x - w) = (x - w) * (2 * h - (x - w)).
    by ring.
  rewrite ger0_norm; first by apply: mulr_ge0; lra.
  by have := sqr_ge0 (h - (x - w)); nra.
- have -> : (x - (w + h)) ^+ 2 - (x - w) ^+ 2 + 2 * h * (x - w) = h ^+ 2.
    by ring.
  by rewrite ger0_norm ?sqr_ge0.
Qed.

(* Regularity of m and s. *)

Lemma upper_moment1_lipschitz w1 w2 : w1 <= w2 ->
  0 <= m w1 - m w2 <= w2 - w1.
Proof.
move=> w12; have i1 v := @integrable_upper_pow v 1 isT.
rewrite /upper_moment -RintegralB//; apply/andP; split.
  apply: Rintegral_ge0 => x _; rewrite !expr1.
  by case/andP: (upper_part_diff x w12).
rewrite -[X in _ <= X]Rintegral_prob_cst; apply: le_Rintegral => //.
- exact: integrableB_R.
- exact: integrable_cst_R.
- by move=> x _; rewrite !expr1; case/andP: (upper_part_diff x w12).
Qed.

Lemma upper_moment1_ge w : \int[mu]_x (x : R) - w <= m w.
Proof.
rewrite -[X in _ - X <= _]Rintegral_prob_cst -RintegralB//.
- exact: integrable_idR.
- exact: integrable_cst_R.
apply: le_Rintegral => //.
- by apply: integrableB_R; [exact: integrable_idR|exact: integrable_cst_R].
- exact: integrable_upper_pow.
- by move=> x _; rewrite expr1 le_max lexx.
Qed.

Lemma upper_moment1_le w : 0 < w ->
  m w <= \int[mu]_x ((x : R) ^+ 2) / (4 * w).
Proof.
move=> w0; rewrite -RintegralZr//; apply: le_Rintegral => //.
- exact: integrable_upper_pow.
- have := integrableZl_R (4 * w)^-1 mu2.
  by apply: eq_integrable => // x _; rewrite /= mulrC.
move=> x _; rewrite expr1; case: (leP ((x : R) - w) 0) => xw.
  by rewrite mulr_ge0 ?sqr_ge0// invr_ge0 mulr_ge0// ltW.
rewrite ler_pdivlMr ?mulr_gt0//.
by have := sqr_ge0 ((x : R) - 2 * w); nra.
Qed.

Lemma upper_moment1_gt0 (w b : R) : w < b ->
  (0 < mu `]b, +oo[%classic)%E -> 0 < m w.
Proof.
move=> wb Pb; pose A := `]b, +oo[%classic : set (measurableTypeR R).
have mA : measurable A by exact: measurable_itv.
have iA : integrable (fun x => \1_A x : R) by exact: integrable_indic.
have EA : \int[mu]_x (\1_A x : R) = fine (mu A).
  by rewrite /Rintegral integral_indic// setIT.
have muA : 0 < fine (mu A).
  apply: fine_gt0; rewrite Pb/=.
  exact: le_lt_trans (probability_le1 mu mA) (ltry 1).
apply: (@lt_le_trans _ _ ((b - w) * fine (mu A))).
  by rewrite mulr_gt0// subr_gt0.
rewrite -EA -RintegralZl//; apply: le_Rintegral => //.
- exact: integrableZl_R.
- exact: integrable_upper_pow.
move=> x _; rewrite expr1 indicE; case: (boolP (x \in A)) => xA.
  rewrite mulr1 le_max lerD2r; apply/orP; left; apply: ltW.
  by move: xA; rewrite inE /A /= in_itv /= andbT.
by rewrite mulr0 le_max lexx orbT.
Qed.

Lemma upper_moment2_taylor w h :
  `|s (w + h) - s w + 2 * h * m w| <= h ^+ 2.
Proof.
have i2 v := @integrable_upper_pow v 2 isT.
have i1 : integrable (fun x => 2 * h * Num.max ((x : R) - w) 0 ^+ 1).
  by apply: integrableZl_R; exact: integrable_upper_pow.
rewrite /upper_moment -RintegralB//.
rewrite -RintegralZl//; first exact: integrable_upper_pow.
rewrite -RintegralD//; first exact: integrableB_R.
have iD : integrable (fun x => Num.max ((x : R) - (w + h)) 0 ^+ 2
    - Num.max ((x : R) - w) 0 ^+ 2 + 2 * h * Num.max ((x : R) - w) 0 ^+ 1).
  by apply: integrableD_R => //; exact: integrableB_R.
rewrite -[X in _ <= X]Rintegral_prob_cst.
apply: le_trans (le_normr_Rintegral _ iD) _ => //.
apply: le_Rintegral => //.
- exact: integrable_norm_R.
- exact: integrable_cst_R.
- by move=> x _; rewrite expr1; exact: upper_part_sqr_taylor.
Qed.

(* The cutoff: the solution of w + z = c m(w). *)

Lemma upper_cutoff_growth c w1 w2 : -1 < c -> w1 <= w2 ->
  Num.min 1 (1 + c) * (w2 - w1) <= (w2 - c * m w2) - (w1 - c * m w1).
Proof.
move=> c1 w12; have /andP[D0 D1] := upper_moment1_lipschitz w12.
have h1 : Num.min 1 (1 + c) <= 1 by rewrite ge_min lexx.
have h2 : Num.min 1 (1 + c) <= 1 + c by rewrite ge_min lexx orbT.
have d0 : 0 <= w2 - w1 by rewrite subr_ge0.
have -> : w2 - c * m w2 - (w1 - c * m w1) = (w2 - w1) + c * (m w1 - m w2).
  by ring.
case: (leP 0 c) => c0; nra.
Qed.

Lemma upper_cutoff_lipschitz c w1 w2 : w1 <= w2 ->
  (w2 - c * m w2) - (w1 - c * m w1) <= (1 + `|c|) * (w2 - w1).
Proof.
move=> w12; have /andP[D0 D1] := upper_moment1_lipschitz w12.
have -> : w2 - c * m w2 - (w1 - c * m w1) = (w2 - w1) + c * (m w1 - m w2).
  by ring.
have : c * (m w1 - m w2) <= `|c| * (w2 - w1).
  apply: le_trans (ler_norm _) _; rewrite normrM [`|m w1 - _|]ger0_norm//.
  by rewrite ler_wpM2l.
lra.
Qed.

Section cutoff.
Variables (c z : R).
Hypothesis c1 : -1 < c.

Local Notation H w := (w + z - c * m w).
Local Notation A := [set w : R | w + z <= c * m w].
Local Notation delta := (Num.min 1 (1 + c)).
Local Notation L := (1 + `|c|).

Let delta0 : 0 < delta.
Proof. by rewrite lt_min ltr01 /= addrC -ltrBlDr sub0r. Qed.

Let L0 : 0 < L.
Proof. by rewrite ltr_pwDl. Qed.

Let H_growth w1 w2 : w1 <= w2 -> delta * (w2 - w1) <= H w2 - H w1.
Proof.
by move=> w12; have := upper_cutoff_growth c1 w12; lra.
Qed.

Let H_lip w1 w2 : w1 <= w2 -> H w2 - H w1 <= L * (w2 - w1).
Proof.
by move=> w12; have := upper_cutoff_lipschitz c w12; lra.
Qed.

Let AE w : A w <-> H w <= 0.
Proof. by rewrite /= subr_le0. Qed.

Let A0 : A !=set0.
Proof.
exists (- `|H 0| / delta); apply/AE.
have d0 := delta0.
have v0 : - `|H 0| / delta <= 0.
  by rewrite mulNr oppr_le0 divr_ge0 ?normr_ge0// ltW.
have := H_growth v0.
rewrite sub0r mulNr opprK mulrCA divff ?gt_eqF// mulr1.
by have := ler_norm (H 0); lra.
Qed.

Let Aub : ubound A (`|H 0| / delta).
Proof.
have d0 := delta0.
move=> v /AE Hv; case: (leP v 0) => v0.
  by apply: le_trans v0 _; rewrite divr_ge0 ?normr_ge0// ltW.
have := H_growth (ltW v0); rewrite subr0 => h.
rewrite ler_pdivlMr// mulrC.
by have := ler_norm (- H 0); rewrite normrN; move: h Hv; lra.
Qed.

Let hasA : has_sup A.
Proof. by split; [exact: A0|exists (`|H 0| / delta); exact: Aub]. Qed.

Let H_sup : H (sup A) = 0.
Proof.
have d0 := delta0; have l0 := L0.
set w := sup A; have wA : ubound A w := ub_le_sup hasA.2.
apply/eqP; rewrite eq_le; apply/andP; split; rewrite leNgt; apply/negP => Hw.
- have ub : ubound A (w - H w / L).
    move=> v /[dup] Av /AE Hv; rewrite leNgt; apply/negP => vw.
    have vw' : v <= w := wA v Av.
    have := H_lip vw'.
    have : L * (w - v) < H w.
      by rewrite -ltr_pdivlMl// mulrC ltrBlDr -ltrBlDl.
    lra.
  have := ge_sup A0 ub; rewrite -/w.
  have : 0 < H w / L by rewrite divr_gt0.
  lra.
- have wv : w <= w - H w / L.
    by rewrite lerDl oppr_ge0 pmulr_lle0 ?invr_gt0// ltW.
  have vA : A (w - H w / L).
    apply/AE; have := H_lip wv.
    have -> : w - H w / L - w = - (H w / L) by ring.
    by rewrite mulrN mulrCA divff ?gt_eqF// mulr1; lra.
  have := wA _ vA.
  have : 0 < - H w / L by rewrite divr_gt0// oppr_gt0.
  by rewrite mulNr; lra.
Qed.

Lemma upper_cutoffE : upper_cutoff mu c z + z = c * m (upper_cutoff mu c z).
Proof. by have := H_sup; rewrite -/(upper_cutoff mu c z); lra. Qed.

Lemma upper_cutoff_le w : w + z <= c * m w <-> w <= upper_cutoff mu c z.
Proof.
have d0 := delta0.
split => [Aw|wc]; first exact: (ub_le_sup hasA.2).
apply/AE; have := H_sup; rewrite -/(upper_cutoff mu c z) => Hc.
have := H_growth wc; have : 0 <= delta * (upper_cutoff mu c z - w).
  by rewrite mulr_ge0 ?subr_ge0// ltW.
lra.
Qed.

Lemma upper_cutoff_unique w : w + z = c * m w -> w = upper_cutoff mu c z.
Proof.
have d0 := delta0.
move=> e; have wc : w <= upper_cutoff mu c z.
  by apply/upper_cutoff_le; rewrite e.
apply/eqP; rewrite eq_le wc /= leNgt; apply/negP => cw.
have := H_growth (ltW cw); have := H_sup; rewrite -/(upper_cutoff mu c z) => ->.
have : 0 < delta * (upper_cutoff mu c z - w) by rewrite mulr_gt0// subr_gt0.
by move: e; lra.
Qed.

End cutoff.

(* Squares, products and Jensen's inequality. *)

Lemma integrable_of_sqr (f : measurableTypeR R -> R) :
  measurable_fun [set: measurableTypeR R] f ->
  integrable (fun x => f x ^+ 2) -> integrable f.
Proof.
move=> mf f2i.
have i1 : integrable (fun x => 1 + f x ^+ 2).
  by apply: integrableD_R => //; exact: integrable_cst_R.
apply: (le_integrable measurableT _ _ i1); first exact/measurable_EFinP.
move=> x _; rewrite /comp !abse_EFin lee_fin [`|1 + _|]ger0_norm.
  by rewrite addr_ge0// sqr_ge0.
by rewrite -[f x ^+ 2]real_normK ?num_real//; have := normr_ge0 (f x); nra.
Qed.

Lemma integrable_mul_sqr (f g : measurableTypeR R -> R) :
  measurable_fun [set: measurableTypeR R] f ->
  measurable_fun [set: measurableTypeR R] g ->
  integrable (fun x => f x ^+ 2) -> integrable (fun x => g x ^+ 2) ->
  integrable (fun x => f x * g x).
Proof.
move=> mf mg f2i g2i.
have i1 : integrable (fun x => f x ^+ 2 + g x ^+ 2) by exact: integrableD_R.
apply: (le_integrable measurableT _ _ i1).
  by apply/measurable_EFinP; exact: measurable_funM.
move=> x _; rewrite /comp !abse_EFin lee_fin [`|_ + _|]ger0_norm.
  by rewrite addr_ge0// sqr_ge0.
rewrite normrM -[f x ^+ 2]real_normK ?num_real//.
rewrite -[g x ^+ 2]real_normK ?num_real//.
by have := sqr_ge0 (`|f x| - `|g x|); nra.
Qed.

Lemma Rintegral_sqr_le (g : measurableTypeR R -> R) :
  integrable g -> integrable (fun x => g x ^+ 2) ->
  (\int[mu]_x g x) ^+ 2 <= \int[mu]_x (g x ^+ 2).
Proof.
move=> gi g2i; set a := \int[mu]_x g x.
have i1 : integrable (fun x => 2 * a * g x) := integrableZl_R _ gi.
have : 0 <= \int[mu]_x ((g x - a) ^+ 2).
  by apply: Rintegral_ge0 => x _; exact: sqr_ge0.
have -> : (fun x => (g x - a) ^+ 2) =
    (fun x => (g x ^+ 2 - 2 * a * g x) + a ^+ 2).
  by apply/funext => x; ring.
rewrite RintegralD//.
- exact: integrableB_R.
- exact: integrable_cst_R.
rewrite RintegralB// RintegralZl// Rintegral_prob_cst -/a.
by lra.
Qed.

(* The energy s + c m^2 decreases. *)

Lemma upper_part_sqr_diff (x w1 w2 : R) : w1 <= w2 ->
  Num.max (x - w1) 0 ^+ 2 - Num.max (x - w2) 0 ^+ 2 =
  2 * (w2 - w1) * Num.max (x - w2) 0
  + (Num.max (x - w1) 0 - Num.max (x - w2) 0) ^+ 2.
Proof.
move=> w12; case: (leP (x - w1) 0) => h1; case: (leP (x - w2) 0) => h2.
- by ring.
- by exfalso; lra.
- by ring.
- by ring.
Qed.

Lemma upper_energy_decr c w1 w2 : -1 < c -> w1 <= w2 ->
  2 * Num.min 1 (1 + c) * m w2 * (w2 - w1) <=
  upper_energy mu c w1 - upper_energy mu c w2.
Proof.
move=> c1 w12.
pose g x := Num.max ((x : R) - w1) 0 ^+ 1 - Num.max ((x : R) - w2) 0 ^+ 1.
have i1 v := @integrable_upper_pow v 1 isT.
have i2 v := @integrable_upper_pow v 2 isT.
have gi : integrable g by exact: integrableB_R.
have gb x : 0 <= g x <= w2 - w1.
  by rewrite /g !expr1; exact: upper_part_diff.
have g2i : integrable (fun x => g x ^+ 2).
  apply: (integrable_quad_bound (a := (w2 - w1) ^+ 2) (b := 0)).
    apply: measurable_funX; apply: measurable_funB;
    exact: measurable_upper_pow.
  move=> x; rewrite mul0r addr0 ger0_norm ?sqr_ge0//.
  by have /andP[g0 g1] := gb x; rewrite ler_pXn2r// ?nnegrE// (le_trans g0).
have p2i : integrable (fun x => 2 * (w2 - w1) * Num.max ((x : R) - w2) 0 ^+ 1).
  exact: integrableZl_R.
have es : upper_moment mu 2 w1 - upper_moment mu 2 w2 =
    2 * (w2 - w1) * m w2 + \int[mu]_x (g x ^+ 2).
  rewrite /upper_moment -RintegralB// -RintegralZl// -RintegralD//.
  apply: eq_Rintegral => x _; rewrite /g !expr1.
  exact: upper_part_sqr_diff.
have em : m w1 - m w2 = \int[mu]_x g x by rewrite /upper_moment -RintegralB.
have hJ := Rintegral_sqr_le gi g2i; rewrite -em in hJ.
have hG := upper_cutoff_growth c1 w12.
have /andP[D0 D1] := upper_moment1_lipschitz w12.
have m0 : 0 <= m w2 := upper_moment_ge0 1 w2.
have d1 : Num.min 1 (1 + c) <= 1 by rewrite ge_min lexx.
have d2 : Num.min 1 (1 + c) <= 1 + c by rewrite ge_min lexx orbT.
rewrite /upper_energy.
set D := m w1 - m w2 in em hJ D0 D1.
have -> : upper_moment mu 2 w1 + c * m w1 ^+ 2 -
    (upper_moment mu 2 w2 + c * m w2 ^+ 2) =
    (upper_moment mu 2 w1 - upper_moment mu 2 w2) + c * D * (D + 2 * m w2).
  by rewrite /D; ring.
rewrite es.
have hD : 0 <= \int[mu]_x (g x ^+ 2) + c * D ^+ 2.
  case: (leP 0 c) => c0.
    by apply: addr_ge0; [exact: (le_trans (sqr_ge0 _) hJ)|
      exact: (mulr_ge0 c0 (sqr_ge0 _))].
  by have := sqr_ge0 D; nra.
have hm : 0 <= m w2 * ((w2 - w1) + c * D - Num.min 1 (1 + c) * (w2 - w1)).
  apply: mulr_ge0 => //; rewrite subr_ge0.
  by move: hG; rewrite /D; have -> : w2 - c * m w2 - (w1 - c * m w1) =
    w2 - w1 + c * (m w1 - m w2) by ring.
by nra.
Qed.

(* Cauchy-Schwarz through the discriminant. *)

Lemma discriminant_le (a b k : R) : 0 <= k ->
  (forall t, 0 <= a + 2 * b * t + k * t ^+ 2) -> b ^+ 2 <= a * k.
Proof.
move=> k0 h; case: (ltP 0 k) => kpos.
  have := h (- b / k); have kn0 : k != 0 by rewrite gt_eqF.
  have -> : a + 2 * b * (- b / k) + k * (- b / k) ^+ 2 = (a * k - b ^+ 2) / k.
    by field.
  by move=> hh; have := mulr_ge0 hh k0; rewrite divfK//; lra.
have k00 : k = 0 by apply/eqP; rewrite eq_le kpos k0.
rewrite k00 mulr0; case: (eqVneq b 0) => [->|b0]; first by rewrite expr0n.
exfalso; have := h (- (a + 1) / (2 * b)); rewrite k00 mul0r addr0.
have -> : a + 2 * b * (- (a + 1) / (2 * b)) = -1.
  by field; rewrite pnatr_eq0.
by rewrite oppr_ge0 ler10.
Qed.

Lemma upper_form_ge0 c (f : measurableTypeR R -> R) : -1 < c ->
  integrable f -> integrable (fun x => f x ^+ 2) ->
  0 <= \int[mu]_x (f x ^+ 2) + c * (\int[mu]_x f x) ^+ 2.
Proof.
move=> c1 fi f2i; have hJ := Rintegral_sqr_le fi f2i.
have := sqr_ge0 (\int[mu]_x f x); case: (leP 0 c) => c0; first by nra.
by move: c1; nra.
Qed.

Lemma upper_moment2_eq0 w : m w = 0 -> s w = 0.
Proof.
move=> m0; have mp := measurable_upper_pow w 1.
have i1 := @integrable_upper_pow w 1 isT.
have h1 : (\int[mu]_x `|(Num.max ((x : R) - w) 0 ^+ 1)%:E| = 0)%E.
  have <- : (m w)%:E = 0%E by rewrite m0.
  rewrite /upper_moment /Rintegral fineK; first exact: integrable_fin_num i1.
  apply: eq_integral => x _; rewrite abse_EFin ger0_norm// expr1 le_max lexx.
  by rewrite orbT.
have mpE : measurable_fun [set: measurableTypeR R]
    (fun x => (Num.max ((x : R) - w) 0 ^+ 1)%:E) by exact/measurable_EFinP.
have ae0 := (ae_eq_integral_abs mu measurableT mpE).1 h1.
rewrite /upper_moment /Rintegral.
have -> : (\int[mu]_x (Num.max ((x : R) - w) 0 ^+ 2)%:E =
    \int[mu]_x (cst 0 x))%E.
  apply: ae_eq_integral => //.
  - by apply/measurable_EFinP; exact: measurable_upper_pow.
  - apply: filterS ae0 => x /[apply] /= /eqP; rewrite eqe expr1 => /eqP ->.
    by rewrite expr0n.
by rewrite integral0.
Qed.

Section variational.
Variables (c z : R).
Hypothesis c1 : -1 < c.

Local Notation w := (upper_cutoff mu c z).
Let p (x : measurableTypeR R) := Num.max ((x : R) - w) 0.

Let p_ge0 x : 0 <= p x.
Proof. by rewrite /p le_max lexx orbT. Qed.

Let mp : measurable_fun [set: measurableTypeR R] p.
Proof.
apply: measurable_maxr => //.
by apply: measurable_funB => //; exact: measurable_cst.
Qed.

Let p2i : integrable (fun x => p x ^+ 2).
Proof. exact: (@integrable_upper_pow w 2 isT). Qed.

Let pi : integrable p.
Proof. exact: integrable_of_sqr. Qed.

Let Ep : \int[mu]_x p x = m w.
Proof. by apply: eq_Rintegral => x _; rewrite expr1. Qed.

Let Ep2 : \int[mu]_x (p x ^+ 2) = s w.
Proof. by []. Qed.

Lemma upper_value_ge0 : 0 <= upper_value mu c z.
Proof.
by have := upper_form_ge0 c1 pi p2i; rewrite Ep Ep2.
Qed.

Lemma upper_variational_attained :
  \int[mu]_x (((x : R) + z) * p x) = upper_value mu c z.
Proof.
have -> : (fun x => ((x : R) + z) * p x) =
    (fun x => p x ^+ 2 + (w + z) * p x).
  apply/funext => x; rewrite /p; case: (leP ((x : R) - w) 0) => xw.
    by rewrite !mulr0 expr0n /= add0r.
  by ring.
rewrite RintegralD//; first exact: integrableZl_R.
rewrite RintegralZl// Ep Ep2 upper_cutoffE//.
by rewrite /upper_value /upper_energy; ring.
Qed.

Lemma upper_variational_le (f : measurableTypeR R -> R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, 0 <= f x) ->
  integrable (fun x => f x ^+ 2) ->
  Num.max (\int[mu]_x (((x : R) + z) * f x)) 0 ^+ 2 <=
  upper_value mu c z * (\int[mu]_x (f x ^+ 2) + c * (\int[mu]_x f x) ^+ 2).
Proof.
move=> mf f0 f2i; have fi := integrable_of_sqr mf f2i.
have pfi : integrable (fun x => p x * f x) := integrable_mul_sqr mp mf p2i f2i.
have xfi : integrable (fun x => (x : R) * f x).
  exact: (integrable_mul_sqr mx mf mu2 f2i).
have xzfi : integrable (fun x => ((x : R) + z) * f x).
  have := integrableD_R xfi (integrableZl_R z fi).
  by apply: eq_integrable => // x _; rewrite /= mulrDl.
set N := \int[mu]_x (((x : R) + z) * f x).
set Q := \int[mu]_x (p x * f x) + c * m w * \int[mu]_x f x.
have hN : N <= Q.
  rewrite /Q -RintegralZl//; rewrite -RintegralD//; first exact: integrableZl_R.
  apply: le_Rintegral => //.
    by apply: integrableD_R => //; exact: integrableZl_R.
  move=> x _; have e := @upper_cutoffE c z c1; rewrite -/w in e.
  have hx : (x : R) + z <= p x + c * m w.
    by rewrite /p; case: (leP ((x : R) - w) 0) => xw; lra.
  by have := f0 x; nra.
have hQ : Q ^+ 2 <= upper_value mu c z *
    (\int[mu]_x (f x ^+ 2) + c * (\int[mu]_x f x) ^+ 2).
  apply: discriminant_le; first exact: upper_form_ge0.
  move=> t; pose u x := p x + t * f x.
  have tfi : integrable (fun x => t * f x) := integrableZl_R t fi.
  have ui : integrable u by exact: integrableD_R.
  have u2i : integrable (fun x => u x ^+ 2).
    have := integrableD_R (integrableD_R p2i (integrableZl_R (2 * t) pfi))
      (integrableZl_R (t ^+ 2) f2i).
    by apply: eq_integrable => // x _; rewrite /= /u; congr EFin; ring.
  have Eu : \int[mu]_x u x = m w + t * \int[mu]_x f x.
    by rewrite RintegralD// RintegralZl// Ep.
  have Eu2 : \int[mu]_x (u x ^+ 2) =
      s w + 2 * t * \int[mu]_x (p x * f x) + t ^+ 2 * \int[mu]_x (f x ^+ 2).
    have -> : (fun x => u x ^+ 2) =
        (fun x => (p x ^+ 2 + 2 * t * (p x * f x)) + t ^+ 2 * f x ^+ 2).
      by apply/funext => x; rewrite /u; ring.
    rewrite RintegralD//.
    - exact: integrableD_R (integrableZl_R _ pfi).
    - exact: integrableZl_R.
    rewrite RintegralD//; first exact: integrableZl_R.
    by rewrite !RintegralZl// Ep2.
  have := upper_form_ge0 c1 ui u2i; rewrite Eu Eu2.
  rewrite /upper_value /upper_energy -/w /Q.
  set F2 := \int[mu]_x (f x ^+ 2); set F1 := \int[mu]_x f x.
  set PF := \int[mu]_x (p x * f x).
  have -> : s w + 2 * t * PF + t ^+ 2 * F2 + c * (m w + t * F1) ^+ 2 =
      s w + c * m w ^+ 2 + 2 * (PF + c * m w * F1) * t
      + (F2 + c * F1 ^+ 2) * t ^+ 2.
    by ring.
  done.
have V0 := upper_value_ge0; have F0 := upper_form_ge0 c1 fi f2i.
case: (leP N 0) => N0; first by rewrite expr0n /= mulr_ge0.
by apply: le_trans hQ; rewrite ler_pXn2r// ?nnegrE ltW// (lt_le_trans N0 hN).
Qed.

Lemma upper_moment1_cutoff_gt0 : 0 < upper_value mu c z -> 0 < m w.
Proof.
move=> V0; rewrite lt_neqAle upper_moment_ge0 andbT eq_sym.
apply/negP => /eqP m0; move: V0.
by rewrite /upper_value /upper_energy -/w m0 upper_moment2_eq0// expr0n mulr0
  addr0 ltxx.
Qed.

Lemma upper_ratio_le f : upper_admissible mu f ->
  upper_ratio mu c z f <= upper_value mu c z.
Proof.
case=> mf f0 f2i fpos; have fi := integrable_of_sqr mf f2i.
have Q0 : 0 < \int[mu]_x (f x ^+ 2) + c * (\int[mu]_x f x) ^+ 2.
  have hJ := Rintegral_sqr_le fi f2i.
  have h2 : 0 < (\int[mu]_x f x) ^+ 2 by rewrite exprn_gt0.
  by have := c1; case: (leP 0 c) => c0; nra.
by rewrite /upper_ratio ler_pdivrMr//; exact: upper_variational_le.
Qed.

Lemma upper_ratio_ge0 f : upper_admissible mu f -> 0 <= upper_ratio mu c z f.
Proof.
case=> mf f0 f2i fpos; have fi := integrable_of_sqr mf f2i.
apply: divr_ge0; first exact: sqr_ge0.
exact: upper_form_ge0.
Qed.

Lemma upper_admissible_cst : upper_admissible mu (fun _ => 1).
Proof.
split => //.
- exact: integrable_cst_R.
- by rewrite Rintegral_prob_cst ltr01.
Qed.

Lemma upper_admissible_cutoff : 0 < upper_value mu c z -> upper_admissible mu p.
Proof.
move=> V0; split => //; rewrite Ep; exact: upper_moment1_cutoff_gt0.
Qed.

Lemma upper_ratio_cutoff : 0 < upper_value mu c z ->
  upper_ratio mu c z p = upper_value mu c z.
Proof.
move=> V0; rewrite /upper_ratio upper_variational_attained.
have -> : \int[mu]_x (p x ^+ 2) + c * (\int[mu]_x p x) ^+ 2 =
    upper_value mu c z.
  by rewrite Ep Ep2.
by rewrite max_l ?ltW// expr2 mulfK// gt_eqF.
Qed.

Lemma upper_variational :
  sup [set upper_ratio mu c z f | f in upper_admissible mu] =
  upper_value mu c z.
Proof.
set S := [set upper_ratio mu c z f | f in upper_admissible mu].
have S0 : S !=set0 by exists (upper_ratio mu c z (fun _ => 1)), (fun _ => 1);
  [exact: upper_admissible_cst|].
have Sub : ubound S (upper_value mu c z).
  by move=> _ [f fA <-]; exact: upper_ratio_le.
have hS : has_sup S by split => //; exists (upper_value mu c z).
apply/eqP; rewrite eq_le ge_sup//=.
have [->|Vn0] := eqVneq (upper_value mu c z) 0.
  apply: le_trans (upper_ratio_ge0 upper_admissible_cst) _.
  apply: (ub_le_sup hS.2); exists (fun _ => 1) => //.
  exact: upper_admissible_cst.
have V0 : 0 < upper_value mu c z.
  by rewrite lt_neqAle eq_sym Vn0 upper_value_ge0.
rewrite -[X in X <= _]upper_ratio_cutoff//; apply: (ub_le_sup hS.2).
by exists p => //; exact: upper_admissible_cutoff.
Qed.

Lemma upper_ratio_nondecr z' f : z <= z' -> upper_admissible mu f ->
  upper_ratio mu c z f <= upper_ratio mu c z' f.
Proof.
move=> zz [mf f0 f2i fpos]; have fi := integrable_of_sqr mf f2i.
have xfi : integrable (fun x => (x : R) * f x).
  exact: (integrable_mul_sqr mx mf mu2 f2i).
have xzfi v : integrable (fun x => ((x : R) + v) * f x).
  have := integrableD_R xfi (integrableZl_R v fi).
  by apply: eq_integrable => // x _; rewrite /= mulrDl.
rewrite /upper_ratio ler_pM2r.
  rewrite invr_gt0; have hJ := Rintegral_sqr_le fi f2i.
  have h2 : 0 < (\int[mu]_x f x) ^+ 2 by rewrite exprn_gt0.
  by have := c1; case: (leP 0 c) => c0; nra.
have hN : \int[mu]_x (((x : R) + z) * f x) <= \int[mu]_x (((x : R) + z') * f x).
  apply: le_Rintegral => // x _; apply: ler_wpM2r => //.
  by rewrite lerD2l.
set N := \int[mu]_x (((x : R) + z) * f x) in hN *.
set N' := \int[mu]_x (((x : R) + z') * f x) in hN *.
have h1 : 0 <= Num.max N 0 by rewrite le_max lexx orbT.
have h2 : Num.max N 0 <= Num.max N' 0.
  by rewrite ge_max !le_max hN lexx /= !orbT.
by rewrite ler_pXn2r// ?nnegrE// (le_trans h1 h2).
Qed.

End variational.

Lemma upper_value_nondecr c z z' : -1 < c -> z <= z' ->
  upper_value mu c z <= upper_value mu c z'.
Proof.
move=> c1 zz; rewrite -(upper_variational z c1) -(upper_variational z' c1).
have Sub' : ubound [set upper_ratio mu c z' f | f in upper_admissible mu]
    (upper_value mu c z').
  by move=> _ [f fA <-]; exact: (upper_ratio_le z' c1).
apply: ge_sup.
  by exists (upper_ratio mu c z (fun _ => 1)), (fun _ => 1);
    [exact: upper_admissible_cst|].
move=> _ [f fA <-]; apply: le_trans (upper_ratio_nondecr c1 zz fA) _.
by apply: (ub_le_sup (ex_intro _ _ Sub')); exists f.
Qed.

Lemma upper_value_incr c z z' : -1 < c -> z < z' -> 0 < upper_value mu c z ->
  upper_value mu c z < upper_value mu c z'.
Proof.
move=> c1 zz V0.
pose w := upper_cutoff mu c z.
pose p (x : measurableTypeR R) := Num.max ((x : R) - w) 0.
have pA : upper_admissible mu p := upper_admissible_cutoff V0.
have m0 : 0 < m w := upper_moment1_cutoff_gt0 V0.
case: pA => mp p0 p2i ppos; have pi := integrable_of_sqr mp p2i.
have xpi : integrable (fun x => (x : R) * p x).
  exact: (integrable_mul_sqr mx mp mu2 p2i).
have Ep : \int[mu]_x p x = m w by apply: eq_Rintegral => x _; rewrite expr1.
have N' : \int[mu]_x (((x : R) + z') * p x) =
    upper_value mu c z + (z' - z) * m w.
  rewrite -(upper_variational_attained z c1) -Ep -RintegralZl//.
  have xzpi v : integrable (fun x => ((x : R) + v) * p x).
    have := integrableD_R xpi (integrableZl_R v pi).
    by apply: eq_integrable => // x _; rewrite /= mulrDl.
  rewrite -RintegralD//.
  - exact: integrableZl_R.
  - by apply: eq_Rintegral => x _; rewrite /p; ring.
apply: lt_le_trans (upper_ratio_le z' c1 (upper_admissible_cutoff V0)).
rewrite /upper_ratio N' Ep.
have -> : \int[mu]_x (p x ^+ 2) + c * m w ^+ 2 = upper_value mu c z by [].
have d0 : 0 < (z' - z) * m w by rewrite mulr_gt0// subr_gt0.
rewrite max_l; first by rewrite addr_ge0// ltW.
by rewrite ltr_pdivlMr// expr2; nra.
Qed.

Lemma upper_moment2_lipschitz a b : a <= b ->
  0 <= s a - s b <= (b - a) * (m a + m b).
Proof.
move=> ab; have i1 v := @integrable_upper_pow v 1 isT.
have i2 v := @integrable_upper_pow v 2 isT.
rewrite /upper_moment -RintegralB//; apply/andP; split.
  apply: Rintegral_ge0 => x _; rewrite subr_ge0.
  have /andP[h0 _] := upper_part_diff x ab.
  have pb : 0 <= Num.max ((x : R) - b) 0 by rewrite le_max lexx orbT.
  by rewrite ler_pXn2r// ?nnegrE// ?(le_trans pb)// -subr_ge0.
rewrite -RintegralD// -RintegralZl//; first exact: integrableD_R.
apply: le_Rintegral => //.
- exact: integrableB_R.
- by apply: integrableZl_R; exact: integrableD_R.
move=> x _; rewrite !expr1.
have /andP[h0 h1] := upper_part_diff x ab.
have pa : 0 <= Num.max ((x : R) - a) 0 by rewrite le_max lexx orbT.
have pb : 0 <= Num.max ((x : R) - b) 0 by rewrite le_max lexx orbT.
by nra.
Qed.

Lemma upper_energy_lipschitz c a b : a <= b ->
  `|upper_energy mu c a - upper_energy mu c b| <=
  2 * (1 + `|c|) * m a * (b - a).
Proof.
move=> ab; have /andP[S0 S1] := upper_moment2_lipschitz ab.
have /andP[M0 M1] := upper_moment1_lipschitz ab.
have ma0 := upper_moment_ge0 1 a; have mb0 := upper_moment_ge0 1 b.
have d0 : 0 <= b - a by rewrite subr_ge0.
rewrite /upper_energy.
have -> : s a + c * m a ^+ 2 - (s b + c * m b ^+ 2) =
    (s a - s b) + c * ((m a - m b) * (m a + m b)) by ring.
apply: le_trans (ler_normD _ _) _; rewrite normrM [`|s a - _|]ger0_norm//.
rewrite [`|(m a - m b) * _|]ger0_norm.
  exact: mulr_ge0 M0 (addr_ge0 ma0 mb0).
have h1 : (m a - m b) * (m a + m b) <= (b - a) * (2 * m a) by nra.
have h2 : `|c| * ((m a - m b) * (m a + m b)) <= `|c| * ((b - a) * (2 * m a)).
  by rewrite ler_wpM2l.
by have := normr_ge0 c; nra.
Qed.

Lemma upper_energy_continuous c : continuous (upper_energy mu c).
Proof.
move=> x; apply/(cvgrPdist_lt (F := nbhs x)) => e e0.
pose K := 2 * (1 + `|c|) * m (x - 1) + 1.
have mx0 := upper_moment_ge0 1 (x - 1).
have L0 : 0 <= 2 * (1 + `|c|) by rewrite mulr_ge0// addr_ge0.
have K0 : 0 < K by rewrite /K ltr_pwDr// mulr_ge0.
have h1 := @cvgr_dist_lt _ _ _ (nbhs x) (nbhs_filter x) id x cvg_id _ ltr01.
have h2 := @cvgr_dist_lt _ _ _ (nbhs x) (nbhs_filter x) id x cvg_id _
  (divr_gt0 e0 K0).
apply: filterS2 h1 h2 => y /= y1 y2.
have Kd : K * `|x - y| < e by rewrite mulrC -ltr_pdivlMr.
apply: le_lt_trans Kd; have d0 := normr_ge0 (x - y).
have LK : 2 * (1 + `|c|) * m (x - 1) <= K by rewrite /K lerDl.
case: (leP x y) => xy.
  have := upper_energy_lipschitz c xy.
  have x1 : x - 1 <= x by rewrite lerBlDr lerDl.
  have /andP[M0 _] := upper_moment1_lipschitz x1.
  rewrite [`|x - y|]distrC [`|y - x|]ger0_norm ?subr_ge0// => h.
  apply: le_trans h _.
  have h1 : 2 * (1 + `|c|) * m x <= 2 * (1 + `|c|) * m (x - 1).
    by rewrite ler_wpM2l// -subr_ge0.
  by rewrite ler_wpM2r ?subr_ge0// (le_trans h1 LK).
have xy0 : 0 <= x - y by rewrite subr_ge0 ltW.
rewrite [`|x - y|]ger0_norm// in y1 *.
have x1 : x - 1 <= y by rewrite lerBlDr -lerBlDl ltW.
have /andP[M0 _] := upper_moment1_lipschitz x1.
rewrite distrC; apply: le_trans (upper_energy_lipschitz c (ltW xy)) _.
have h1 : 2 * (1 + `|c|) * m y <= 2 * (1 + `|c|) * m (x - 1).
  by rewrite ler_wpM2l// -subr_ge0.
by rewrite ler_wpM2r// (le_trans h1 LK).
Qed.

Lemma upper_energy_lt c w1 w2 : -1 < c -> w1 < w2 -> 0 < m w2 ->
  upper_energy mu c w2 < upper_energy mu c w1.
Proof.
move=> c1 w12 m2; rewrite -subr_gt0.
apply: lt_le_trans (upper_energy_decr c1 (ltW w12)).
have c0 : 0 < 1 + c by rewrite addrC -ltrBlDr sub0r.
by rewrite !mulr_gt0// ?subr_gt0// lt_min ltr01.
Qed.

Lemma upper_energy_ge c w : (1 + c) * m w ^+ 2 <= upper_energy mu c w.
Proof.
pose p x := Num.max ((x : R) - w) 0.
have i2 := @integrable_upper_pow w 2 isT.
have pi : integrable p.
  by move: (@integrable_upper_pow w 1 isT); apply: eq_integrable => // x _;
    rewrite /= expr1.
have sm : m w ^+ 2 <= s w.
  have -> : m w = \int[mu]_x p x by apply: eq_Rintegral => x _; rewrite expr1.
  exact: Rintegral_sqr_le pi i2.
by rewrite /upper_energy mulrDl mul1r lerD2r.
Qed.

End upper_moment_theory.

Section stability.
Context {R : realType} (mu nu : probability (measurableTypeR R) R).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Hypothesis nu2 :
  nu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Variables (c z : R).
Hypothesis c1 : -1 < c.

Local Notation w2 := (upper_cutoff nu c z).
Local Notation D := (`|upper_moment mu 1 w2 - upper_moment nu 1 w2|).
Local Notation delta := (`|c| / Num.min 1 (1 + c) * D).

Lemma upper_cutoff_stability : `|upper_cutoff mu c z - w2| <= delta.
Proof.
set w1 := upper_cutoff mu c z.
have e1 := upper_cutoffE mu2 z c1; rewrite -/w1 in e1.
have e2 := upper_cutoffE nu2 z c1.
have d0 : 0 < Num.min 1 (1 + c) by rewrite lt_min ltr01 /= addrC -ltrBlDr sub0r.
have G12 := fun h : w1 <= w2 => upper_cutoff_growth mu2 c1 h.
have G21 := fun h : w2 <= w1 => upper_cutoff_growth mu2 c1 h.
move: G12 G21 e1 e2 d0.
move: (upper_moment mu 1 w1) (upper_moment mu 1 w2) (upper_moment nu 1 w2).
move=> A1 A2 B2; move: (Num.min 1 (1 + c)) => dm.
clearbody w1; move: w1 (upper_cutoff nu c z) => v1 v2 G12 G21 e1 e2 d0.
have hc1 : c * (B2 - A2) <= `|c| * `|A2 - B2|.
  by rewrite distrC -normrM ler_norm.
have hc2 : - (c * (B2 - A2)) <= `|c| * `|A2 - B2|.
  by rewrite distrC -normrM -normrN ler_norm.
have key : dm * `|v1 - v2| <= `|c| * `|A2 - B2|.
  case: (leP v1 v2) => v12.
    by have := G12 v12; rewrite distrC ger0_norm ?subr_ge0//; lra.
  have := G21 (ltW v12); rewrite ger0_norm; first by rewrite subr_ge0 ltW.
  by move: hc2; rewrite mulrBr; lra.
by rewrite mulrAC ler_pdivlMr// mulrC.
Qed.

Lemma upper_value_stability :
  `|upper_value mu c z - upper_value nu c z| <=
  `|upper_moment mu 2 w2 - upper_moment nu 2 w2|
  + `|c| * `|upper_moment mu 1 w2 ^+ 2 - upper_moment nu 1 w2 ^+ 2|
  + 2 * (1 + `|c|) * (upper_moment mu 1 w2 + delta) * delta.
Proof.
set w1 := upper_cutoff mu c z.
have hd := upper_cutoff_stability; rewrite -/w1 in hd.
have d0 : 0 <= delta.
  by rewrite mulr_ge0 ?divr_ge0// ltW// lt_min ltr01 /= addrC -ltrBlDr sub0r.
have L12 := fun h : w1 <= w2 => upper_energy_lipschitz mu2 c h.
have L21 := fun h : w2 <= w1 => upper_energy_lipschitz mu2 c h.
have M12 := fun h : w1 <= w2 => upper_moment1_lipschitz mu2 h.
have ma := upper_moment_ge0 mu 1 w1; have mb := upper_moment_ge0 mu 1 w2.
have T2 : `|upper_energy mu c w2 - upper_energy nu c w2| <=
    `|upper_moment mu 2 w2 - upper_moment nu 2 w2|
    + `|c| * `|upper_moment mu 1 w2 ^+ 2 - upper_moment nu 1 w2 ^+ 2|.
  rewrite /upper_energy.
  have -> : upper_moment mu 2 w2 + c * upper_moment mu 1 w2 ^+ 2 -
      (upper_moment nu 2 w2 + c * upper_moment nu 1 w2 ^+ 2) =
      (upper_moment mu 2 w2 - upper_moment nu 2 w2)
      + c * (upper_moment mu 1 w2 ^+ 2 - upper_moment nu 1 w2 ^+ 2) by ring.
  by apply: le_trans (ler_normD _ _) _; rewrite normrM.
rewrite /upper_value -/w1.
(* Generalize the large terms, so that lra works on atoms. *)
move: L12 L21 M12 ma mb T2 hd d0.
move: (upper_energy mu c w1) (upper_energy mu c w2) (upper_energy nu c w2).
move=> E11 E12 E22.
move: (upper_moment mu 1 w1) (upper_moment mu 1 w2) => a1 a2.
clearbody w1; move: w1 w2 => v1 v2 L12 L21 M12 ma mb T2 hd d0.
set dl := `|c| / Num.min 1 (1 + c) * `|a2 - upper_moment nu 1 v2| in hd d0 *.
set B := `|upper_moment mu 2 v2 - upper_moment nu 2 v2| +
  `|c| * `|a2 ^+ 2 - upper_moment nu 1 v2 ^+ 2| in T2 *.
clearbody dl B.
have k0 : 0 <= 2 * (1 + `|c|) by rewrite mulr_ge0// addr_ge0.
have T1 : `|E11 - E12| <= 2 * (1 + `|c|) * (a2 + dl) * dl.
  case: (leP v1 v2) => v12.
    have := L12 v12; have /andP[_ hM] := M12 v12.
    have h0 : 0 <= v2 - v1 by rewrite subr_ge0.
    have hv : v2 - v1 <= dl by move: hd; rewrite distrC ger0_norm.
    move=> h; apply: le_trans h _; rewrite -!mulrA ler_wpM2l//.
    rewrite ler_wpM2l ?addr_ge0//.
    by apply: ler_pM => //; lra.
  have := L21 (ltW v12).
  have h0 : 0 <= v1 - v2 by rewrite subr_ge0 ltW.
  have hv : v1 - v2 <= dl by move: hd; rewrite ger0_norm.
  rewrite distrC => h; apply: le_trans h _; rewrite -!mulrA ler_wpM2l//.
  rewrite ler_wpM2l ?addr_ge0//.
  by apply: ler_pM => //; lra.
have -> : E11 - E22 = (E11 - E12) + (E12 - E22) by ring.
by apply: le_trans (ler_normD _ _) _; lra.
Qed.

End stability.

Section stability_cvg.
Context {R : realType} (mu_ : nat -> probability (measurableTypeR R) R)
  (mu : probability (measurableTypeR R) R).
Hypothesis mu_2 : forall n, (mu_ n).-integrable [set: measurableTypeR R]
  (EFin \o (fun x => (x : R) ^+ 2)).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Variables (c z : R).
Hypothesis c1 : -1 < c.

Local Notation w := (upper_cutoff mu c z).
Hypothesis m_cvg :
  upper_moment (mu_ n) 1 w @[n --> \oo] --> upper_moment mu 1 w.
Hypothesis s_cvg :
  upper_moment (mu_ n) 2 w @[n --> \oo] --> upper_moment mu 2 w.

Let K := `|c| / Num.min 1 (1 + c).
Let d n := K * `|upper_moment (mu_ n) 1 w - upper_moment mu 1 w|.

Let d_cvg : d n @[n --> \oo] --> 0.
Proof.
rewrite -(mulr0 K); apply: cvgM; first exact: cvg_cst.
by apply/norm_cvg0P; apply/subr_cvg0.
Qed.

Lemma upper_cutoff_cvg : upper_cutoff (mu_ n) c z @[n --> \oo] --> w.
Proof.
apply: (@squeeze_cvgr _ _ _ _ (fun n => w - d n) (fun n => w + d n)).
- apply: nearW => n; have := upper_cutoff_stability (mu_2 n) mu2 z c1.
  by rewrite -/K -/(d n) -ler_distlC distrC.
- by rewrite -[X in _ --> X]subr0; apply: cvgB => //; exact: cvg_cst.
- by rewrite -[X in _ --> X]addr0; apply: cvgD => //; exact: cvg_cst.
Qed.

Lemma upper_value_cvg :
  upper_value (mu_ n) c z @[n --> \oo] --> upper_value mu c z.
Proof.
pose a n := upper_moment (mu_ n) 1 w; pose A := upper_moment mu 1 w.
pose b n := `|upper_moment (mu_ n) 2 w - upper_moment mu 2 w|
  + `|c| * `|a n ^+ 2 - A ^+ 2| + 2 * (1 + `|c|) * (a n + d n) * d n.
have hb n : `|upper_value (mu_ n) c z - upper_value mu c z| <= b n.
  exact: (upper_value_stability (mu_2 n) mu2 z c1).
have a2 : a n ^+ 2 @[n --> \oo] --> A ^+ 2.
  have -> : (fun n => a n ^+ 2) = a \* a by apply/funext => n; rewrite expr2.
  by rewrite expr2; exact: cvgM.
have b_cvg : b n @[n --> \oo] --> 0.
  have -> : (0 : R) = 0 + `|c| * 0 + 2 * (1 + `|c|) * (A + 0) * 0.
    by rewrite !mulr0 !addr0.
  apply: cvgD; first apply: cvgD.
  - by apply/norm_cvg0P; apply/subr_cvg0.
  - apply: cvgM; first exact: cvg_cst.
    by apply/norm_cvg0P; apply/subr_cvg0.
  - apply: cvgM => //; apply: cvgM; first exact: cvg_cst.
    exact: cvgD.
apply/subr_cvg0/norm_cvg0P.
apply: (@squeeze_cvgr _ _ _ _ (fun=> 0) b) => //.
- by apply: nearW => n; rewrite normr_ge0 hb.
- exact: cvg_cst.
Qed.

End stability_cvg.

Section symmetric_law.
Context {R : realType} (mu : probability (measurableTypeR R) R).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Hypothesis musym : forall A : set (measurableTypeR R), measurable A ->
  mu ((fun x => - x) @^-1` A) = mu A.

Local Notation m := (upper_moment mu 1).
Local Notation s := (upper_moment mu 2).
Local Notation integrable f :=
  (mu.-integrable [set: measurableTypeR R] (EFin \o f)).

Let mN : measurable_fun [set: measurableTypeR R]
  (fun x : measurableTypeR R => (- x : measurableTypeR R)).
Proof. exact: measurable_funN. Qed.

Lemma integrable_sym (f : measurableTypeR R -> R) :
  integrable f -> integrable (fun x => f (- x)).
Proof.
move=> fi; have mf : measurable_fun [set: measurableTypeR R] (EFin \o f).
  exact: measurable_int fi.
pose ng := (fun x : measurableTypeR R => ((- x)%R : measurableTypeR R)).
have E : (\int[pushforward mu ng]_y `|(f y)%:E| = \int[mu]_y `|(f y)%:E|)%E.
  by apply: eq_measure_integral => A mA _; exact: musym.
apply/integrableP; split; first exact: (measurableT_comp mf mN).
have := @ge0_integral_pushforward _ _ _ _ _ ng mN mu [set: measurableTypeR R]
  (fun y => `|(f y)%:E|%E) measurableT.
rewrite preimage_setT => <- //=.
  by apply/measurable_EFinP; apply: measurableT_comp => //;
    apply/measurable_EFinP.
move: E; under eq_integral do rewrite abse_EFin.
under [X in _ = X -> _]eq_integral do rewrite abse_EFin.
move=> ->; case/integrableP: fi => _ h; apply: le_lt_trans h.
by under [X in (_ <= X)%E]eq_integral => x _ do rewrite /comp abse_EFin.
Qed.

Lemma Rintegral_sym (f : measurableTypeR R -> R) :
  integrable f -> \int[mu]_x f (- x) = \int[mu]_x f x.
Proof.
move=> fi; have fgi := integrable_sym fi.
pose ng := (fun x : measurableTypeR R => ((- x)%R : measurableTypeR R)).
rewrite /Rintegral; congr fine.
have E2 : (\int[pushforward mu ng]_y (f y)%:E = \int[mu]_y (f y)%:E)%E.
  by apply: eq_measure_integral => A mA _; exact: musym.
rewrite -E2 integral_pushforward//; exact: measurable_int fi.
Qed.

Lemma Rintegral_id_sym : \int[mu]_x (x : R) = 0.
Proof.
have xi := integrable_idR mu2; have h := Rintegral_sym xi.
have e : \int[mu]_x (- (x : R)) = - \int[mu]_x (x : R).
  under eq_Rintegral do rewrite -mulN1r.
  by rewrite RintegralZl// mulN1r.
by move: h; rewrite e; move: (\int[mu]_x (x : R)) => I; lra.
Qed.

Let upper_reflect k w : (k <= 2)%N ->
  upper_moment mu k (- w) = \int[mu]_x (Num.max (w - (x : R)) 0 ^+ k).
Proof.
move=> k2; rewrite /upper_moment.
rewrite -(Rintegral_sym (integrable_upper_pow mu2 (- w) k2)).
by apply: eq_Rintegral => x _; rewrite opprK addrC.
Qed.

Let integrable_reflect k w : (k <= 2)%N ->
  integrable (fun x => Num.max (w - (x : R)) 0 ^+ k).
Proof.
move=> k2; apply: (integrable_quad_bound mu2 (a := 1 + 2 * w ^+ 2) (b := 2)).
  apply: measurable_funX; apply: measurable_maxr => //.
  by apply: measurable_funB => //; exact: measurable_cst.
move=> x; case: (leP (w - (x : R)) 0) => xw.
  rewrite ger0_norm ?exprn_ge0//.
  by case: k k2 => [_|[_|[_|//]]]; rewrite ?expr0 ?expr1 ?expr0n/=; nra.
rewrite ger0_norm; first by rewrite exprn_ge0// ltW.
case: k k2 => [_|[_|[_|//]]]; rewrite ?expr0 ?expr1.
- by nra.
- have h1 := sqr_ge0 (2 * (x : R) + 1); have h2 := sqr_ge0 (2 * w - 1).
  by nra.
- by have h1 := sqr_ge0 ((x : R) + w); nra.
Qed.

Lemma upper_moment1_sym w : m (- w) = m w + w.
Proof.
have i1 := integrable_upper_pow mu2 w (isT : (1 <= 2)%N).
have ir := integrable_reflect w (isT : (1 <= 2)%N).
have xi := integrable_idR mu2.
rewrite upper_reflect//.
have : m w - \int[mu]_x (Num.max (w - (x : R)) 0 ^+ 1) = - w.
  rewrite /upper_moment -RintegralB//.
  have -> : (fun x =>
      Num.max ((x : R) - w) 0 ^+ 1 - Num.max (w - (x : R)) 0 ^+ 1)
      = (fun x => (x : R) - w).
    apply/funext => x; rewrite !expr1.
    by case: (leP ((x : R) - w) 0) => h1; case: (leP (w - (x : R)) 0) => h2;
      lra.
  by rewrite RintegralB ?Rintegral_id_sym ?Rintegral_prob_cst ?sub0r//;
    exact: integrable_cst_R.
by move: (m w) (\int[mu]_x (Num.max (w - (x : R)) 0 ^+ 1)) => a b; lra.
Qed.

Lemma upper_moment2_sym w : s (- w) + s w = \int[mu]_x ((x : R) ^+ 2) + w ^+ 2.
Proof.
have i2 := integrable_upper_pow mu2 w (isT : (2 <= 2)%N).
have ir := integrable_reflect w (isT : (2 <= 2)%N).
have xi := integrable_idR mu2.
rewrite upper_reflect// /upper_moment -RintegralD//.
have -> : (fun x => Num.max (w - (x : R)) 0 ^+ 2 + Num.max ((x : R) - w) 0 ^+ 2)
    = (fun x => ((x : R) ^+ 2 - 2 * w * (x : R)) + w ^+ 2).
  apply/funext => x.
  by case: (leP ((x : R) - w) 0) => h1; case: (leP (w - (x : R)) 0) => h2;
    rewrite ?expr0n /=; nra.
rewrite RintegralD//.
- by apply: integrableB_R => //; exact: integrableZl_R.
- exact: integrable_cst_R.
rewrite RintegralB//; first exact: integrableZl_R.
by rewrite RintegralZl// Rintegral_id_sym Rintegral_prob_cst mulr0 subr0.
Qed.

Lemma upper_cutoff_dual c z : -1 < c ->
  upper_cutoff mu (- c / (1 + c)) (- z / (1 + c)) = - upper_cutoff mu c z.
Proof.
move=> c1; have c0 : 0 < 1 + c by rewrite addrC -ltrBlDr sub0r.
have c1' : -1 < - c / (1 + c).
  by rewrite ltr_pdivlMr// mulN1r ltrN2 ltrDr ltr01.
symmetry; apply: (upper_cutoff_unique mu2 c1').
set w := upper_cutoff mu c z.
have e := upper_cutoffE mu2 z c1; rewrite -/w in e.
rewrite upper_moment1_sym; move: (m w) e => M e.
have -> : z = c * M - w by lra.
have cn0 : 1 + c != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma upper_value_dual c z : -1 < c ->
  upper_value mu c z + upper_value mu (- c / (1 + c)) (- z / (1 + c)) =
  \int[mu]_x ((x : R) ^+ 2) + z ^+ 2 / (1 + c).
Proof.
move=> c1; have c0 : 0 < 1 + c by rewrite addrC -ltrBlDr sub0r.
rewrite /upper_value upper_cutoff_dual// /upper_energy.
set w := upper_cutoff mu c z.
have e := upper_cutoffE mu2 z c1; rewrite -/w in e.
have h2 := upper_moment2_sym w; rewrite upper_moment1_sym.
move: (m w) (s w) (s (- w)) (\int[mu]_x ((x : R) ^+ 2)) e h2 => M S1 S2 V e h2.
have -> : S2 = V + w ^+ 2 - S1 by lra.
have -> : z = c * M - w by lra.
have cn0 : 1 + c != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma upper_variational_sym_le c (f : measurableTypeR R -> R) : -1 < c ->
  measurable_fun [set: measurableTypeR R] f -> (forall x, 0 <= f x) ->
  integrable (fun x => f x ^+ 2) ->
  (\int[mu]_x ((x : R) * f x)) ^+ 2 <=
  upper_value mu c 0 * (\int[mu]_x (f x ^+ 2) + c * (\int[mu]_x f x) ^+ 2).
Proof.
move=> c1 mf f0 f2i.
have V' (g : measurableTypeR R -> R) :
    measurable_fun [set: measurableTypeR R] g -> (forall x, 0 <= g x) ->
    integrable (fun x => g x ^+ 2) ->
    Num.max (\int[mu]_x ((x : R) * g x)) 0 ^+ 2 <=
    upper_value mu c 0 * (\int[mu]_x (g x ^+ 2) + c * (\int[mu]_x g x) ^+ 2).
  move=> mg g0 g2i; have := upper_variational_le mu2 0 c1 mg g0 g2i.
  have -> : (fun x : measurableTypeR R => ((x : R) + 0) * g x) =
      (fun x => (x : R) * g x) by apply/funext => x; rewrite addr0.
  exact.
have fi := integrable_of_sqr mf f2i.
have xfi : integrable (fun x => (x : R) * f x).
  by apply: integrable_mul_sqr => //; exact: measurable_id.
case: (leP 0 (\int[mu]_x ((x : R) * f x))) => a0.
  by have := V' f mf f0 f2i; rewrite max_l.
pose h x := f (- x).
have mh : measurable_fun [set: measurableTypeR R] h := measurableT_comp mf mN.
have h0 x : 0 <= h x by exact: f0.
have h2i : integrable (fun x => h x ^+ 2) := integrable_sym f2i.
have Eh2 : \int[mu]_x (h x ^+ 2) = \int[mu]_x (f x ^+ 2) := Rintegral_sym f2i.
have Eh : \int[mu]_x h x = \int[mu]_x f x := Rintegral_sym fi.
have Fi : integrable (fun x => (-1) * ((x : R) * f x)) :=
  integrableZl_R (-1) xfi.
have Exh : \int[mu]_x ((x : R) * h x) = - \int[mu]_x ((x : R) * f x).
  rewrite -mulN1r -RintegralZl// -(Rintegral_sym Fi).
  by apply: eq_Rintegral => x _; rewrite /h mulN1r mulNr opprK.
have := V' h mh h0 h2i; rewrite Exh Eh2 Eh max_l ?sqrrN//.
by rewrite oppr_ge0 ltW.
Qed.

End symmetric_law.

(* HB declares canonical projections that the structures of the measure
   already provide; the warning says so. The setting lasts until the end of
   this file and is not exported. *)
Set Warnings "-redundant-canonical-projection".

Section empirical.
Context {R : realType}.
Local Open Scope ereal_scope.
Implicit Types (s : seq R) (A : set (measurableTypeR R)).

(* The Dirac masses at the elements of s. *)
Definition emp_diracs s (k : nat) :
    {measure set (measurableTypeR R) -> \bar R} :=
  \d_(nth 0%R s k : measurableTypeR R).

Lemma emp_weight_ge0 s : (0 <= (size s)%:R^-1 :> R)%R.
Proof. by rewrite invr_ge0 ler0n. Qed.

(* The empirical law of s: the average of the Dirac masses at its elements,
   and the Dirac mass at 0 when s is empty. *)
Definition empirical s : set (measurableTypeR R) -> \bar R :=
  if s is [::] then \d_(0%R : measurableTypeR R)
  else mscale (NngNum (emp_weight_ge0 s)) (msum (emp_diracs s) (size s)).

Lemma empiricalE s A : s != [::] ->
  empirical s A =
  (((size s)%:R^-1)%R)%:E * \sum_(x <- s) \d_(x : measurableTypeR R) A.
Proof.
case: s => [//|x s] _ /=.
rewrite /mscale /msum /=; congr (_ * _).
rewrite [RHS](big_nth 0%R) big_mkord /=.
by apply: eq_bigr => k _.
Qed.

Let empirical0 s : empirical s set0 = 0.
Proof. by case: s => [|x s] /=; rewrite measure0. Qed.

Let empirical_ge0 s A : 0 <= empirical s A.
Proof. by case: s => [|x s] /=; rewrite measure_ge0. Qed.

Let empirical_sigma_additive s : semi_sigma_additive (empirical s).
Proof. by case: s => [|x s] /=; exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ s := isMeasure.Build _ _ _ (empirical s)
  (empirical0 s) (empirical_ge0 s) (@empirical_sigma_additive s).

Lemma empirical_setT s : empirical s [set: measurableTypeR R] = 1.
Proof.
case: s => [|x s]; first by rewrite /= diracT.
rewrite empiricalE //; under eq_bigr do rewrite diracT.
rewrite sumEFin -EFinM; congr (_%:E).
rewrite big_const_seq count_predT iter_addr addr0 -[(_ *+ _)%R]mulr_natl.
by rewrite mulr1 mulVf // pnatr_eq0.
Qed.

HB.instance Definition _ s :=
  Measure_isProbability.Build _ _ _ (empirical s) (empirical_setT s).


Lemma ge0_integral_empirical s (f : measurableTypeR R -> \bar R) :
  s != [::] -> measurable_fun [set: measurableTypeR R] f ->
  (forall x, 0 <= f x) ->
  \int[empirical s]_x f x = (((size s)%:R^-1)%R)%:E * \sum_(x <- s) f x.
Proof.
case: s => [//|x s] _ mf f0 /=.
rewrite ge0_integral_mscale //= ge0_integral_measure_sum //; congr (_ * _).
rewrite [RHS](big_nth 0%R) big_mkord; apply: eq_bigr => k _.
by rewrite /emp_diracs integral_dirac // diracT mul1e.
Qed.

Lemma integrable_empirical s (f : measurableTypeR R -> R) :
  s != [::] -> measurable_fun [set: measurableTypeR R] f ->
  (empirical s).-integrable [set: measurableTypeR R] (EFin \o f).
Proof.
move=> s0 mf; apply/integrableP; split; first exact/measurable_EFinP.
rewrite ge0_integral_empirical //; last first.
  have -> : (\sum_(x <- s) `|(EFin \o f) x|)%E = (\sum_(x <- s) `|f x|)%:E.
    by rewrite -sumEFin; apply: eq_bigr => x _; rewrite /comp abse_EFin.
  by rewrite -EFinM ltry.
by apply: measurableT_comp => //; exact/measurable_EFinP.
Qed.

Lemma Rintegral_empirical_ge0 s (f : measurableTypeR R -> R) :
  s != [::] -> measurable_fun [set: measurableTypeR R] f ->
  (forall x, (0 <= f x)%R) ->
  (\int[empirical s]_x f x = (size s)%:R^-1 * \sum_(x <- s) f x)%R.
Proof.
move=> s0 mf f0; rewrite /Rintegral ge0_integral_empirical //.
  exact/measurable_EFinP.
have e (t : seq R) : (\sum_(x <- t) (f x)%:E)%R = (\sum_(x <- t) f x)%:E.
  by elim: t => [|y t IH]; rewrite ?big_nil ?big_cons // IH EFinD.
by rewrite e -EFinM.
Qed.

Lemma Rintegral_empirical s (f : measurableTypeR R -> R) :
  s != [::] -> measurable_fun [set: measurableTypeR R] f ->
  (\int[empirical s]_x f x = (size s)%:R^-1 * \sum_(x <- s) f x)%R.
Proof.
move=> s0 mf.
pose fp x := Num.max (f x) 0%R; pose fn x := Num.max (- f x)%R 0%R.
have fE : f = (fun x => fp x - fn x)%R.
  apply/funext => x; rewrite /fp /fn.
  case: (lerP 0 (f x)) => h.
    by rewrite (max_idPr (_ : (- f x <= 0)%R)) ?subr0 // oppr_le0.
  by rewrite (max_idPl (_ : (0 <= - f x)%R)) ?sub0r ?opprK // oppr_ge0 ltW.
have mfp : measurable_fun [set: measurableTypeR R] fp.
  by apply: measurable_maxr => //; exact: measurable_cst.
have mfn : measurable_fun [set: measurableTypeR R] fn.
  apply: measurable_maxr; last exact: measurable_cst.
  exact: measurableT_comp mf.
have fp0 x : (0 <= fp x)%R by rewrite /fp le_max lexx orbT.
have fn0 x : (0 <= fn x)%R by rewrite /fn le_max lexx orbT.
have ip := integrable_empirical s0 mfp.
have iN := integrable_empirical s0 mfn.
rewrite [in LHS]fE (RintegralB _ ip iN) //.
rewrite (Rintegral_empirical_ge0 s0 mfp fp0).
rewrite (Rintegral_empirical_ge0 s0 mfn fn0).
by rewrite -mulrBr -sumrB [in RHS]fE.
Qed.

End empirical.

Section empirical_variational.
Context {R : realType} (d : nat) (g : 'I_d -> R).
Hypothesis d0 : (0 < d)%N.

(* The empirical law of g 0, ..., g (d - 1). *)
Definition empirical_fun := empirical [seq g i | i <- enum 'I_d].

Local Notation nu := empirical_fun.

Lemma empirical_fun_neq0 : [seq g i | i <- enum 'I_d] != [::].
Proof. by rewrite -size_eq0 size_map size_enum_ord -lt0n. Qed.

Lemma sum_empirical_fun (F : R -> R) :
  \sum_(x <- [seq g i | i <- enum 'I_d]) F x = \sum_i F (g i).
Proof. by rewrite big_map big_enum. Qed.

Lemma Rintegral_empirical_fun (f : measurableTypeR R -> R) :
  measurable_fun [set: measurableTypeR R] f ->
  \int[nu]_x f x = d%:R^-1 * \sum_i f (g i).
Proof.
move=> mf; rewrite /empirical_fun (Rintegral_empirical empirical_fun_neq0 mf).
by rewrite size_map size_enum_ord sum_empirical_fun.
Qed.

Lemma empirical_fun_sqr :
  nu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Proof.
apply: integrable_empirical; first exact: empirical_fun_neq0.
exact: measurable_funX.
Qed.

Lemma upper_moment_empirical_fun k w :
  upper_moment nu k w = d%:R^-1 * \sum_i Num.max (g i - w) 0 ^+ k.
Proof.
rewrite /upper_moment Rintegral_empirical_fun //.
apply: measurable_funX; apply: measurable_maxr => //.
by apply: measurable_funB.
Qed.

(* The finite form of Lemma 5.7: the weights need not be functions of the
   values g i. *)
Lemma empirical_variational_le (c z : R) (r : 'I_d -> R) :
  0 <= c -> (forall i, 0 <= r i) ->
  d%:R^-1 * \sum_i (g i + z) * r i <=
  Num.sqrt (upper_value nu c z) *
  Num.sqrt (d%:R^-1 * \sum_i r i ^+ 2 + c * (d%:R^-1 * \sum_i r i) ^+ 2).
Proof.
move=> c0 r0.
have c1 : -1 < c by apply: lt_le_trans c0; rewrite ltrN10.
set w := upper_cutoff nu c z.
have e := upper_cutoffE empirical_fun_sqr z c1; rewrite -/w in e.
set m := upper_moment nu 1 w in e *.
set sv := upper_moment nu 2 w.
have VE : upper_value nu c z = sv + c * m ^+ 2 by [].
pose p i := Num.max (g i - w) 0.
have mE : m = d%:R^-1 * \sum_i p i.
  by rewrite /m upper_moment_empirical_fun; under eq_bigr do rewrite expr1.
have sE : sv = d%:R^-1 * \sum_i p i ^+ 2.
  by rewrite /sv upper_moment_empirical_fun.
(* Cauchy-Schwarz for finite sums *)
have cs : (\sum_i p i * r i) ^+ 2 <= (\sum_i p i ^+ 2) * (\sum_i r i ^+ 2).
  apply: discriminant_le; first by apply: sumr_ge0 => i _; exact: sqr_ge0.
  move=> t; have -> : \sum_i p i ^+ 2 + 2 * (\sum_i p i * r i) * t +
      (\sum_i r i ^+ 2) * t ^+ 2 = \sum_i (p i + t * r i) ^+ 2.
    rewrite [RHS](eq_bigr (fun i =>
      p i ^+ 2 + 2 * t * (p i * r i) + t ^+ 2 * r i ^+ 2)).
      by move=> i _; ring.
    by rewrite !big_split /= -!mulr_sumr; ring.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
(* (g i + z) r i <= (g i - w)_+ r i + c m r i, since w + z = c m *)
have h1 : \sum_i (g i + z) * r i <= \sum_i p i * r i + c * m * \sum_i r i.
  rewrite mulr_sumr -big_split /=; apply: ler_sum => i _.
  have -> : (g i + z) * r i = (g i - w) * r i + (w + z) * r i by ring.
  by rewrite e -mulrA lerD2r ler_wpM2r // /p le_max lexx.
have m0 : 0 <= m.
  rewrite mE mulr_ge0 ?invr_ge0 ?ler0n // sumr_ge0 // => i _.
  by rewrite /p le_max lexx orbT.
have sv0 : 0 <= sv.
  by rewrite sE mulr_ge0 ?invr_ge0 ?ler0n // sumr_ge0 // => i _; exact: sqr_ge0.
set A := d%:R^-1 * \sum_i r i ^+ 2.
set B := d%:R^-1 * \sum_i r i.
have A0 : 0 <= A.
  by rewrite mulr_ge0 ?invr_ge0 ?ler0n // sumr_ge0 // => i _; exact: sqr_ge0.
have B0 : 0 <= B by rewrite mulr_ge0 ?invr_ge0 ?ler0n // sumr_ge0.
set P := d%:R^-1 * \sum_i p i * r i.
have P0 : 0 <= P.
  rewrite mulr_ge0 ?invr_ge0 ?ler0n // sumr_ge0 // => i _.
  by rewrite mulr_ge0 // /p le_max lexx orbT.
have hP2 : P ^+ 2 <= sv * A.
  rewrite /P sE /A exprMn.
  have -> : d%:R^-1 * (\sum_i p i ^+ 2) * (d%:R^-1 * \sum_i r i ^+ 2) =
      d%:R^-1 ^+ 2 * ((\sum_i p i ^+ 2) * \sum_i r i ^+ 2) by ring.
  by rewrite ler_wpM2l // exprn_ge0 // invr_ge0 ler0n.
have hP : P <= Num.sqrt sv * Num.sqrt A.
  rewrite -sqrtrM // -[P]ger0_norm // -sqrtr_sqr; exact: ler_wsqrtr.
have h2 : d%:R^-1 * \sum_i (g i + z) * r i <= P + c * m * B.
  by rewrite /P /B mulrCA -mulrDr ler_wpM2l ?invr_ge0 ?ler0n.
apply: (le_trans h2); apply: (le_trans (lerD hP (lexx (c * m * B)))).
rewrite VE -sqrtrM ?addr_ge0 ?mulr_ge0 ?exprn_ge0 //.
set u := Num.sqrt sv; set v := Num.sqrt A.
have u0 : 0 <= u := sqrtr_ge0 sv.
have v0 : 0 <= v := sqrtr_ge0 A.
have -> : sv = u ^+ 2 by rewrite /u sqr_sqrtr.
have -> : A = v ^+ 2 by rewrite /v sqr_sqrtr.
apply: le_trans (_ : _ <= Num.sqrt ((u * v + c * m * B) ^+ 2)) _.
  rewrite -exprMn sqrtr_sqr ger0_norm ?mulr_ge0 // sqrtr_sqr.
  exact: ler_norm.
rewrite -sqrtrM ?addr_ge0 ?mulr_ge0 ?exprn_ge0 //; apply: ler_wsqrtr.
have : 0 <= c * (u * B - m * v) ^+ 2 by rewrite mulr_ge0 // sqr_ge0.
nra.
Qed.

Lemma empirical_variational_attained (c z : R) : -1 < c ->
  d%:R^-1 * \sum_i (g i + z) * Num.max (g i - upper_cutoff nu c z) 0 =
  upper_value nu c z.
Proof.
move=> c1; have := upper_variational_attained empirical_fun_sqr z c1.
rewrite Rintegral_empirical_fun //.
apply: measurable_funM; first by apply: measurable_funD.
by apply: measurable_maxr => //; apply: measurable_funB.
Qed.

End empirical_variational.

(* ## Monotonicity from a Taylor bound *)

Section taylor_monotone.
Context {R : realType}.

(* A function with derivative g in the sense of a Taylor bound with a
   quadratic remainder does not increase where g <= 0: a discrete
   integration of the bound. *)
Lemma taylor_nincr (F g : R -> R) (K a b : R) :
  (forall t h : R, 0 <= h -> `|F (t + h) - F t - h * g t| <= K * h ^+ 2) ->
  a <= b -> (forall t : R, a <= t -> t < b -> g t <= 0) -> F b <= F a.
Proof.
move=> hT ab hg.
have [-> //|ab'] := eqVneq a b.
have ablt : a < b by rewrite lt_neqAle ab' ab.
(* F b - F a <= K (b - a)^2 / N, by N steps of length (b - a) / N *)
have key N : (0 < N)%N -> F b - F a <= K * (b - a) ^+ 2 / N%:R.
  move=> N0; have NR : 0 < N%:R :> R by rewrite ltr0n.
  pose h := (b - a) / N%:R.
  have h0 : 0 < h by rewrite divr_gt0 // subr_gt0.
  pose u (k : nat) := F (a + k%:R * h).
  have uN : u N = F b by rewrite /u /h mulrC divfK ?gt_eqF // addrC subrK.
  have u0 : u 0%N = F a by rewrite /u mul0r addr0.
  rewrite -uN -u0 -(telescope_sumr _ (leq0n N)).
  have -> : K * (b - a) ^+ 2 / N%:R = \sum_(0 <= k < N) (K * h ^+ 2).
    rewrite sumr_const_nat subn0 /h -mulr_natr.
    have nz : N%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
    by field.
  apply: ler_sum_nat => k /andP[_ kN].
  have tk : a <= a + k%:R * h by rewrite lerDl mulr_ge0 // ltW.
  have tkb : a + k%:R * h < b.
    have : k%:R * h < N%:R * h by rewrite ltr_pM2r // ltr_nat.
    have Nh : N%:R * h = b - a by rewrite /h mulrC divfK ?gt_eqF.
    by rewrite Nh => kh; lra.
  have gk := hg _ tk tkb.
  rewrite /u -natr1 mulrDl mul1r addrA.
  have hb := hT (a + k%:R * h) h (ltW h0).
  have hg0 : h * g (a + k%:R * h) <= 0 by rewrite mulr_ge0_le0 // ltW.
  have := ler_norm (F (a + k%:R * h + h) - F (a + k%:R * h) -
    h * g (a + k%:R * h)).
  lra.
rewrite leNgt; apply/negP => Fab.
have d0 : 0 < F b - F a by rewrite subr_gt0.
pose N := (archimedean.Num.truncn (K * (b - a) ^+ 2 / (F b - F a))).+1.
have NR : 0 < N%:R :> R by rewrite ltr0n.
have := key N isT.
have : K * (b - a) ^+ 2 / N%:R < F b - F a.
  have hk :=
    archimedean.Num.Theory.truncnS_gt (K * (b - a) ^+ 2 / (F b - F a)).
  rewrite ltr_pdivrMr // in hk; rewrite -/N in hk.
  by rewrite ltr_pdivrMr //; nra.
lra.
Qed.

Lemma taylor_ndecr (F g : R -> R) (K a b : R) :
  (forall t h : R, 0 <= h -> `|F (t + h) - F t - h * g t| <= K * h ^+ 2) ->
  a <= b -> (forall t : R, a <= t -> t < b -> 0 <= g t) -> F a <= F b.
Proof.
move=> hT ab hg.
suff : - F b <= - F a by rewrite lerN2.
apply: (taylor_nincr (F := fun t => - F t) (g := fun t => - g t) (K := K))
  => //.
  move=> t h h0.
  have -> : - F (t + h) - - F t - h * - g t =
    - (F (t + h) - F t - h * g t) by ring.
  by rewrite normrN; exact: hT.
by move=> t ta tb; rewrite oppr_le0; exact: hg.
Qed.

End taylor_monotone.

(* ## The energy of a clip to [t, C t] *)

Section clip_energy.
Context {R : realType} (mu : probability (measurableTypeR R) R).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).

Local Notation m := (upper_moment mu 1).
Local Notation s := (upper_moment mu 2).

(* s(-t) + s(C t): for a symmetric law, the mean squared distance from X
   to the interval [t, C t] (clip_energyE). *)
Definition clip_energy (C t : R) : R := s (- t) + s (C * t).

(* Its infimum over t >= 0. *)
Definition clip_value (C : R) : R :=
  inf [set clip_energy C t | t in [set t : R | 0 <= t]].

Lemma clip_energy_ge0 (C t : R) : 0 <= clip_energy C t.
Proof. by rewrite /clip_energy addr_ge0 // upper_moment_ge0. Qed.

Lemma clip_value_le (C t : R) : 0 <= t -> clip_value C <= clip_energy C t.
Proof.
move=> t0; apply: ge_inf; last by exists t.
by exists 0 => _ [u _ <-]; exact: clip_energy_ge0.
Qed.

Lemma clip_value_ge (C r : R) :
  (forall t : R, 0 <= t -> r <= clip_energy C t) -> r <= clip_value C.
Proof.
move=> h; apply: lb_le_inf; first by exists (clip_energy C 0), 0 => //=.
by move=> _ [t t0 <-]; exact: h.
Qed.

(* The derivative in t is 2 (m(-t) - C m(C t)). *)
Lemma clip_energy_taylor (C t h : R) :
  `|clip_energy C (t + h) - clip_energy C t -
    h * (2 * (m (- t) - C * m (C * t)))| <= (1 + C ^+ 2) * h ^+ 2.
Proof.
have h1 := upper_moment2_taylor mu2 (- t) (- h).
have h2 := upper_moment2_taylor mu2 (C * t) (C * h).
rewrite /clip_energy opprD mulrDr.
have -> : s (- t + - h) + s (C * t + C * h) - (s (- t) + s (C * t)) -
    h * (2 * (m (- t) - C * m (C * t))) =
  (s (- t + - h) - s (- t) + 2 * (- h) * m (- t)) +
  (s (C * t + C * h) - s (C * t) + 2 * (C * h) * m (C * t)) by ring.
apply: le_trans (ler_normD _ _) _.
have -> : (1 + C ^+ 2) * h ^+ 2 = (- h) ^+ 2 + (C * h) ^+ 2.
  by rewrite sqrrN exprMn; ring.
exact: lerD h1 h2.
Qed.

(* A zero t0 of the derivative, with the derivative <= 0 before it and
   >= 0 after it, is a minimum. *)
Lemma clip_value_attained (C t0 : R) : 0 <= t0 ->
  (forall t : R, 0 <= t -> t < t0 -> m (- t) <= C * m (C * t)) ->
  (forall t : R, t0 <= t -> C * m (C * t) <= m (- t)) ->
  clip_value C = clip_energy C t0.
Proof.
move=> t00 hlo hhi.
have hT (t h : R) : 0 <= h ->
    `|clip_energy C (t + h) - clip_energy C t -
      h * (2 * (m (- t) - C * m (C * t)))| <= (1 + C ^+ 2) * h ^+ 2.
  by move=> _; exact: clip_energy_taylor.
apply/eqP; rewrite eq_le; apply/andP; split; first exact: clip_value_le.
apply: clip_value_ge => t tp.
have [tt0|t0t] := leP t t0.
  apply: (taylor_nincr hT tt0) => u tu ut0.
  by rewrite pmulr_rle0 // subr_le0; apply: hlo => //; exact: le_trans tp tu.
apply: (taylor_ndecr hT (ltW t0t)) => u tu ut.
by rewrite pmulr_rge0 // subr_ge0; exact: hhi.
Qed.

Lemma clip_energy_C (C C' t : R) : 0 <= t -> C <= C' ->
  0 <= clip_energy C t - clip_energy C' t <=
    (C' - C) * t * (m (C * t) + m (C' * t)).
Proof.
move=> t0 CC.
have h := upper_moment2_lipschitz mu2 (ler_wpM2r t0 CC).
have -> : clip_energy C t - clip_energy C' t = s (C * t) - s (C' * t).
  by rewrite /clip_energy; ring.
by rewrite (_ : (C' - C) * t = C' * t - C * t) //; ring.
Qed.

Lemma clip_value_nincr (C C' : R) : C <= C' -> clip_value C' <= clip_value C.
Proof.
move=> CC; apply: clip_value_ge => t t0.
apply: le_trans (clip_value_le C' t0) _.
by have /andP[h _] := clip_energy_C t0 CC; rewrite -subr_ge0.
Qed.

End clip_energy.

Section clip_energy_sym.
Context {R : realType} (mu : probability (measurableTypeR R) R).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Hypothesis musym : forall A : set (measurableTypeR R), measurable A ->
  mu ((fun x => - x) @^-1` A) = mu A.

(* For a symmetric law, clip_energy is the integral of
   (t - x)_+^2 + (x - C t)_+^2, the squared distance from x to [t, C t]
   when 0 <= t <= C t. *)
Lemma clip_energyE (C t : R) :
  \int[mu]_x (Num.max (t - (x : R)) 0 ^+ 2 + Num.max ((x : R) - C * t) 0 ^+ 2) =
  clip_energy mu C t.
Proof.
have i0 := integrable_upper_pow mu2 (- t) (isT : (2 <= 2)%N).
have i1 : mu.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => Num.max (t - (x : R)) 0 ^+ 2)).
  have := integrable_sym musym i0.
  by apply: eq_integrable => // x _ /=; rewrite opprK addrC.
have i2 := integrable_upper_pow mu2 (C * t) (isT : (2 <= 2)%N).
rewrite RintegralD //; congr (_ + _).
have -> : \int[mu]_x Num.max (t - (x : R)) 0 ^+ 2 =
    \int[mu]_x (Num.max ((- (x : R)) - (- t)) 0 ^+ 2).
  by apply: eq_Rintegral => x _; rewrite opprK addrC.
exact: (Rintegral_sym musym i0).
Qed.

End clip_energy_sym.
