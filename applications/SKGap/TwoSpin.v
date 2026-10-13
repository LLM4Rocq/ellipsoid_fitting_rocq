From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint matrix sesquilinear.
From mathcomp Require Import boolp reals sequences exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianApplications Require Import SKGapDefinitions.
From GaussianApplications.SKGap Require Import Ising.

(**md**************************************************************************)
(* # The uniform two-spin inequality                                          *)
(*                                                                            *)
(* Part of target T4 of phase 12 (AGENTS.md, section Phase 12). A Rocq        *)
(* formalization of the credited argument of the lemma 'Uniform two-spin      *)
(* inequality' of 'Cutoff throughout the high-temperature Sherrington-        *)
(* Kirkpatrick phase' (family 227 of the OpenAI math collection, revision     *)
(* 1581d4cbd, appendices/entropy.tex). The remainder of the expansion in t is *)
(* bounded by a real polynomial certificate instead of the manuscript's       *)
(* complex Cauchy estimate, as the Lean module of the collection does:        *)
(* Lean: pair_cubic_signed_bound (SKRatio/Calculus/TwoSpin.lean)              *)
(* The coefficients of the certificate are those of the unique polynomial R   *)
(* with t^3 R equal to the numerator of C - L; they were computed             *)
(* independently and agree with those of the Lean module. Nothing is copied   *)
(* from the Lean code.                                                        *)
(*                                                                            *)
(* - The pair law: for |a|, |b| <= 1 and |t| <= 1/4, plaw a b t F is the mean *)
(*   of F under the law proportional to (1 + a x)(1 + b y)(1 + t x y) on {-1, *)
(*   1}^2; pcm and pcv are the conditional means and variances, and pg1, pg2  *)
(*   the half-differences p + r (y - b) and q + r (x - a).                    *)
(* - ts_certificate, ts_coef_bound: the coefficient C of the manuscript is    *)
(*   the leading term L = 1 + a b t + (1 - a^2 - b^2 + 2 a^2 b^2) t^2 up to   *)
(*   30000 |t|^3.                                                             *)
(* - pair_factorization: the mixed energy plus the correction term is P_0 Q,  *)
(*   as in the manuscript; pair_signed_mean_lower: Q >= - 30000 |t|^3 (p^2 +  *)
(*   q^2) for |t| <= 1/1000.                                                  *)
(* - plaw_energy_ge, pprefactor_bounds: the energies are at least (3/5) (1 -  *)
(*   a^2) p^2 and (3/5) (1 - b^2) q^2, and 0 <= P_0 <= (4/3) (1 - a^2) (1 -   *)
(*   b^2).                                                                    *)
(* - pair_two_spin: the inequality of the lemma for the pair law, with t_0 =  *)
(*   1/1000 and C_0 = 70000 (the manuscript's example is t_0 = 1/100, C_0 =   *)
(*   22000; the Lean theorem has C_0 = 1920000).                              *)
(* - ising_two_spin: the inequality of the lemma for the Ising law of a       *)
(*   symmetric A with zero diagonal, for i != j with |tanh A_ij| <= 1/1000:   *)
(*   nu[D_i f D_j f] >= - nu[(t + 2 t^2 m_i m_j) v_i v_j d_i f d_j f] - 70000 *)
(*   |t|^3 (nu[v_i (d_i f)^2] + nu[v_j (d_j f)^2]), with t = tanh A_ij. The   *)
(*   proof conditions on the spins outside i and j (ising_mean_block,         *)
(*   ising_weight_block).                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section two_spin_certificate.
Variable R : realType.
Implicit Types a b t : R.

Definition ts_lead a b t : R :=
  1 + a * b * t + (1 - a ^+ 2 - b ^+ 2 + 2 * a ^+ 2 * b ^+ 2) * t ^+ 2.

Definition ts_coef a b t : R :=
  (1 - t) / ((1 + a * t) * (1 + b * t)) +
  (t + 2 * t ^+ 2 * ((a + t) / (1 + a * t)) * ((b + t) / (1 + b * t))) *
    ((1 - t ^+ 2) * (1 + a) * (1 + b) * (1 + t)) /
    ((1 + a * t) ^+ 2 * (1 + b * t) ^+ 2).

Definition ts_monomials : seq (int * nat * nat * nat) :=
  [:: (Negz 0, 0, 0, 0); (Negz 0, 0, 1, 0); (Posz 2, 0, 2, 0);
     (Posz 2, 0, 3, 0); (Negz 0, 1, 0, 0); (Posz 4, 1, 1, 0);
     (Posz 2, 1, 2, 0); (Negz 2, 1, 3, 0); (Posz 2, 2, 0, 0);
     (Posz 2, 2, 1, 0); (Negz 5, 2, 2, 0); (Negz 5, 2, 3, 0);
     (Posz 2, 3, 0, 0); (Negz 2, 3, 1, 0); (Negz 5, 3, 2, 0);
     (Posz 1, 0, 0, 1); (Posz 2, 0, 1, 1); (Negz 1, 0, 2, 1);
     (Posz 3, 0, 4, 1); (Posz 2, 1, 0, 1); (Negz 6, 1, 1, 1);
     (Negz 1, 1, 2, 1); (Posz 6, 1, 3, 1); (Negz 0, 1, 4, 1);
     (Negz 1, 2, 0, 1); (Negz 1, 2, 1, 1); (Negz 2, 2, 2, 1);
     (Negz 8, 2, 3, 1); (Negz 5, 2, 4, 1); (Posz 6, 3, 1, 1);
     (Negz 8, 3, 2, 1); (Negz 17, 3, 3, 1); (Posz 3, 4, 0, 1);
     (Negz 0, 4, 1, 1); (Negz 5, 4, 2, 1); (Posz 2, 0, 0, 2);
     (Negz 0, 0, 1, 2); (Negz 2, 0, 2, 2); (Negz 0, 0, 3, 2);
     (Posz 1, 0, 5, 2); (Negz 0, 1, 0, 2); (Negz 6, 1, 1, 2);
     (Negz 14, 1, 2, 2); (Posz 9, 1, 4, 2); (Negz 2, 2, 0, 2);
     (Negz 14, 2, 1, 2); (Negz 3, 2, 2, 2); (Posz 7, 2, 3, 2);
     (Negz 2, 2, 4, 2); (Negz 1, 2, 5, 2); (Negz 0, 3, 0, 2);
     (Posz 7, 3, 2, 2); (Negz 8, 3, 3, 2); (Negz 17, 3, 4, 2);
     (Posz 9, 4, 1, 2); (Negz 2, 4, 2, 2); (Negz 17, 4, 3, 2);
     (Posz 1, 5, 0, 2); (Negz 1, 5, 2, 2); (Negz 1, 0, 0, 3);
     (Negz 3, 0, 1, 3); (Negz 1, 0, 2, 3); (Negz 3, 1, 0, 3);
     (Negz 6, 1, 1, 3); (Negz 2, 1, 2, 3); (Negz 2, 1, 3, 3);
     (Posz 3, 1, 5, 3); (Negz 1, 2, 0, 3); (Negz 2, 2, 1, 3);
     (Negz 9, 2, 2, 3); (Posz 9, 2, 4, 3); (Negz 2, 3, 1, 3);
     (Posz 5, 3, 3, 3); (Negz 2, 3, 4, 3); (Negz 5, 3, 5, 3);
     (Posz 9, 4, 2, 3); (Negz 2, 4, 3, 3); (Negz 17, 4, 4, 3);
     (Posz 3, 5, 1, 3); (Negz 5, 5, 3, 3); (Negz 1, 0, 0, 4);
     (Negz 1, 0, 1, 4); (Negz 1, 1, 0, 4); (Negz 1, 1, 1, 4);
     (Negz 2, 2, 3, 4); (Posz 3, 2, 5, 4); (Negz 2, 3, 2, 4);
     (Posz 3, 3, 4, 4); (Posz 3, 4, 3, 4); (Negz 0, 4, 4, 4);
     (Negz 5, 4, 5, 4); (Posz 3, 5, 2, 4); (Negz 5, 5, 4, 4);
     (Negz 0, 3, 3, 5); (Posz 1, 3, 5, 5); (Posz 1, 5, 3, 5);
     (Negz 1, 5, 5, 5)].

Definition ts_rem a b t : R :=
  \sum_(m <- ts_monomials) m.1.1.1%:~R * a ^+ m.1.1.2 * b ^+ m.1.2 * t ^+ m.2.

Lemma ts_certificate a b t :
  (1 - t) * (1 + a * t) ^+ 2 * (1 + b * t) ^+ 2 +
  (t * (1 + a * t) * (1 + b * t) + 2 * t ^+ 2 * (a + t) * (b + t)) *
    ((1 - t ^+ 2) * (1 + a) * (1 + b) * (1 + t)) -
  ts_lead a b t * ((1 + a * t) ^+ 3 * (1 + b * t) ^+ 3) =
  t ^+ 3 * ts_rem a b t.
Proof.
rewrite /ts_rem /ts_monomials !big_cons big_nil /= /ts_lead.
ring.
Qed.

Lemma monomials_bound (l : seq (int * nat * nat * nat)) a b t :
  `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 ->
  `|\sum_(m <- l) m.1.1.1%:~R * a ^+ m.1.1.2 * b ^+ m.1.2 * t ^+ m.2| <=
  \sum_(m <- l) `|m.1.1.1%:~R : R|.
Proof.
move=> a1 b1 t1; apply: le_trans (ler_norm_sum _ _ _) _; apply: ler_sum => m _.
rewrite !normrM !normrX -[X in _ <= X]mulr1 -!mulrA ler_wpM2l //.
by rewrite mulr_ile1 ?exprn_ge0 ?mulr_ge0 ?exprn_ile1 ?mulr_ile1 ?exprn_ge0 ?exprn_ile1.
Qed.

Lemma ts_rem_bound a b t : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 ->
  `|ts_rem a b t| <= 428.
Proof.
move=> a1 b1 t1; apply: le_trans (monomials_bound _ a1 b1 t1) _.
have -> : \sum_(m <- ts_monomials) `|m.1.1.1%:~R : R| =
    (\sum_(m <- ts_monomials) `|m.1.1.1|)%:~R.
  by rewrite rmorph_sum /=; apply: eq_bigr => m _; rewrite intr_norm.
by rewrite /ts_monomials !big_cons big_nil.
Qed.

Lemma affine_half a t : `|a| <= 1 -> `|t| <= 1 / 4 -> 1 / 2 <= 1 + a * t.
Proof.
move=> a1 t4; have : `|a * t| <= 1 / 4.
  by rewrite normrM; apply: le_trans t4; rewrite ler_piMl.
by rewrite ler_norml => /andP[h _]; lra.
Qed.

Lemma ts_coef_remainder a b t : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  ts_coef a b t - ts_lead a b t =
  t ^+ 3 * ts_rem a b t / ((1 + a * t) ^+ 3 * (1 + b * t) ^+ 3).
Proof.
move=> a1 b1 t4; have ha := affine_half a1 t4; have hb := affine_half b1 t4.
have ha0 : 1 + a * t != 0 by apply: lt0r_neq0; lra.
have hb0 : 1 + b * t != 0 by apply: lt0r_neq0; lra.
by rewrite -ts_certificate /ts_coef; field.
Qed.

Lemma ts_coef_bound a b t : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  `|ts_coef a b t - ts_lead a b t| <= 3 * 10 ^+ 4 * `|t| ^+ 3.
Proof.
move=> a1 b1 t4; have ha := affine_half a1 t4; have hb := affine_half b1 t4.
have t1 : `|t| <= 1 by apply: le_trans t4 _; lra.
rewrite ts_coef_remainder //.
set D := (1 + a * t) ^+ 3 * (1 + b * t) ^+ 3.
have h3 (u : R) : 1 / 2 <= u -> 1 / 8 <= u ^+ 3.
  move=> u2; have u0 : 0 <= u by lra.
  have := ler_pM (_ : 0 <= 1 / 2) (_ : 0 <= 1 / 2 * (1 / 2)) u2 (ler_pM _ _ u2 u2).
  move=> h; rewrite (_ : u ^+ 3 = u * (u * u)); first by rewrite !exprS expr0 mulr1.
  by apply: le_trans (h _ _ _ _); lra.
have D64 : 1 / 64 <= D.
  have h1 := h3 _ ha; have h2 := h3 _ hb; rewrite /D.
  move: h1 h2; set u := (1 + a * t) ^+ 3; set v := (1 + b * t) ^+ 3; nra.
have D0 : 0 < D by lra.
rewrite normf_div (ger0_norm (ltW D0)) normrM normrX ler_pdivrMr //.
have hr := ts_rem_bound a1 b1 t1.
have T0 : 0 <= `|t| ^+ 3 by rewrite exprn_ge0.
move: hr D64 T0; set T := `|t| ^+ 3; set X := `|ts_rem a b t|; move=> hr D64 T0.
nra.
Qed.

End two_spin_certificate.

Section two_spin_pair.
Variable R : realType.
Implicit Types (a b t p q r : R) (x y : bool).

Definition pmean a b (F : bool -> bool -> R) : R :=
  ((1 + a) * (1 + b) * F true true + (1 + a) * (1 - b) * F true false +
   (1 - a) * (1 + b) * F false true + (1 - a) * (1 - b) * F false false) / 4.

Definition plaw a b t (F : bool -> bool -> R) : R :=
  pmean a b (fun x y => (1 + t * spin x * spin y) / (1 + t * a * b) * F x y).

Definition pcm a t y : R := (a + t * spin y) / (1 + t * a * spin y).

Definition pcv a t y : R :=
  (1 - a ^+ 2) * (1 - t ^+ 2) / (1 + t * a * spin y) ^+ 2.

Definition pg1 b p r y : R := p + r * (spin y - b).

Definition pg2 a q r x : R := q + r * (spin x - a).

Definition psign a b t x y : R :=
  (spin x * spin y - t) / ((1 + t * a * spin y) * (1 + t * b * spin x)) +
  (t + 2 * t ^+ 2 * pcm a t y * pcm b t x) *
    ((1 - t ^+ 2) * (1 + a * spin x) * (1 + b * spin y) * (1 + t * spin x * spin y)) /
    ((1 + t * a * spin y) ^+ 2 * (1 + t * b * spin x) ^+ 2).

Definition pprefactor a b t : R :=
  (1 - a ^+ 2) * (1 - b ^+ 2) * (1 - t ^+ 2) / (1 + t * a * b).

Lemma affine_half' a t x : `|a| <= 1 -> `|t| <= 1 / 4 -> 1 / 2 <= 1 + t * a * spin x.
Proof.
move=> a1 t4; rewrite -mulrA [t * _]mulrC; apply: affine_half => //.
by rewrite normrM spin_norm mulr1.
Qed.

Lemma pcv_eq a t y : `|a| <= 1 -> `|t| <= 1 / 4 -> pcv a t y = 1 - pcm a t y ^+ 2.
Proof.
move=> a1 t4; have h := affine_half' y a1 t4.
have h0 : 1 + t * a * spin y != 0 by apply: lt0r_neq0; lra.
rewrite /pcv /pcm; case: y h h0 => /= h h0.
  by rewrite !mulr1 in h0 *; field.
by rewrite !mulrN1 in h0 *; field.
Qed.

Lemma psign_eq a b t x y : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  psign a b t x y =
  spin x * spin y * ts_coef (a * spin x) (b * spin y) (t * spin x * spin y).
Proof.
move=> a1 b1 t4.
have ha (z : bool) : 1 + t * a * spin z != 0.
  by apply: lt0r_neq0; have := affine_half' z a1 t4; lra.
have hb (z : bool) : 1 + t * b * spin z != 0.
  by apply: lt0r_neq0; have := affine_half' z b1 t4; lra.
move: (ha true) (ha false) (hb true) (hb false).
rewrite /psign /ts_coef /pcm /= !mulr1 !mulrN1 => h1 h2 h3 h4.
case: x; case: y => /=; rewrite ?mulr1 ?mulrN1 ?mul1r ?mulN1r ?opprK.
all: rewrite ?mulrNN ?mulrN ?mulNr ?[a * t]mulrC ?[b * t]mulrC ?mul1r ?sqrrN.
all: field.
Qed.

Lemma ts_lead_sign a b t x y :
  ts_lead (a * spin x) (b * spin y) (t * spin x * spin y) = ts_lead a b t.
Proof. by rewrite /ts_lead; case: x; case: y => /=; ring. Qed.

Lemma psign_bound a b t x y : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  `|psign a b t x y - spin x * spin y * ts_lead a b t| <= 3 * 10 ^+ 4 * `|t| ^+ 3.
Proof.
move=> a1 b1 t4; rewrite psign_eq // -(ts_lead_sign a b t x y) -mulrBr.
rewrite normrM normrM !spin_norm mul1r mul1r.
have h := @ts_coef_bound R (a * spin x) (b * spin y) (t * spin x * spin y).
by move: h; rewrite !normrM !spin_norm !mulr1; apply.
Qed.

Lemma pair_factorization a b t p q r : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  plaw a b t (fun x y => (spin x - pcm a t y) * pg1 b p r y *
    ((spin y - pcm b t x) * pg2 a q r x)) +
  plaw a b t (fun x y => (t + 2 * t ^+ 2 * pcm a t y * pcm b t x) *
    pcv a t y * pcv b t x * pg1 b p r y * pg2 a q r x) =
  pprefactor a b t *
    pmean 0 0 (fun x y => pg1 b p r y * pg2 a q r x * psign a b t x y).
Proof.
move=> a1 b1 t4.
have ha (z : bool) : 1 + t * a * spin z != 0.
  by apply: lt0r_neq0; have := affine_half' z a1 t4; lra.
have hb (z : bool) : 1 + t * b * spin z != 0.
  by apply: lt0r_neq0; have := affine_half' z b1 t4; lra.
have ab1 : `|a * b| <= 1 by rewrite normrM; apply: mulr_ile1.
have hab : 1 + t * a * b != 0.
  apply: lt0r_neq0; have := affine_half' true ab1 t4.
  by rewrite /= mulr1 mulrA; lra.
move: (ha true) (ha false) (hb true) (hb false).
rewrite /plaw /pmean /pcm /pcv /pg1 /pg2 /psign /pprefactor /spin /= !mulr1 !mulrN1.
move=> h1 h2 h3 h4.
rewrite ?mulrNN ?mulrN ?mulNr ?mul1r ?mulN1r ?opprK ?addr0 ?subr0.
rewrite /pcm /spin /= !mulr1 !mulrN1 ?mul1r.
field.
Qed.

Lemma pair_cross_mean a b p q r :
  pmean 0 0 (fun x y => spin x * spin y * pg1 b p r y * pg2 a q r x) = r ^+ 2.
Proof. by rewrite /pmean /pg1 /pg2 /spin /=; field. Qed.

Lemma pair_grad_bound a b p q r x y : `|a| <= 1 -> `|b| <= 1 ->
  `|pg1 b p r y * pg2 a q r x| <= p ^+ 2 + q ^+ 2 + 8 * r ^+ 2.
Proof.
move=> a1 b1; rewrite /pg1 /pg2.
have hy : `|spin y - b| <= 2.
  by apply: le_trans (ler_normB _ _) _; rewrite spin_norm; lra.
have hx : `|spin x - a| <= 2.
  by apply: le_trans (ler_normB _ _) _; rewrite spin_norm; lra.
move: hx hy; set u := spin y - b; set v := spin x - a => hx hy.
have hu : u ^+ 2 <= 4.
  by rewrite -real_normK ?num_real //; have := normr_ge0 u; nra.
have hv : v ^+ 2 <= 4.
  by rewrite -real_normK ?num_real //; have := normr_ge0 v; nra.
have h1 : (p + r * u) ^+ 2 <= 2 * p ^+ 2 + 8 * r ^+ 2.
  have := sqr_ge0 (p - r * u).
  have := mulr_ge0 (sqr_ge0 r) (_ : 0 <= 4 - u ^+ 2); nra.
have h2 : (q + r * v) ^+ 2 <= 2 * q ^+ 2 + 8 * r ^+ 2.
  have := sqr_ge0 (q - r * v).
  have := mulr_ge0 (sqr_ge0 r) (_ : 0 <= 4 - v ^+ 2); nra.
have h3 : `|(p + r * u) * (q + r * v)| <=
    ((p + r * u) ^+ 2 + (q + r * v) ^+ 2) / 2.
  rewrite normrM; have := sqr_ge0 (`|p + r * u| - `|q + r * v|).
  rewrite -[(p + r * u) ^+ 2]real_normK ?num_real //.
  rewrite -[(q + r * v) ^+ 2]real_normK ?num_real //.
  nra.
lra.
Qed.

Lemma ts_lead_ge a b t : `|a| <= 1 -> `|b| <= 1 -> 1 - `|t| <= ts_lead a b t.
Proof.
move=> a1 b1; rewrite /ts_lead.
have a2 : a ^+ 2 <= 1 by rewrite -real_normK ?num_real //; have := normr_ge0 a; nra.
have b2 : b ^+ 2 <= 1 by rewrite -real_normK ?num_real //; have := normr_ge0 b; nra.
have hq : 0 <= 1 - a ^+ 2 - b ^+ 2 + 2 * a ^+ 2 * b ^+ 2.
  have h1 : 0 <= (1 - a ^+ 2) * (1 - b ^+ 2) by apply: mulr_ge0; lra.
  have := mulr_ge0 (sqr_ge0 a) (sqr_ge0 b); nra.
have hab : `|a * b * t| <= `|t|.
  by rewrite !normrM ler_piMl // ?mulr_ge0 // mulr_ile1.
have := mulr_ge0 hq (sqr_ge0 t); move: hab; rewrite ler_norml => /andP[h _]; lra.
Qed.

Lemma pmean_le a b (F G : bool -> bool -> R) : `|a| <= 1 -> `|b| <= 1 ->
  (forall x y, F x y <= G x y) -> pmean a b F <= pmean a b G.
Proof.
move=> a1 b1 FG; rewrite /pmean ler_pM2r ?invr_gt0 ?ltr0n //.
have ha : 0 <= 1 + a /\ 0 <= 1 - a by move: a1; rewrite ler_norml => /andP[]; lra.
have hb : 0 <= 1 + b /\ 0 <= 1 - b by move: b1; rewrite ler_norml => /andP[]; lra.
case: ha => ha1 ha2; case: hb => hb1 hb2.
by rewrite !lerD // ler_wpM2l ?mulr_ge0.
Qed.

Lemma pmean_add a b (F G : bool -> bool -> R) :
  pmean a b (fun x y => F x y + G x y) = pmean a b F + pmean a b G.
Proof. by rewrite /pmean; field. Qed.

Lemma pmean_scale a b c (F : bool -> bool -> R) :
  pmean a b (fun x y => c * F x y) = c * pmean a b F.
Proof. by rewrite /pmean; field. Qed.

Lemma pmean_const a b c : pmean a b (fun _ _ => c) = c.
Proof. by rewrite /pmean; field. Qed.

Lemma plaw_add a b t (F G : bool -> bool -> R) :
  plaw a b t (fun x y => F x y + G x y) = plaw a b t F + plaw a b t G.
Proof. by rewrite /plaw -pmean_add; congr pmean; apply/funext => x; apply/funext => y; rewrite mulrDr. Qed.

Lemma pmean_swap a b (F : bool -> bool -> R) :
  pmean a b F = pmean b a (fun x y => F y x).
Proof. by rewrite /pmean; field. Qed.

Lemma plaw_swap a b t (F : bool -> bool -> R) :
  plaw a b t F = plaw b a t (fun x y => F y x).
Proof.
rewrite /plaw pmean_swap; congr pmean; apply/funext => x; apply/funext => y.
by rewrite [t * spin y * _]mulrAC [t * b * a]mulrAC.
Qed.

Lemma pair_signed_mean_lower a b t p q r :
  `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 10 ^+ 3 ->
  - (3 * 10 ^+ 4 * `|t| ^+ 3 * (p ^+ 2 + q ^+ 2)) <=
  pmean 0 0 (fun x y => pg1 b p r y * pg2 a q r x * psign a b t x y).
Proof.
move=> a1 b1 t3; have t4 : `|t| <= 1 / 4 by lra.
set K := 3 * 10 ^+ 4 * `|t| ^+ 3.
have K0 : 0 <= K by rewrite /K; apply: mulr_ge0; [lra | exact: exprn_ge0].
have hpt (x y : bool) :
    pg1 b p r y * pg2 a q r x * (spin x * spin y * ts_lead a b t) -
      K * (p ^+ 2 + q ^+ 2 + 8 * r ^+ 2) <=
    pg1 b p r y * pg2 a q r x * psign a b t x y.
  have hg := pair_grad_bound p q r x y a1 b1.
  have hs := psign_bound x y a1 b1 t4.
  have : `|pg1 b p r y * pg2 a q r x *
      (psign a b t x y - spin x * spin y * ts_lead a b t)| <=
      (p ^+ 2 + q ^+ 2 + 8 * r ^+ 2) * K.
    by rewrite normrM; apply: ler_pM; rewrite ?normr_ge0.
  rewrite mulrBr ler_norml => /andP[h _]; rewrite mulrC; lra.
have h0 : `|0 : R| <= 1 by rewrite normr0 ler01.
have := pmean_le h0 h0 hpt.
have -> : pmean 0 0 (fun x y => pg1 b p r y * pg2 a q r x *
    (spin x * spin y * ts_lead a b t) - K * (p ^+ 2 + q ^+ 2 + 8 * r ^+ 2)) =
    ts_lead a b t * r ^+ 2 - K * (p ^+ 2 + q ^+ 2 + 8 * r ^+ 2).
  by rewrite -(pair_cross_mean a b p q r) /pmean; field.
have hL := ts_lead_ge t a1 b1.
have h8 : 8 * K <= ts_lead a b t.
  apply: (le_trans _ hL); rewrite /K.
  have u0 := normr_ge0 t; move: t3 u0; set u := `|t| => t3 u0.
  have h2 : u ^+ 2 <= u / 10 ^+ 3 by rewrite expr2; nra.
  have u2 := exprn_ge0 2 u0.
  have h3 : u ^+ 3 <= u ^+ 2 / 10 ^+ 3 by rewrite exprS; nra.
  lra.
have r0 := sqr_ge0 r; have hr := ler_wpM2r r0 h8.
move: hL h8 hr; set L := ts_lead a b t => hL h8 hr h.
by apply: (le_trans _ h); lra.
Qed.

End two_spin_pair.

Section two_spin_energy.
Variable R : realType.
Implicit Types (a b t p q r : R) (x y : bool).

Lemma sqr_le1 a : `|a| <= 1 -> a ^+ 2 <= 1.
Proof. by move=> a1; rewrite -real_normK ?num_real // expr2 mulr_ile1. Qed.

Lemma sqr_le_norm a c : 0 <= c -> `|a| <= c -> a ^+ 2 <= c ^+ 2.
Proof. by move=> c0 ac; rewrite -real_normK ?num_real // ler_sqr ?nnegrE. Qed.

Lemma plaw_energy a b t p r : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  plaw a b t (fun x y => pcv a t y * pg1 b p r y ^+ 2) =
  (1 - a ^+ 2) * (1 - t ^+ 2) / (2 * (1 + t * a * b)) *
    ((1 + b) * pg1 b p r true ^+ 2 / (1 + t * a) +
     (1 - b) * pg1 b p r false ^+ 2 / (1 - t * a)).
Proof.
move=> a1 b1 t4.
have h1 : 1 + t * a != 0.
  by apply: lt0r_neq0; have := affine_half' true a1 t4; rewrite /= mulr1; lra.
have h2 : 1 - t * a != 0.
  by apply: lt0r_neq0; have := affine_half' false a1 t4; rewrite /= mulrN1; lra.
have ab1 : `|a * b| <= 1 by rewrite normrM; apply: mulr_ile1.
have h3 : 1 + t * a * b != 0.
  apply: lt0r_neq0; have := affine_half' true ab1 t4.
  by rewrite /= mulr1 mulrA; lra.
rewrite /plaw /pmean /pcv /pg1 /spin /= ?mulr1 ?mulrN1 ?mul1r.
by rewrite ?mulrN ?mulNr ?opprK; field.
Qed.

Lemma energy_bound_aux (A0 c u v X1 X2 P : R) : 0 <= A0 -> 3 / 8 <= c ->
  4 / 5 <= u -> 4 / 5 <= v -> 0 <= X1 -> 0 <= X2 -> 0 <= P ->
  2 * P <= X1 + X2 -> 3 / 5 * A0 * P <= A0 * c * (X1 * u + X2 * v).
Proof.
move=> A0p c3 u4 v4 X1p X2p Pp hP.
have h1 : 8 / 5 * P <= X1 * u + X2 * v by nra.
have h2 : 0 <= A0 * c by apply: mulr_ge0; lra.
have := ler_wpM2l h2 h1; have := mulr_ge0 A0p Pp; nra.
Qed.

Lemma plaw_energy_ge a b t p r : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  3 / 5 * (1 - a ^+ 2) * p ^+ 2 <=
  plaw a b t (fun x y => pcv a t y * pg1 b p r y ^+ 2).
Proof.
move=> a1 b1 t4; rewrite plaw_energy //.
have [ha1 ha2] : -1 <= a /\ a <= 1 by move: a1; rewrite ler_norml => /andP[].
have [hb1 hb2] : -1 <= b /\ b <= 1 by move: b1; rewrite ler_norml => /andP[].
have [ht1 ht2] : - (1 / 4) <= t /\ t <= 1 / 4 by move: t4; rewrite ler_norml => /andP[].
have hta : `|t * a| <= 1 / 4.
  by rewrite normrM; apply: le_trans t4; rewrite ler_piMr.
have [hta1 hta2] : - (1 / 4) <= t * a /\ t * a <= 1 / 4.
  by move: hta; rewrite ler_norml => /andP[].
have htab : `|t * a * b| <= 1 / 4.
  by rewrite normrM; apply: le_trans hta; rewrite ler_piMr.
have [htab1 htab2] : - (1 / 4) <= t * a * b /\ t * a * b <= 1 / 4.
  by move: htab; rewrite ler_norml => /andP[].
have tt : t ^+ 2 <= 1 / 16.
  by have := sqr_le_norm (_ : 0 <= 1 / 4) t4; rewrite expr2; lra.
set g1 := pg1 b p r true; set g2 := pg1 b p r false.
rewrite -[(1 - a ^+ 2) * (1 - t ^+ 2) / _]mulrA.
set c := (1 - t ^+ 2) / _.
set u := (1 + t * a)^-1; set v := (1 - t * a)^-1.
apply: energy_bound_aux.
- by have := sqr_le1 a1; lra.
- by rewrite /c ler_pdivlMr; lra.
- by rewrite /u -[(1 + t * a)^-1]mul1r ler_pdivlMr; lra.
- by rewrite /v -[(1 - t * a)^-1]mul1r ler_pdivlMr; lra.
- by apply: mulr_ge0; rewrite ?sqr_ge0 //; lra.
- by apply: mulr_ge0; rewrite ?sqr_ge0 //; lra.
- exact: sqr_ge0.
- rewrite /g1 /g2 /pg1 /spin.
  have hb : 0 <= 1 - b ^+ 2 by have := sqr_le1 b1; lra.
  by have := mulr_ge0 hb (sqr_ge0 r); lra.
Qed.

Lemma pprefactor_bounds a b t : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  0 <= pprefactor a b t /\
  pprefactor a b t <= 4 / 3 * ((1 - a ^+ 2) * (1 - b ^+ 2)).
Proof.
move=> a1 b1 t4.
have [ha1 ha2] : -1 <= a /\ a <= 1 by move: a1; rewrite ler_norml => /andP[].
have [hb1 hb2] : -1 <= b /\ b <= 1 by move: b1; rewrite ler_norml => /andP[].
have [ht1 ht2] : - (1 / 4) <= t /\ t <= 1 / 4 by move: t4; rewrite ler_norml => /andP[].
have ab1 : `|a * b| <= 1 by rewrite normrM; apply: mulr_ile1.
have htab : `|t * a * b| <= 1 / 4.
  by rewrite -mulrA normrM; apply: le_trans t4; rewrite ler_piMr.
have [htab1 htab2] : - (1 / 4) <= t * a * b /\ t * a * b <= 1 / 4.
  by move: htab; rewrite ler_norml => /andP[].
have tt : t ^+ 2 <= 1 / 16.
  by have := sqr_le_norm (_ : 0 <= 1 / 4) t4; rewrite expr2; lra.
have AB : 0 <= (1 - a ^+ 2) * (1 - b ^+ 2).
  by apply: mulr_ge0; [have := sqr_le1 a1 | have := sqr_le1 b1]; lra.
rewrite /pprefactor -[_ * (1 - t ^+ 2) / _]mulrA.
have Z0 : 0 < 1 + t * a * b by lra.
split.
  by apply: mulr_ge0 => //; apply: divr_ge0; lra.
rewrite [4 / 3 * _]mulrC; apply: ler_wpM2l => //.
by rewrite ler_pdivrMr //; have := sqr_ge0 t; lra.
Qed.

Lemma plaw_energy_ge' a b t q r : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 4 ->
  3 / 5 * (1 - b ^+ 2) * q ^+ 2 <=
  plaw a b t (fun x y => pcv b t x * pg2 a q r x ^+ 2).
Proof.
move=> a1 b1 t4; rewrite plaw_swap.
by have := plaw_energy_ge q r b1 a1 t4.
Qed.

Lemma pair_two_spin a b t p q r : `|a| <= 1 -> `|b| <= 1 -> `|t| <= 1 / 10 ^+ 3 ->
  - plaw a b t (fun x y => (t + 2 * t ^+ 2 * pcm a t y * pcm b t x) *
      pcv a t y * pcv b t x * pg1 b p r y * pg2 a q r x) -
  7 * 10 ^+ 4 * `|t| ^+ 3 * (plaw a b t (fun x y => pcv a t y * pg1 b p r y ^+ 2) +
                       plaw a b t (fun x y => pcv b t x * pg2 a q r x ^+ 2)) <=
  plaw a b t (fun x y => (spin x - pcm a t y) * pg1 b p r y *
    ((spin y - pcm b t x) * pg2 a q r x)).
Proof.
move=> a1 b1 t3; have t4 : `|t| <= 1 / 4 by lra.
have hA : 0 <= 1 - a ^+ 2 by have := sqr_le1 a1; lra.
have hB : 0 <= 1 - b ^+ 2 by have := sqr_le1 b1; lra.
have hAp := mulr_ge0 hA (sqr_ge0 p); have hBq := mulr_ge0 hB (sqr_ge0 q).
have hAb := mulr_ge0 hAp (sqr_ge0 b); have hBa := mulr_ge0 hBq (sqr_ge0 a).
have hpq : 0 <= p ^+ 2 + q ^+ 2 by rewrite addr_ge0 ?sqr_ge0.
have hF := pair_factorization p q r a1 b1 t4.
have hS := pair_signed_mean_lower p q r a1 b1 t3.
have [hP0 hP1] := pprefactor_bounds a1 b1 t4.
have hEi := plaw_energy_ge p r a1 b1 t4.
have hEj := plaw_energy_ge' q r a1 b1 t4.
move: hF hS hP0 hP1 hEi hEj.
set S := pmean 0 0 _; set P0 := pprefactor a b t.
set L := plaw a b t (fun x y => (spin x - pcm a t y) * _ * _).
set M := plaw a b t (fun x y => (t + _) * _ * _ * _ * _).
set Ei := plaw a b t (fun x y => pcv a t y * _).
set Ej := plaw a b t (fun x y => pcv b t x * _).
move=> hF hS hP0 hP1 hEi hEj.
move: hF hS hP0 hP1 hEi hEj.
clearbody S P0 L M Ei Ej.
move=> hF hS hP0 hP1 hEi hEj.
have hK3 : 0 <= `|t| ^+ 3 by rewrite exprn_ge0.
have K0 : 0 <= 3 * 10 ^+ 4 * `|t| ^+ 3 by apply: mulr_ge0 => //; lra.
have h1 := ler_wpM2l hP0 hS.
have h2 : P0 * (p ^+ 2 + q ^+ 2) <=
    4 / 3 * ((1 - a ^+ 2) * p ^+ 2 + (1 - b ^+ 2) * q ^+ 2).
  by apply: le_trans (ler_wpM2r hpq hP1) _; lra.
have h3 : (1 - a ^+ 2) * p ^+ 2 + (1 - b ^+ 2) * q ^+ 2 <= 5 / 3 * (Ei + Ej).
  by lra.
have hE : 0 <= Ei + Ej by lra.
have c43 : (0 : R) <= 4 / 3 by lra.
have h4 := ler_wpM2l K0 (le_trans h2 (ler_wpM2l c43 h3)).
have h5 : 3 * 10 ^+ 4 * `|t| ^+ 3 * (4 / 3 * (5 / 3 * (Ei + Ej))) <=
    7 * 10 ^+ 4 * `|t| ^+ 3 * (Ei + Ej).
  by have := mulr_ge0 hK3 hE; lra.
have hL : L = P0 * S - M by lra.
by rewrite hL; lra.
Qed.


End two_spin_energy.

Lemma spinT (R : realType) : spin true = 1 :> R.
Proof. by []. Qed.

Lemma spinF (R : realType) : spin false = -1 :> R.
Proof. by []. Qed.

Section ising_two_spin.
Variables (R : realType) (n : nat) (A : 'M[R]_n) (theta : 'cV[R]_n).
Hypothesis Asym : A \is symmetricmx.
Hypothesis Adiag : forall k, A k k = 0.
Local Notation cube := {ffun 'I_n -> bool}.
Local Notation w := (ising_weight A theta).
Local Notation E := (ising_mean A theta).
Implicit Types (x : cube) (i j : 'I_n) (f G : cube -> R).

Local Notation blk x i j c d := (spin_set (spin_set x i c) j d).

Definition bsum x i j G : R :=
  w (blk x i j true true) * G (blk x i j true true) +
  w (blk x i j true false) * G (blk x i j true false) +
  w (blk x i j false true) * G (blk x i j false true) +
  w (blk x i j false false) * G (blk x i j false false).

Lemma ising_mean_block i j G : i != j ->
  E G = (\sum_x bsum x i j G) / 4 / \sum_x w x.
Proof.
move=> ij; rewrite ising_meanE.
have Z0 : \sum_x w x != 0 := lt0r_neq0 (ising_Z_gt0 A theta).
suff -> : \sum_x bsum x i j G = 4 * \sum_x w x * G x by field.
pose H x := w (spin_set x i true) * G (spin_set x i true) +
  w (spin_set x i false) * G (spin_set x i false).
have e x : bsum x i j G = H (spin_set x j true) + H (spin_set x j false).
  by rewrite /bsum /H !(spin_setC _ _ _ ij); ring.
under eq_bigr do rewrite e.
rewrite sum_pair2 /H (sum_pair2 i (fun x => w x * G x)) /=.
by ring.
Qed.

Lemma block_set_i x i j c d c' : i != j ->
  spin_set (blk x i j c d) i c' = blk x i j c' d.
Proof. by move=> ij; rewrite spin_setC 1?eq_sym // spin_setK. Qed.

Lemma block_set_j x i j c d d' : spin_set (blk x i j c d) j d' = blk x i j c d'.
Proof. by rewrite spin_setK. Qed.

Lemma block_val_i x i j c d : i != j -> blk x i j c d i = c.
Proof. by move=> ij; rewrite spin_set_other // spin_set_same. Qed.

Lemma block_val_j x i j c d : blk x i j c d j = d.
Proof. exact: spin_set_same. Qed.

Lemma bsum_plaw x i j G K a b t (g : bool -> bool -> R) :
  1 + t * a * b != 0 ->
  (forall c d, w (blk x i j c d) =
     K * ((1 + a * spin c) * (1 + b * spin d) * (1 + t * spin c * spin d))) ->
  (forall c d, G (blk x i j c d) = g c d) ->
  bsum x i j G = 4 * K * (1 + t * a * b) * plaw a b t g.
Proof.
move=> h0 hw hg; rewrite /bsum !hw !hg /plaw /pmean /spin /spin /=.
by field.
Qed.

Lemma pcm_block_i (K a b t s : R) : K != 0 -> 1 + b * s != 0 -> 1 + t * a * s != 0 ->
  (K * ((1 + a) * (1 + b * s) * (1 + t * s)) -
     K * ((1 - a) * (1 + b * s) * (1 - t * s))) /
  (K * ((1 + a) * (1 + b * s) * (1 + t * s)) +
     K * ((1 - a) * (1 + b * s) * (1 - t * s))) =
  (a + t * s) / (1 + t * a * s).
Proof.
move=> K0 bs as0.
have -> : K * ((1 + a) * (1 + b * s) * (1 + t * s)) +
    K * ((1 - a) * (1 + b * s) * (1 - t * s)) =
    2 * K * (1 + b * s) * (1 + t * a * s) by ring.
have -> : K * ((1 + a) * (1 + b * s) * (1 + t * s)) -
    K * ((1 - a) * (1 + b * s) * (1 - t * s)) =
    2 * K * (1 + b * s) * (a + t * s) by ring.
by field.
Qed.

Lemma pcm_block_j (K a b t s : R) : K != 0 -> 1 + a * s != 0 -> 1 + t * b * s != 0 ->
  (K * ((1 + a * s) * (1 + b) * (1 + t * s)) -
     K * ((1 + a * s) * (1 - b) * (1 - t * s))) /
  (K * ((1 + a * s) * (1 + b) * (1 + t * s)) +
     K * ((1 + a * s) * (1 - b) * (1 - t * s))) =
  (b + t * s) / (1 + t * b * s).
Proof.
move=> K0 bs as0.
have -> : K * ((1 + a * s) * (1 + b) * (1 + t * s)) +
    K * ((1 + a * s) * (1 - b) * (1 - t * s)) =
    2 * K * (1 + a * s) * (1 + t * b * s) by ring.
have -> : K * ((1 + a * s) * (1 + b) * (1 + t * s)) -
    K * ((1 + a * s) * (1 - b) * (1 - t * s)) =
    2 * K * (1 + a * s) * (b + t * s) by ring.
by field.
Qed.

Lemma affine_pos (a s : R) : `|a| < 1 -> `|s| = 1 -> 0 < 1 + a * s.
Proof.
move=> a1 s1; have : `|a * s| < 1 by rewrite normrM s1 mulr1.
by rewrite ltr_norml => /andP[h _]; lra.
Qed.

Lemma div_le4 (Z K a b c d : R) : 0 < Z -> - b - K * (c + d) <= a ->
  - (b / 4 / Z) - K * (c / 4 / Z + d / 4 / Z) <= a / 4 / Z.
Proof.
move=> Z0 h; have Z1 : Z != 0 := lt0r_neq0 Z0.
have -> : - (b / 4 / Z) - K * (c / 4 / Z + d / 4 / Z) =
    (- b - K * (c + d)) / 4 / Z by field.
have i4 : (0 : R) < 4^-1 by rewrite invr_gt0 ltr0n.
have iZ : 0 < Z^-1 by rewrite invr_gt0.
by rewrite ler_pM2r // ler_pM2r.
Qed.

Lemma sum_combine (I : finType) (F1 F2 F3 F4 : I -> R) (K : R) :
  (forall k, - F2 k - K * (F3 k + F4 k) <= F1 k) ->
  - (\sum_k F2 k) - K * (\sum_k F3 k + \sum_k F4 k) <= \sum_k F1 k.
Proof.
move=> h.
have -> : - (\sum_k F2 k) - K * (\sum_k F3 k + \sum_k F4 k) =
    \sum_k (- F2 k - K * (F3 k + F4 k)).
  by rewrite sumrB sumrN -mulr_sumr big_split.
exact: ler_sum.
Qed.

Lemma scale_ineq (c K P1 P2 P3 P4 : R) : 0 <= c ->
  - P2 - K * (P3 + P4) <= P1 -> - (c * P2) - K * (c * P3 + c * P4) <= c * P1.
Proof.
move=> c0 h; have := ler_wpM2l c0 h.
by rewrite mulrBr mulrN mulrCA mulrDr.
Qed.

Local Notation m := (ising_cond_mean A theta).
Local Notation v := (ising_cond_var A theta).
Local Notation D := (ising_dproj A theta).

Lemma ising_two_spin_block x i j f : i != j ->
  `|sk_tanh (A i j)| <= 1 / 10 ^+ 3 ->
  - bsum x i j (fun y => (sk_tanh (A i j) + 2 * sk_tanh (A i j) ^+ 2 * m i y * m j y) *
       v i y * v j y * half_diff i f y * half_diff j f y) -
  7 * 10 ^+ 4 * `|sk_tanh (A i j)| ^+ 3 *
    (bsum x i j (fun y => v i y * half_diff i f y ^+ 2) +
     bsum x i j (fun y => v j y * half_diff j f y ^+ 2)) <=
  bsum x i j (fun y => D i f y * D j f y).
Proof.
move=> ij t3.
have [K [a [b [K0 a1 b1 hw]]]] := ising_weight_block theta Asym Adiag x ij.
move: t3 hw; set t := sk_tanh (A i j) => t3 hw.
have t4 : `|t| <= 1 / 4 by lra.
have a1' := ltW a1; have b1' := ltW b1.
have hab0 : 0 < 1 + t * a * b.
  have ab1 : `|a * b| <= 1 by rewrite normrM; apply: mulr_ile1.
  have := affine_half' true ab1 t4.
  by rewrite /= mulr1 mulrA; lra.
have hab : 1 + t * a * b != 0 := lt0r_neq0 hab0.
have K1 : K != 0 := lt0r_neq0 K0.
pose F c d := f (blk x i j c d).
pose r := (F true true - F true false - F false true + F false false) / 4.
pose p := (F true true + F true false - F false true - F false false) / 4 + r * b.
pose q := (F true true - F true false + F false true - F false false) / 4 + r * a.
have ta1 : `|t * a| < 1.
  by rewrite normrM; apply: le_lt_trans (_ : `|t| * 1 < 1); rewrite ?ler_wpM2l ?mulr1 //; lra.
have tb1 : `|t * b| < 1.
  by rewrite normrM; apply: le_lt_trans (_ : `|t| * 1 < 1); rewrite ?ler_wpM2l ?mulr1 //; lra.
have hmi c d : m i (blk x i j c d) = pcm a t d.
  rewrite /ising_cond_mean !block_set_i // !hw /pcm spinT spinF.
  rewrite !mulr1 !mulrN1 !mulNr.
  apply: pcm_block_i => //; apply: lt0r_neq0; apply: affine_pos => //;
    exact: spin_norm.
have hmj c d : m j (blk x i j c d) = pcm b t c.
  rewrite /ising_cond_mean !block_set_j !hw /pcm spinT spinF.
  rewrite !mulr1 !mulrN1.
  apply: pcm_block_j => //; apply: lt0r_neq0; apply: affine_pos => //;
    exact: spin_norm.
have hdi c d : half_diff i f (blk x i j c d) = pg1 b p r d.
  rewrite /half_diff !block_set_i // /pg1 /p /r /F /spin.
  by case: d => /=; field.
have hdj c d : half_diff j f (blk x i j c d) = pg2 a q r c.
  rewrite /half_diff !block_set_j /pg2 /q /r /F /spin.
  by case: c => /=; field.
have hvi c d : v i (blk x i j c d) = pcv a t d.
  by rewrite /ising_cond_var hmi pcv_eq.
have hvj c d : v j (blk x i j c d) = pcv b t c.
  by rewrite /ising_cond_var hmj pcv_eq.
have hDi c d : D i f (blk x i j c d) = (spin c - pcm a t d) * pg1 b p r d.
  by rewrite ising_dproj_eq block_val_i // hmi hdi.
have hDj c d : D j f (blk x i j c d) = (spin d - pcm b t c) * pg2 a q r c.
  by rewrite ising_dproj_eq block_val_j hmj hdj.
have hw' c d : w (blk x i j c d) =
    K * ((1 + a * spin c) * (1 + b * spin d) * (1 + t * spin c * spin d)) := hw c d.
rewrite (bsum_plaw (g := fun c d => (t + 2 * t ^+ 2 * pcm a t d * pcm b t c) *
    pcv a t d * pcv b t c * pg1 b p r d * pg2 a q r c) hab hw'); first by move=> c d; rewrite hmi hmj hvi hvj hdi hdj.
rewrite (bsum_plaw (g := fun c d => pcv a t d * pg1 b p r d ^+ 2) hab hw'); first by move=> c d; rewrite hvi hdi.
rewrite (bsum_plaw (g := fun c d => pcv b t c * pg2 a q r c ^+ 2) hab hw'); first by move=> c d; rewrite hvj hdj.
rewrite (bsum_plaw (g := fun c d => (spin c - pcm a t d) * pg1 b p r d *
    ((spin d - pcm b t c) * pg2 a q r c)) hab hw'); first by move=> c d; rewrite hDi hDj.
have hc : 0 < 4 * K * (1 + t * a * b) by rewrite !mulr_gt0.
apply: scale_ineq; first exact: ltW hc.
exact: (pair_two_spin p q r a1' b1' t3).
Qed.

Lemma ising_two_spin i j f : i != j -> `|sk_tanh (A i j)| <= 1 / 10 ^+ 3 ->
  - E (fun y => (sk_tanh (A i j) + 2 * sk_tanh (A i j) ^+ 2 * m i y * m j y) *
       v i y * v j y * half_diff i f y * half_diff j f y) -
  7 * 10 ^+ 4 * `|sk_tanh (A i j)| ^+ 3 *
    (E (fun y => v i y * half_diff i f y ^+ 2) +
     E (fun y => v j y * half_diff j f y ^+ 2)) <=
  E (fun y => D i f y * D j f y).
Proof.
move=> ij t3; rewrite !(ising_mean_block _ ij).
apply: div_le4; first exact: ising_Z_gt0.
by apply: sum_combine => x; exact: ising_two_spin_block.
Qed.

End ising_two_spin.
