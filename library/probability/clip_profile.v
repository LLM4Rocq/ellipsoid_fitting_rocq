From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import variational.


(**md**************************************************************************)
(* # Clipped profiles: a constrained scalar variational problem               *)
(*                                                                            *)
(* For a law mu on the line, symmetric with a finite second moment            *)
(* sigma2 = E X^2, reals c > -1 and C >= 1, and a profile q, let              *)
(*   V_c(q) = 2 E[X q(X)] - E[q(X)^2] - c (E q(X))^2.                         *)
(* A profile is admissible for C when it is measurable with t <= q <= C t     *)
(* for some t >= 0. For a real a and t >= 0, the clipped profile              *)
(*   q_{a,t}(x) = min (max (x - a) t) (C t)                                   *)
(* is admissible; with l = t + a and u = C t + a it is                        *)
(* t + (x - l)_+ - (x - u)_+, and q_{a,t}(x) is the point of [t, C t]         *)
(* closest to x - a. m and s are the upper moments of variational.v.          *)
(*                                                                            *)
(* Main results:                                                              *)
(* - clip_first_order: under the balance m(-l) = C m(u), the residual         *)
(*   w(x) = x - a - q_{a,t}(x) has E[w (q - q_{a,t})] <= 0 for every          *)
(*   admissible q; clip_residual_profile: E[w q_{a,t}] = 0.                   *)
(* - clip_optimal: if moreover a = c E q_{a,t} (a fixed point), q_{a,t}       *)
(*   maximizes V_c over the admissible profiles. clip_objective_profile:      *)
(*   V_c(q_{a,t}) = E[X q_{a,t}(X)]; clip_objective_radial:                   *)
(*   V_c(q_{a,t}) = E[q_{a,t}(X)^2] + c (E q_{a,t}(X))^2; clip_objectiveE:    *)
(*   V_c(q_{a,t}) = J(l) - J(u), with J(w) = s(w) + w m(w).                   *)
(* - clip_energy_shiftE: s(-t - a) + s(C t + a) = E (X - a - q_{a,t}(X))^2,   *)
(*   the mean squared distance from X - a to [t, C t].                        *)
(* - The dual form, with clip_dual mu c C b the function                      *)
(*   D(b) = sigma2 + c (1 + c) b^2 - inf_(t' >= 0) (s(-t' - c b)              *)
(*   + s(C t' + c b)), under the balance and the fixed point:                 *)
(*   clip_dual_opt: D(E q_{a,t}) = V_c(q_{a,t});                              *)
(*   clip_dual_le: D(b) <= V_c(q_{a,t}) for every b if c <= 0;                *)
(*   clip_dual_ge: V_c(q_{a,t}) <= D(b) for every b if c >= 0;                *)
(*   clip_dual_window: 0 <= E q_{a,t} and                                     *)
(*   min(1, 1 + c)^2 (E q_{a,t})^2 <= sigma2.                                 *)
(* - clip_objective_add: for bounded measurable q and h, V_c(q + h) is        *)
(*   V_c(q) + 2 E[(X - c E q(X) - q(X)) h(X)] - E[h(X)^2] - c (E h(X))^2;     *)
(*   clip_admissible_le: a profile admissible for C is admissible for every   *)
(*   C' >= C.                                                                 *)
(* - Tools: clip_profile_mean, E q_{a,t} = t + m(l) - m(u);                   *)
(*   clip_energy_shift_min, t minimizes t' |-> s(-t' - a) + s(C t' + a);      *)
(*   clip_dual_profile, clip_dual_lower; clip_res_sqE, the expansion of       *)
(*   E (X - a - f(X))^2 for a bounded measurable f; the integrability of      *)
(*   bounded measurable functions and of their products with x.               *)
(*                                                                            *)
(* ```                                                                        *)
(*         clip_profile C a t x == min (max (x - a) t) (C t)                  *)
(*        clip_admissible C q == q measurable, t <= q <= C t, some t >= 0     *)
(*      clip_objective mu c q == 2 E[X q] - E[q^2] - c (E q)^2                *)
(*   clip_energy_shift mu C a t == s(-t - a) + s(C t + a)                     *)
(*         clip_dual mu c C b == E X^2 + c (1 + c) b^2                        *)
(*                 - inf_(t >= 0) clip_energy_shift mu C (c b) t              *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section clip_profile_def.
Context {R : realType}.

(* The clipped profile x |-> min (max (x - a) t) (C t). *)
Definition clip_profile (C a t : R) (x : R) : R :=
  Num.min (Num.max (x - a) t) (C * t).

(* The admissible profiles: measurable, with t <= q <= C t for some
   t >= 0. *)
Definition clip_admissible (C : R) : set (measurableTypeR R -> R) :=
  [set q | measurable_fun [set: measurableTypeR R] q /\
     exists2 t : R, 0 <= t & forall x, t <= q x <= C * t].

(* A profile admissible for C is admissible for every C' >= C. *)
Lemma clip_admissible_le (C C' : R) (q : measurableTypeR R -> R) :
  C <= C' -> clip_admissible C q -> clip_admissible C' q.
Proof.
move=> CC [mq [t t0 hq]]; split => //; exists t => // x.
have /andP[h1 h2] := hq x; rewrite h1 /=.
by apply: le_trans h2 _; rewrite ler_wpM2r.
Qed.

End clip_profile_def.

Section clip_objective_def.
Context {R : realType} (mu : probability (measurableTypeR R) R).

(* V_c(q) = 2 E[X q(X)] - E[q(X)^2] - c (E q(X))^2. *)
Definition clip_objective (c : R) (q : measurableTypeR R -> R) : R :=
  2 * \int[mu]_x ((x : R) * q x) - \int[mu]_x (q x ^+ 2)
  - c * (\int[mu]_x q x) ^+ 2.

(* s(-t - a) + s(C t + a), the mean squared distance from X - a to
   [t, C t] for a symmetric law. *)
Definition clip_energy_shift (C a t : R) : R :=
  upper_moment mu 2 (- t - a) + upper_moment mu 2 (C * t + a).

(* D(b) = E X^2 + c (1 + c) b^2 - inf_(t >= 0) (s(-t - c b) + s(C t + c b)). *)
Definition clip_dual (c C b : R) : R :=
  \int[mu]_x ((x : R) ^+ 2) + c * (1 + c) * b ^+ 2
  - inf [set clip_energy_shift C (c * b) t | t in [set t : R | 0 <= t]].

End clip_objective_def.

Section clip_profile_facts.
Context {R : realType}.
Variables (C a t : R).
Hypotheses (C1 : 1 <= C) (t0 : 0 <= t).

Local Notation q := (clip_profile C a t).

Lemma clip_profile_ct : t <= C * t.
Proof. by rewrite -[X in X <= _]mul1r ler_wpM2r. Qed.

Lemma clip_profile_bounds x : t <= q x <= C * t.
Proof.
rewrite /clip_profile; have ct := clip_profile_ct.
apply/andP; split.
  by rewrite le_min ct le_max lexx orbT.
by rewrite ge_min lexx orbT.
Qed.

(* q(x) = t + (x - (t + a))_+ - (x - (C t + a))_+. *)
Lemma clip_profileE x : q x =
  t + Num.max (x - (t + a)) 0 - Num.max (x - (C * t + a)) 0.
Proof.
rewrite /clip_profile; have ct := clip_profile_ct.
case: (leP (x - a) t) => h1; case: (leP (x - (t + a)) 0) => h2;
  case: (leP (x - (C * t + a)) 0) => h3; rewrite ?(min_idPl ct) //;
  try (case: (leP (x - a) (C * t)) => h4); lra.
Qed.

(* The residual x - a - q(x) is (x - u)_+ - (ell - x)_+. *)
Lemma clip_residualE x : x - a - q x =
  Num.max (x - (C * t + a)) 0 - Num.max ((t + a) - x) 0.
Proof.
rewrite clip_profileE; have ct := clip_profile_ct.
case: (leP (x - (t + a)) 0) => h1; case: (leP (x - (C * t + a)) 0) => h2;
  case: (leP ((t + a) - x) 0) => h3; lra.
Qed.

Lemma measurable_clip_profile :
  measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => q x).
Proof.
rewrite /clip_profile; apply: measurable_minr; last exact: measurable_cst.
apply: measurable_maxr; last exact: measurable_cst.
by apply: measurable_funB => //; exact: measurable_cst.
Qed.

Lemma clip_profile_admissible :
  clip_admissible C (fun x : measurableTypeR R => q x).
Proof.
split; first exact: measurable_clip_profile.
by exists t => // x; exact: clip_profile_bounds.
Qed.

End clip_profile_facts.

Section clip_integrals.
Context {R : realType} (mu : probability (measurableTypeR R) R).
Hypothesis mu2 :
  mu.-integrable [set: measurableTypeR R] (EFin \o (fun x => (x : R) ^+ 2)).
Hypothesis musym : forall A : set (measurableTypeR R), measurable A ->
  mu ((fun x => - x) @^-1` A) = mu A.

Local Notation m := (upper_moment mu 1).
Local Notation s := (upper_moment mu 2).
Local Notation integrable f :=
  (mu.-integrable [set: measurableTypeR R] (EFin \o f)).

Let integrableZ_R (k : R) (f : measurableTypeR R -> R) :
  integrable f -> integrable (fun x => k * f x).
Proof.
move=> fi; have := integrableZl measurableT k fi.
by apply: eq_integrable => // x _; rewrite /= EFinM.
Qed.

Let integrableB_R (f g : measurableTypeR R -> R) :
  integrable f -> integrable g -> integrable (fun x => f x - g x).
Proof.
move=> fi gi; have := integrableB measurableT fi gi.
by apply: eq_integrable => // x _; rewrite /= EFinB.
Qed.

Let integrableD_R (f g : measurableTypeR R -> R) :
  integrable f -> integrable g -> integrable (fun x => f x + g x).
Proof.
move=> fi gi; have := integrableD measurableT fi gi.
by apply: eq_integrable => // x _; rewrite /= EFinD.
Qed.

(* Bounded measurable functions are integrable, and so is their product
   with the identity. *)
Lemma clip_integrable_bounded (f : measurableTypeR R -> R) (B : R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, `|f x| <= B) ->
  integrable f.
Proof.
move=> mf fB; apply: (integrable_quad_bound mu2 (a := B) (b := 0)) => //.
by move=> x; rewrite mul0r addr0.
Qed.

Lemma clip_integrable_id_bounded (f : measurableTypeR R -> R) (B : R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, `|f x| <= B) ->
  integrable (fun x => (x : R) * f x).
Proof.
move=> mf fB; have B0 : 0 <= B by apply: le_trans (fB 0); exact: normr_ge0.
apply: (integrable_quad_bound mu2 (a := B) (b := B)).
  by apply: measurable_funM => //; exact: measurable_id.
move=> x; rewrite normrM.
have hx : `|(x : R)| <= 1 + (x : R) ^+ 2.
  rewrite -[X in _ <= 1 + X]real_normK ?num_real //.
  by have := sqr_ge0 (`|(x : R)| - 1); nra.
by have := fB x; have := normr_ge0 (f x); have := normr_ge0 (x : R); nra.
Qed.

(* E (w - X)_+ = m(-w) for a symmetric law. *)
Lemma upper_moment1_reflect w :
  \int[mu]_x Num.max (w - (x : R)) 0 = m (- w).
Proof.
rewrite /upper_moment.
have i1 := integrable_upper_pow mu2 (- w) (isT : (1 <= 2)%N).
rewrite -(Rintegral_sym musym i1).
by apply: eq_Rintegral => x _; rewrite expr1 opprK addrC.
Qed.

Lemma integrable_upper1 w : integrable (fun x => Num.max ((x : R) - w) 0).
Proof.
have := integrable_upper_pow mu2 w (isT : (1 <= 2)%N).
by apply: eq_integrable => // x _ /=; rewrite expr1.
Qed.

Lemma integrable_upper1_reflect w :
  integrable (fun x => Num.max (w - (x : R)) 0).
Proof.
have := integrable_sym musym (integrable_upper1 (- w)).
by apply: eq_integrable => // x _ /=; rewrite opprK addrC.
Qed.

Lemma clip_integrable_sq (f : measurableTypeR R -> R) (B : R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, `|f x| <= B) ->
  integrable (fun x => f x ^+ 2).
Proof.
move=> mf fB; apply: (clip_integrable_bounded (B := B ^+ 2)).
  exact: measurable_funX.
move=> x; rewrite normrX lerXn2r ?nnegrE ?normr_ge0 //.
by apply: le_trans (normr_ge0 _) (fB x).
Qed.

Lemma clip_integrable_mul (f g : measurableTypeR R -> R) (B B' : R) :
  measurable_fun [set: measurableTypeR R] f ->
  measurable_fun [set: measurableTypeR R] g ->
  (forall x, `|f x| <= B) -> (forall x, `|g x| <= B') ->
  integrable (fun x => f x * g x).
Proof.
move=> mf mg fB gB; apply: (clip_integrable_bounded (B := B * B')).
  exact: measurable_funM.
by move=> x; rewrite normrM ler_pM ?normr_ge0.
Qed.

(* The residual x - a - f(x) of a bounded measurable f, times a bounded
   measurable g, and squared. *)
Lemma clip_integrable_res_mul (a : R) (f g : measurableTypeR R -> R)
    (B B' : R) :
  measurable_fun [set: measurableTypeR R] f ->
  measurable_fun [set: measurableTypeR R] g ->
  (forall x, `|f x| <= B) -> (forall x, `|g x| <= B') ->
  integrable (fun x => ((x : R) - a - f x) * g x).
Proof.
move=> mf mg fB gB.
have B'0 : 0 <= B' by apply: le_trans (gB 0); exact: normr_ge0.
apply: (integrable_quad_bound mu2 (a := B' * (1 + `|a| + B)) (b := B')).
  apply: measurable_funM => //.
  by apply: measurable_funB => //; apply: measurable_funB.
move=> x; rewrite normrM.
have h2 : `|(x : R) - a - f x| <= `|(x : R)| + `|a| + B.
  apply: le_trans (ler_normB _ _) _; apply: lerD => //.
  exact: ler_normB.
have hx : `|(x : R)| <= 1 + (x : R) ^+ 2.
  rewrite -[X in _ <= 1 + X]real_normK ?num_real //.
  by have := sqr_ge0 (`|(x : R)| - 1); nra.
have := gB x; have := normr_ge0 (g x); have := normr_ge0 ((x : R) - a - f x).
have := normr_ge0 (x : R); have := normr_ge0 a; nra.
Qed.

Lemma clip_integrable_res_sq (a : R) (f : measurableTypeR R -> R) (B : R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, `|f x| <= B) ->
  integrable (fun x => ((x : R) - a - f x) ^+ 2).
Proof.
move=> mf fB.
apply: (integrable_quad_bound mu2 (a := 2 * (`|a| + B) ^+ 2) (b := 2)).
  apply: measurable_funX.
  by apply: measurable_funB => //; apply: measurable_funB.
move=> x; rewrite normrX.
have h2 : `|(x : R) - a - f x| <= `|(x : R)| + (`|a| + B).
  apply: le_trans (ler_normB _ _) _; rewrite addrA; apply: lerD => //.
  exact: ler_normB.
have := normr_ge0 ((x : R) - a - f x); have := normr_ge0 (x : R).
have := sqr_ge0 (`|(x : R)| - (`|a| + B)).
rewrite -[(x : R) ^+ 2]real_normK ?num_real //.
nra.
Qed.

(* E (X - a - f(X))^2, expanded, for a bounded measurable f. *)
Lemma clip_res_sqE (a : R) (f : measurableTypeR R -> R) (B : R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, `|f x| <= B) ->
  \int[mu]_x (((x : R) - a - f x) ^+ 2) =
  \int[mu]_x ((x : R) ^+ 2) + a ^+ 2 - 2 * \int[mu]_x ((x : R) * f x)
  + 2 * a * \int[mu]_x f x + \int[mu]_x (f x ^+ 2).
Proof.
move=> mf fB.
have ix := integrable_idR mu2.
have i1 := clip_integrable_bounded mf fB.
have ixf := clip_integrable_id_bounded mf fB.
have if2 := clip_integrable_sq mf fB.
have ic : integrable (fun _ : measurableTypeR R => a ^+ 2).
  apply: (clip_integrable_bounded (B := `|a ^+ 2|));
    [exact: measurable_cst | by move=> x].
have j1 := integrableB_R mu2 (integrableZ_R (2 * a) ix).
have j2 := integrableD_R j1 ic.
have j3 := integrableB_R j2 (integrableZ_R 2 ixf).
have j4 := integrableD_R j3 (integrableZ_R (2 * a) i1).
have iax := integrableZ_R (2 * a) ix.
have i2xf := integrableZ_R 2 ixf.
have i2af := integrableZ_R (2 * a) i1.
have -> : (fun x : measurableTypeR R => ((x : R) - a - f x) ^+ 2) =
    (fun x => (((((x : R) ^+ 2 - 2 * a * (x : R)) + a ^+ 2)
               - 2 * ((x : R) * f x)) + 2 * a * f x) + f x ^+ 2).
  by apply/funext => x; ring.
rewrite RintegralD // RintegralD // RintegralB // RintegralD // RintegralB //.
rewrite Rintegral_prob_cst !RintegralZl // (Rintegral_id_sym mu2 musym).
by rewrite mulr0 subr0.
Qed.

Lemma clip_admissible_bounded (C : R) (q' : measurableTypeR R -> R) :
  clip_admissible C q' -> exists2 B : R, 0 <= B & forall x, `|q' x| <= B.
Proof.
move=> [_ [t' t'0 hq]]; exists (C * t') => [|x].
  by have /andP[h1 h2] := hq 0; apply: le_trans t'0 (le_trans h1 h2).
have /andP[h1 h2] := hq x.
by rewrite ger0_norm // (le_trans t'0 h1).
Qed.

Lemma clip_profile_bounded (C a t : R) : 1 <= C -> 0 <= t ->
  exists2 B : R, 0 <= B & forall x, `|clip_profile C a t x| <= B.
Proof.
move=> C1 t0.
exact: (clip_admissible_bounded (clip_profile_admissible a C1 t0)).
Qed.

(* E q_{a,t} = t + m(t + a) - m(C t + a). *)
Lemma clip_profile_mean (C a t : R) : 1 <= C -> 0 <= t ->
  \int[mu]_x clip_profile C a t x = t + m (t + a) - m (C * t + a).
Proof.
move=> C1 t0.
have ic : integrable (fun _ : measurableTypeR R => t).
  apply: (clip_integrable_bounded (B := `|t|));
    [exact: measurable_cst | by move=> x].
have il := integrable_upper1 (t + a).
have iu := integrable_upper1 (C * t + a).
have icl := integrableD_R ic il.
have -> : (fun x : measurableTypeR R => clip_profile C a t x) =
    (fun x => (t + Num.max ((x : R) - (t + a)) 0) -
              Num.max ((x : R) - (C * t + a)) 0).
  by apply/funext => x; rewrite clip_profileE.
by rewrite RintegralB // RintegralD // Rintegral_prob_cst.
Qed.

(* q_{a,t}(x) is the point of [t, C t] closest to x - a. *)
Lemma clip_profile_closest (C a t : R) (x z : R) : 1 <= C -> 0 <= t ->
  t <= z <= C * t -> (x - a - clip_profile C a t x) ^+ 2 <= (x - a - z) ^+ 2.
Proof.
move=> C1 t0 /andP[z1 z2]; rewrite /clip_profile.
have ct := clip_profile_ct C1 t0.
case: (leP (x - a) t) => h1.
  rewrite (min_idPl ct).
  have d1 : 0 <= z - t by rewrite subr_ge0.
  have d2 : 0 <= t - (x - a) by rewrite subr_ge0.
  by have := mulr_ge0 d1 d1; have := mulr_ge0 d1 d2; nra.
case: (leP (x - a) (C * t)) => h2.
  by rewrite subrr expr0n /= sqr_ge0.
have d1 : 0 <= C * t - z by rewrite subr_ge0.
have d2 : 0 <= (x - a) - C * t by rewrite subr_ge0 ltW.
by have := mulr_ge0 d1 d1; have := mulr_ge0 d1 d2; nra.
Qed.

(* s(-t - a) + s(C t + a) = E (X - a - q_{a,t}(X))^2. *)
Lemma clip_energy_shiftE (C a t : R) : 1 <= C -> 0 <= t ->
  clip_energy_shift mu C a t =
  \int[mu]_x (((x : R) - a - clip_profile C a t x) ^+ 2).
Proof.
move=> C1 t0.
have i2u := integrable_upper_pow mu2 (C * t + a) (isT : (2 <= 2)%N).
have i2l' := integrable_upper_pow mu2 (- t - a) (isT : (2 <= 2)%N).
have i2l : integrable (fun x => Num.max ((t + a) - (x : R)) 0 ^+ 2).
  have := integrable_sym musym i2l'.
  apply: eq_integrable => // x _ /=; congr (EFin (_ ^+ 2)).
  by congr (Num.max _ 0); ring.
have ct := clip_profile_ct C1 t0.
have -> : (fun x : measurableTypeR R =>
      ((x : R) - a - clip_profile C a t x) ^+ 2) =
    (fun x => Num.max ((t + a) - (x : R)) 0 ^+ 2 +
              Num.max ((x : R) - (C * t + a)) 0 ^+ 2).
  apply/funext => x; rewrite clip_residualE //.
  case: (leP ((x : R) - (C * t + a)) 0) => h1;
    case: (leP ((t + a) - (x : R)) 0) => h2; rewrite ?expr0n /=;
    first [ring | lra].
rewrite RintegralD // /clip_energy_shift; congr (_ + _).
have hs := Rintegral_sym musym i2l'; rewrite /= in hs.
rewrite /upper_moment -hs.
by apply: eq_Rintegral => x _; congr (_ ^+ 2); congr (Num.max _ 0); ring.
Qed.

Lemma clip_energy_shift_ge0 (C a t : R) : 0 <= clip_energy_shift mu C a t.
Proof. by rewrite /clip_energy_shift addr_ge0 // upper_moment_ge0. Qed.

(* D(b) without the infimum, at a clipped profile:
   E X^2 + c (1 + c) b^2 - (s(-t - c b) + s(C t + c b))
   = V_c(q_{c b, t}) + c (E q_{c b, t} - b)^2. *)
Lemma clip_dual_profile (c C b t : R) : 1 <= C -> 0 <= t ->
  \int[mu]_x ((x : R) ^+ 2) + c * (1 + c) * b ^+ 2
  - clip_energy_shift mu C (c * b) t =
  clip_objective mu c (clip_profile C (c * b) t)
  + c * (\int[mu]_x clip_profile C (c * b) t x - b) ^+ 2.
Proof.
move=> C1 t0.
have [B B0 qB] := clip_profile_bounded (c * b) C1 t0.
have mq := measurable_clip_profile C (c * b) t.
rewrite clip_energy_shiftE // (clip_res_sqE (c * b) mq qB) /clip_objective.
move: (\int[mu]_x ((x : R) ^+ 2))
  (\int[mu]_x ((x : R) * clip_profile C (c * b) t x))
  (\int[mu]_x clip_profile C (c * b) t x)
  (\int[mu]_x (clip_profile C (c * b) t x ^+ 2)) => S X M Q.
by ring.
Qed.

(* The expansion of V_c around a bounded measurable q, in a bounded
   measurable direction h: V_c(q + h) = V_c(q)
   + 2 E[(X - c E q - q(X)) h(X)] - (E h^2 + c (E h)^2). *)
Lemma clip_objective_add (c : R) (q h : measurableTypeR R -> R) (B B' : R) :
  measurable_fun [set: measurableTypeR R] q ->
  measurable_fun [set: measurableTypeR R] h ->
  (forall x, `|q x| <= B) -> (forall x, `|h x| <= B') ->
  clip_objective mu c (fun x => q x + h x) =
  clip_objective mu c q
  + 2 * \int[mu]_x (((x : R) - c * \int[mu]_y q y - q x) * h x)
  - (\int[mu]_x (h x ^+ 2) + c * (\int[mu]_x h x) ^+ 2).
Proof.
move=> mq mh qB hB.
have iq := clip_integrable_bounded mq qB.
have ih := clip_integrable_bounded mh hB.
have ixq := clip_integrable_id_bounded mq qB.
have ixh := clip_integrable_id_bounded mh hB.
have iq2 := clip_integrable_sq mq qB.
have ih2 := clip_integrable_sq mh hB.
have iqh := clip_integrable_mul mq mh qB hB.
have i2qh := integrableZ_R 2 iqh.
have iq2qh := integrableD_R iq2 i2qh.
set a := c * \int[mu]_y q y.
have iah := integrableZ_R a ih.
have ixah := integrableB_R ixh iah.
have J1 : \int[mu]_x ((x : R) * (q x + h x)) =
    \int[mu]_x ((x : R) * q x) + \int[mu]_x ((x : R) * h x).
  by rewrite -RintegralD //; apply: eq_Rintegral => x _ /=; ring.
have J2 : \int[mu]_x ((q x + h x) ^+ 2) =
    \int[mu]_x (q x ^+ 2) + 2 * \int[mu]_x (q x * h x) + \int[mu]_x (h x ^+ 2).
  rewrite -RintegralZl // -RintegralD // -RintegralD //.
  by apply: eq_Rintegral => x _ /=; ring.
have J3 : \int[mu]_x (q x + h x) = \int[mu]_x q x + \int[mu]_x h x.
  by rewrite RintegralD.
have J4 : \int[mu]_x (((x : R) - a - q x) * h x) =
    \int[mu]_x ((x : R) * h x) - a * \int[mu]_x h x - \int[mu]_x (q x * h x).
  have -> : (fun x : measurableTypeR R => ((x : R) - a - q x) * h x) =
      (fun x => ((x : R) * h x - a * h x) - q x * h x).
    by apply/funext => x; ring.
  by rewrite RintegralB // RintegralB // RintegralZl.
rewrite /clip_objective J1 J2 J3 J4 /a.
by ring.
Qed.

(* 1. The first-order inequality under the balance m(-ell) = C m(u). *)

Section clip_first_order.
Variables (C a t : R).
Hypotheses (C1 : 1 <= C) (t0 : 0 <= t).
Hypothesis balance : m (- (t + a)) = C * m (C * t + a).

Local Notation q := (clip_profile C a t).

Let C0 : 0 <= C := le_trans ler01 C1.

(* E[w (q' - q)] <= 0 for every admissible q', w(x) = x - a - q(x). *)
Lemma clip_first_order (q' : measurableTypeR R -> R) : clip_admissible C q' ->
  \int[mu]_x ((x - a - q x) * (q' x - q x)) <= 0.
Proof.
move=> hq'; have [_ [t' t'0 hb]] := hq'.
have [B B0 qB] := clip_admissible_bounded hq'.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have mq := measurable_clip_profile C a t.
have mq' : measurable_fun [set: measurableTypeR R] q' by case: hq'.
(* the pointwise bound: w (q' - q) <= (t' - t) (C (x - u)_+ - (ell - x)_+) *)
pose g x := (t' - t) * (C * Num.max ((x : R) - (C * t + a)) 0
                        - Num.max ((t + a) - (x : R)) 0).
have iu := integrable_upper1 (C * t + a).
have il := integrable_upper1_reflect (t + a).
have iCu := integrableZ_R C iu.
have iB := integrableB_R iCu il.
have ig : integrable g := integrableZ_R (t' - t) iB.
have Eg : \int[mu]_x g x = 0.
  rewrite /g RintegralZl // RintegralB // RintegralZl //.
  rewrite upper_moment1_reflect.
  have -> : \int[mu]_x Num.max ((x : R) - (C * t + a)) 0 = m (C * t + a).
    by rewrite /upper_moment; apply: eq_Rintegral => x _; rewrite expr1.
  by rewrite balance subrr mulr0.
rewrite -Eg; apply: le_Rintegral => //.
  apply: (integrable_quad_bound mu2 (a := (B + B') * (1 + `|a| + B'))
    (b := B + B')).
    apply: measurable_funM; last exact: measurable_funB.
    by apply: measurable_funB => //; apply: measurable_funB.
  move=> x; rewrite normrM.
  have h1 : `|q' x - q x| <= B + B'.
    by apply: le_trans (ler_normB _ _) _; apply: lerD.
  have h2 : `|(x : R) - a - q x| <= `|(x : R)| + `|a| + B'.
    apply: le_trans (ler_normB _ _) _; apply: lerD => //.
    exact: ler_normB.
  have hx : `|(x : R)| <= 1 + (x : R) ^+ 2.
    rewrite -[X in _ <= 1 + X]real_normK ?num_real //.
    by have := sqr_ge0 (`|(x : R)| - 1); nra.
  have := normr_ge0 (q' x - q x); have := normr_ge0 ((x : R) - a - q x).
  have := normr_ge0 (x : R); have := normr_ge0 a; nra.
move=> x _; rewrite /g clip_residualE // clip_profileE //.
have /andP[l1 l2] := hb x.
have ct := clip_profile_ct C1 t0.
case: (leP ((x : R) - (C * t + a)) 0) => h1;
  case: (leP ((t + a) - (x : R)) 0) => h2;
  case: (leP ((x : R) - (t + a)) 0) => h3;
  rewrite ?subr0 ?sub0r ?addr0 ?mulr0 ?mul0r; nra.
Qed.

(* E[w q] = 0. *)
Lemma clip_residual_profile : \int[mu]_x ((x - a - q x) * q x) = 0.
Proof.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have e : (fun x : measurableTypeR R => ((x : R) - a - q x) * q x) =
    (fun x => C * t * Num.max ((x : R) - (C * t + a)) 0
              - t * Num.max ((t + a) - (x : R)) 0).
  apply/funext => x; rewrite clip_residualE // clip_profileE //.
  have ct := clip_profile_ct C1 t0.
  case: (leP ((x : R) - (C * t + a)) 0) => h1;
    case: (leP ((t + a) - (x : R)) 0) => h2;
    case: (leP ((x : R) - (t + a)) 0) => h3; nra.
have iu := integrable_upper1 (C * t + a).
have il := integrable_upper1_reflect (t + a).
have i1 := integrableZ_R (C * t) iu.
have i2 := integrableZ_R t il.
rewrite e RintegralB // !RintegralZl // upper_moment1_reflect balance.
have -> : \int[mu]_x Num.max ((x : R) - (C * t + a)) 0 = m (C * t + a).
  by rewrite /upper_moment; apply: eq_Rintegral => x _; rewrite expr1.
by ring.
Qed.

(* 2. Optimality and value, under the fixed point a = c E q. *)

Variable c : R.
Hypothesis c1 : -1 < c.
Hypothesis fixpt : a = c * \int[mu]_x q x.

Let bounded_sq (f : measurableTypeR R -> R) (B : R) :
  measurable_fun [set: measurableTypeR R] f -> (forall x, `|f x| <= B) ->
  integrable (fun x => f x ^+ 2).
Proof.
move=> mf fB; apply: (clip_integrable_bounded (B := B ^+ 2)).
  exact: measurable_funX.
move=> x; rewrite normrX lerXn2r ?nnegrE ?normr_ge0 //.
by apply: le_trans (normr_ge0 _) (fB x).
Qed.

Let bounded_mul (f g : measurableTypeR R -> R) (B B' : R) :
  measurable_fun [set: measurableTypeR R] f ->
  measurable_fun [set: measurableTypeR R] g ->
  (forall x, `|f x| <= B) -> (forall x, `|g x| <= B') ->
  integrable (fun x => f x * g x).
Proof.
move=> mf mg fB gB; apply: (clip_integrable_bounded (B := B * B')).
  exact: measurable_funM.
move=> x; rewrite normrM ler_pM ?normr_ge0 //.
Qed.

(* E[X q] = E[q^2] + c (E q)^2, so V_c(q) = E[X q]. *)
Lemma clip_objective_profile :
  clip_objective mu c q = \int[mu]_x ((x : R) * q x).
Proof.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have mq := measurable_clip_profile C a t.
have iq := clip_integrable_bounded mq qsB.
have ixq := clip_integrable_id_bounded mq qsB.
have iq2 := bounded_sq mq qsB.
have iaq := integrableZ_R a iq.
have ixaq := integrableB_R ixq iaq.
have e : \int[mu]_x (((x : R) - a - q x) * q x) =
    \int[mu]_x ((x : R) * q x) - a * \int[mu]_x q x - \int[mu]_x (q x ^+ 2).
  have -> : (fun x : measurableTypeR R => ((x : R) - a - q x) * q x) =
      (fun x => ((x : R) * q x - a * q x) - q x ^+ 2).
    by apply/funext => x; ring.
  by rewrite RintegralB // RintegralB // RintegralZl.
have h := clip_residual_profile; rewrite e in h.
rewrite /clip_objective; move: h (fixpt).
move: (\int[mu]_x ((x : R) * q x)) (\int[mu]_x q x) (\int[mu]_x (q x ^+ 2)).
move=> X M Q h fp; rewrite fp in h.
by rewrite expr2; lra.
Qed.

(* The radial identity V_c(q) = E q^2 + c (E q)^2. *)
Lemma clip_objective_radial :
  clip_objective mu c q = \int[mu]_x (q x ^+ 2) + c * (\int[mu]_x q x) ^+ 2.
Proof.
have hv := clip_objective_profile.
rewrite hv; move: hv; rewrite /clip_objective.
move: (\int[mu]_x ((x : R) * q x)) (\int[mu]_x q x) (\int[mu]_x (q x ^+ 2)).
by move=> X M Q hv; lra.
Qed.

(* q maximizes V_c over the admissible profiles. *)
Lemma clip_optimal (q' : measurableTypeR R -> R) : clip_admissible C q' ->
  clip_objective mu c q' <= clip_objective mu c q.
Proof.
move=> hq'.
have [B B0 qB] := clip_admissible_bounded hq'.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have mq := measurable_clip_profile C a t.
have mq' : measurable_fun [set: measurableTypeR R] q' by case: hq'.
pose h x := q' x - q x.
have mh : measurable_fun [set: measurableTypeR R] h by exact: measurable_funB.
have hB : forall x, `|h x| <= B + B'.
  by move=> x; apply: le_trans (ler_normB _ _) _; apply: lerD.
have iq := clip_integrable_bounded mq qsB.
have ih := clip_integrable_bounded mh hB.
have ixq := clip_integrable_id_bounded mq qsB.
have ixh := clip_integrable_id_bounded mh hB.
have iq2 := bounded_sq mq qsB.
have ih2 := bounded_sq mh hB.
have iqh := bounded_mul mq mh qsB hB.
have i2qh := integrableZ_R 2 iqh.
have iq2qh := integrableD_R iq2 i2qh.
have iah := integrableZ_R a ih.
have ixah := integrableB_R ixh iah.
have eq' : q' = (fun x => q x + h x).
  by apply/funext => x; rewrite /h addrC subrK.
have J1 : \int[mu]_x ((x : R) * q' x) =
    \int[mu]_x ((x : R) * q x) + \int[mu]_x ((x : R) * h x).
  rewrite eq' -RintegralD //; apply: eq_Rintegral => x _ /=; ring.
have J2 : \int[mu]_x (q' x ^+ 2) =
    \int[mu]_x (q x ^+ 2) + 2 * \int[mu]_x (q x * h x) + \int[mu]_x (h x ^+ 2).
  rewrite eq' -RintegralZl // -RintegralD // -RintegralD //.
  by apply: eq_Rintegral => x _ /=; ring.
have J3 : \int[mu]_x q' x = \int[mu]_x q x + \int[mu]_x h x.
  by rewrite eq' RintegralD.
have J4 : \int[mu]_x (((x : R) - a - q x) * h x) =
    \int[mu]_x ((x : R) * h x) - a * \int[mu]_x h x - \int[mu]_x (q x * h x).
  have -> : (fun x : measurableTypeR R => ((x : R) - a - q x) * h x) =
      (fun x => ((x : R) * h x - a * h x) - q x * h x).
    by apply/funext => x; ring.
  by rewrite RintegralB // RintegralB // RintegralZl.
(* V(q + h) - V(q) = 2 E[w h] - (E h^2 + c (E h)^2) <= 0 *)
have FO : \int[mu]_x (((x : R) - a - q x) * h x) <= 0 := clip_first_order hq'.
have Qh := upper_form_ge0 c1 ih ih2.
rewrite J4 in FO.
rewrite /clip_objective J1 J2 J3.
move: FO Qh (fixpt).
move: (\int[mu]_x ((x : R) * q x)) (\int[mu]_x ((x : R) * h x))
  (\int[mu]_x (q x ^+ 2)) (\int[mu]_x (q x * h x)) (\int[mu]_x (h x ^+ 2))
  (\int[mu]_x q x) (\int[mu]_x h x) => X0 Xh Q0 P H M0 Mh FO Qh fp.
rewrite fp in FO.
nra.
Qed.

(* E[X (X - w)_+] = s(w) + w m(w). *)
Lemma clip_xupper_integrable w :
  integrable (fun x => (x : R) * Num.max ((x : R) - w) 0).
Proof.
have i2 := integrable_upper_pow mu2 w (isT : (2 <= 2)%N).
have iw := integrableZ_R w (integrable_upper1 w).
have := integrableD_R i2 iw.
apply: eq_integrable => // x _ /=; congr EFin.
by case: (leP ((x : R) - w) 0) => hw; rewrite ?expr0n /=; ring.
Qed.

Lemma clip_xupperE w :
  \int[mu]_x ((x : R) * Num.max ((x : R) - w) 0) = s w + w * m w.
Proof.
have i2 := integrable_upper_pow mu2 w (isT : (2 <= 2)%N).
have i1 := integrable_upper1 w.
have iw := integrableZ_R w i1.
have -> : (fun x : measurableTypeR R => (x : R) * Num.max ((x : R) - w) 0) =
    (fun x => Num.max ((x : R) - w) 0 ^+ 2 + w * Num.max ((x : R) - w) 0).
  apply/funext => x.
  by case: (leP ((x : R) - w) 0) => hw; rewrite ?expr0n /=; ring.
by rewrite RintegralD // RintegralZl.
Qed.

(* V_c(q) = J(t + a) - J(C t + a), with J(w) = s(w) + w m(w). *)
Lemma clip_objectiveE : clip_objective mu c q =
  (s (t + a) + (t + a) * m (t + a)) -
  (s (C * t + a) + (C * t + a) * m (C * t + a)).
Proof.
rewrite clip_objective_profile.
have ix := integrable_idR mu2.
have itx := integrableZ_R t ix.
have il := clip_xupper_integrable (t + a).
have iu := clip_xupper_integrable (C * t + a).
have itl := integrableD_R itx il.
have -> : (fun x : measurableTypeR R => (x : R) * q x) =
    (fun x => (t * (x : R) + (x : R) * Num.max ((x : R) - (t + a)) 0) -
              (x : R) * Num.max ((x : R) - (C * t + a)) 0).
  by apply/funext => x; rewrite clip_profileE //; ring.
rewrite RintegralB // RintegralD // RintegralZl // (Rintegral_id_sym mu2 musym).
by rewrite !clip_xupperE mulr0 add0r.
Qed.

(* 3. The dual form. *)

(* t minimizes t' |-> s(-t' - a) + s(C t' + a) over t' >= 0. *)
Lemma clip_energy_shift_min (t' : R) : 0 <= t' ->
  clip_energy_shift mu C a t <= clip_energy_shift mu C a t'.
Proof.
move=> t'0; rewrite !clip_energy_shiftE //.
have [B B0 qB] := clip_profile_bounded a C1 t'0.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have mq := measurable_clip_profile C a t.
have mq' := measurable_clip_profile C a t'.
pose q' := clip_profile C a t'.
have md : measurable_fun [set: measurableTypeR R]
    (fun x : measurableTypeR R => q' x - q x) by exact: measurable_funB.
have dB : forall x : measurableTypeR R, `|q' x - q x| <= B + B'.
  by move=> x; apply: le_trans (ler_normB _ _) _; apply: lerD.
have FO : \int[mu]_x (((x : R) - a - q x) * (q' x - q x)) <= 0.
  exact: clip_first_order (clip_profile_admissible a C1 t'0).
have iw2 := clip_integrable_res_sq a mq qsB.
have iw2' := clip_integrable_res_sq a mq' qB.
have iwd := clip_integrable_res_mul a mq md qsB dB.
have i2wd := integrableZ_R 2 iwd.
have iB := integrableB_R iw2 i2wd.
apply: (@le_trans _ _ (\int[mu]_x (((x : R) - a - q x) ^+ 2 -
    2 * (((x : R) - a - q x) * (q' x - q x))))).
  rewrite RintegralB // RintegralZl //.
  move: FO; move: (\int[mu]_x (((x : R) - a - q x) * (q' x - q x))) => z.
  by lra.
apply: le_Rintegral => // x _.
by have := sqr_ge0 (q' x - q x); rewrite /q'; nra.
Qed.

(* V_c(q) + c (b - E q)^2
   <= E X^2 + c (1 + c) b^2 - (s(-t - c b) + s(C t + c b)). *)
Lemma clip_dual_lower (b : R) :
  clip_objective mu c q + c * (b - \int[mu]_x q x) ^+ 2 <=
  \int[mu]_x ((x : R) ^+ 2) + c * (1 + c) * b ^+ 2
  - clip_energy_shift mu C (c * b) t.
Proof.
have [B B0 qB] := clip_profile_bounded (c * b) C1 t0.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have mqb := measurable_clip_profile C (c * b) t.
have mq := measurable_clip_profile C a t.
rewrite clip_energy_shiftE //.
have hle : \int[mu]_x (((x : R) - c * b - clip_profile C (c * b) t x) ^+ 2) <=
    \int[mu]_x (((x : R) - c * b - q x) ^+ 2).
  apply: le_Rintegral => //.
  - exact: clip_integrable_res_sq mqb qB.
  - exact: clip_integrable_res_sq mq qsB.
  - move=> x _; apply: clip_profile_closest => //.
    exact: clip_profile_bounds.
rewrite (clip_res_sqE (c * b) mq qsB) in hle.
rewrite /clip_objective.
move: hle.
move: (\int[mu]_x ((x : R) ^+ 2)) (\int[mu]_x ((x : R) * q x))
  (\int[mu]_x q x) (\int[mu]_x (q x ^+ 2))
  (\int[mu]_x (((x : R) - c * b - clip_profile C (c * b) t x) ^+ 2)).
move=> S X M Q E hle.
by nra.
Qed.

Let S_lbound (a' : R) :
  has_lbound [set clip_energy_shift mu C a' t' | t' in [set t' : R | 0 <= t']].
Proof. by exists 0 => _ [t' _ <-]; exact: clip_energy_shift_ge0. Qed.

(* The dual at its optimum: D(E q) = V_c(q); the infimum is attained
   at t. *)
Lemma clip_dual_opt :
  clip_dual mu c C (\int[mu]_x q x) = clip_objective mu c q.
Proof.
rewrite /clip_dual -fixpt.
have Et : inf [set clip_energy_shift mu C a t' | t' in [set t' : R | 0 <= t']] =
    clip_energy_shift mu C a t.
  apply/eqP; rewrite eq_le; apply/andP; split.
    by apply: (ge_inf (S_lbound a)); exists t.
  apply: lb_le_inf; first by exists (clip_energy_shift mu C a t), t.
  by move=> _ [t' t'0 <-]; exact: clip_energy_shift_min.
rewrite Et.
have := clip_dual_profile c (\int[mu]_x q x) C1 t0.
rewrite -fixpt subrr expr0n /= mulr0 addr0 => ->.
by [].
Qed.

(* For c <= 0, D(b) <= V_c(q) for every b. *)
Lemma clip_dual_le : c <= 0 ->
  forall b, clip_dual mu c C b <= clip_objective mu c q.
Proof.
move=> c0 b; rewrite /clip_dual.
set T := [set clip_energy_shift mu C (c * b) t' | t' in [set t' : R | 0 <= t']].
suff h : \int[mu]_x ((x : R) ^+ 2) + c * (1 + c) * b ^+ 2
    - clip_objective mu c q <= inf T.
  by move: h; move: (inf T) => i; lra.
rewrite /T.
apply: lb_le_inf.
  by exists (clip_energy_shift mu C (c * b) 0), 0; rewrite /= ?lexx.
move=> _ [t' t'0 <-].
have h := clip_dual_profile c b C1 t'0.
have hv := clip_optimal (clip_profile_admissible (c * b) C1 t'0).
have hc : c * (\int[mu]_x clip_profile C (c * b) t' x - b) ^+ 2 <= 0.
  by rewrite mulr_le0_ge0 // sqr_ge0.
by move: h hv hc; lra.
Qed.

(* For c >= 0, V_c(q) <= D(b) for every b. *)
Lemma clip_dual_ge : 0 <= c ->
  forall b, clip_objective mu c q <= clip_dual mu c C b.
Proof.
move=> c0 b; rewrite /clip_dual.
have hle :
    inf [set clip_energy_shift mu C (c * b) t' | t' in [set t' : R | 0 <= t']]
    <= clip_energy_shift mu C (c * b) t.
  by apply: (ge_inf (S_lbound (c * b))); exists t.
have h := clip_dual_lower b.
have hc : 0 <= c * (b - \int[mu]_x q x) ^+ 2 by rewrite mulr_ge0 // sqr_ge0.
by move: hle h hc; lra.
Qed.

(* The window: 0 <= E q and min(1, 1 + c)^2 (E q)^2 <= E X^2. *)
Lemma clip_dual_window :
  0 <= \int[mu]_x q x /\
  Num.min 1 (1 + c) ^+ 2 * (\int[mu]_x q x) ^+ 2 <= \int[mu]_x ((x : R) ^+ 2).
Proof.
have [B' B'0 qsB] := clip_profile_bounded a C1 t0.
have mq := measurable_clip_profile C a t.
have iq := clip_integrable_bounded mq qsB.
have iq2 := clip_integrable_sq mq qsB.
have ixq := clip_integrable_id_bounded mq qsB.
split.
  apply: Rintegral_ge0 => x _.
  by have /andP[h _] := clip_profile_bounds a C1 t0 x; exact: le_trans t0 h.
have hv := clip_objective_profile.
have hJ := Rintegral_sqr_le iq iq2.
have S0' : 0 <= \int[mu]_x ((x : R) ^+ 2).
  by apply: Rintegral_ge0 => x _; exact: sqr_ge0.
have Q0 : 0 <= \int[mu]_x (q x ^+ 2).
  by apply: Rintegral_ge0 => x _; exact: sqr_ge0.
(* Cauchy-Schwarz: (E X q)^2 <= E X^2 E q^2 *)
have CS : (\int[mu]_x ((x : R) * q x)) ^+ 2 <=
    \int[mu]_x ((x : R) ^+ 2) * \int[mu]_x (q x ^+ 2).
  rewrite -sqrrN; apply: discriminant_le => // l.
  have ml : measurable_fun [set: measurableTypeR R]
      (fun x : measurableTypeR R => l * q x).
    by apply: measurable_funM => //; exact: measurable_cst.
  have lB : forall x : measurableTypeR R, `|l * q x| <= `|l| * B'.
    by move=> x; rewrite normrM ler_wpM2l.
  have := clip_res_sqE 0 ml lB.
  have -> : \int[mu]_x ((x : R) * (l * q x)) = l * \int[mu]_x ((x : R) * q x).
    by rewrite -RintegralZl //; apply: eq_Rintegral => x _; ring.
  have -> : \int[mu]_x (l * q x) = l * \int[mu]_x q x by rewrite RintegralZl.
  have -> : \int[mu]_x ((l * q x) ^+ 2) = l ^+ 2 * \int[mu]_x (q x ^+ 2).
    by rewrite -RintegralZl //; apply: eq_Rintegral => x _; ring.
  have : 0 <= \int[mu]_x (((x : R) - 0 - l * q x) ^+ 2).
    by apply: Rintegral_ge0 => x _; exact: sqr_ge0.
  move=> h0 e; rewrite e in h0.
  move: h0; rewrite expr0n /= mulr0 mul0r addr0 addr0.
  move: (\int[mu]_x ((x : R) ^+ 2)) (\int[mu]_x ((x : R) * q x))
    (\int[mu]_x (q x ^+ 2)) => S X Q h0.
  by nra.
move: hv; rewrite /clip_objective => hv.
have a01 : Num.min 1 (1 + c) <= 1 by rewrite ge_min lexx.
have a02 : Num.min 1 (1 + c) <= 1 + c by rewrite ge_min lexx orbT.
have a00 : 0 < Num.min 1 (1 + c).
  by rewrite lt_min ltr01 /= -ltrBlDl sub0r.
move: hv hJ S0' Q0 CS a01 a02 a00.
move: (\int[mu]_x ((x : R) ^+ 2)) (\int[mu]_x ((x : R) * q x))
  (\int[mu]_x q x) (\int[mu]_x (q x ^+ 2)) (Num.min 1 (1 + c)) => S X M Q k.
move=> hv hJ S0' Q0 CS a01 a02 a00.
(* X = Q + c M^2 >= k Q, and k^2 Q^2 <= X^2 <= S Q *)
have XkQ : k * Q <= X by case: (leP 0 c) => hc; nra.
have k0 : 0 <= k * Q by rewrite mulr_ge0 // ltW.
have kQ2 : (k * Q) ^+ 2 <= S * Q.
  by apply: le_trans CS; rewrite lerXn2r ?nnegrE // (le_trans k0 XkQ).
case: (ltP 0 Q) => Qp; last first.
  have Q00 : Q = 0 by apply/eqP; rewrite eq_le Qp Q0.
  by move: hJ; rewrite Q00 => hJ; nra.
have : k ^+ 2 * Q <= S.
  by rewrite -(ler_pM2r Qp); move: kQ2; rewrite expr2 => h; nra.
by have := mulr_ge0 (ltW a00) (ltW a00); nra.
Qed.

End clip_first_order.

End clip_integrals.
