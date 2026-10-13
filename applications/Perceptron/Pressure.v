From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive realfun exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import lindeberg log_partition.
From GaussianAnalysis.probability Require Import rademacher_lindeberg.
From GaussianApplications Require Import PerceptronSignDefinitions.

(**md**************************************************************************)
(* # The pressure of the Ising perceptron                                     *)
(*                                                                            *)
(* Part of target T6 of phase 12 (AGENTS.md, section Phase 12), the           *)
(* comparison of the expected pressure of the Ising perceptron under sign and *)
(* Gaussian patterns. A Rocq formalization of the credited argument of the    *)
(* first paragraph of the proof of Theorem ext:sign of 'The free energy of    *)
(* the Ising random perceptron' (family 222 of the OpenAI math collection,    *)
(* revision 1581d4cbd, sections/extensions.tex). The collection has no Lean   *)
(* version of it.                                                             *)
(*                                                                            *)
(* Take patterns G in 'M[R]_(M, N) with N >= 1, and a potential f with three  *)
(* derivatives such that |f| <= B0, |f'| <= B1, |f''| <= B2 and               *)
(* |f'''| <= B3. The normalized pressure p_N(G, f) of                         *)
(* PerceptronSignDefinitions.v is (1/N) ln (2^(-N) sum_x exp (E_G(x))), with  *)
(* the energy E_G(x) = sum_mu f ((G x)_mu / sqrt N) (perceptron_pressureE).   *)
(* It is at most M B0 in absolute value (perceptron_pressure_le) and          *)
(* measurable in the entries of G (measurable_perceptron_pressure). As in     *)
(* the manuscript, the entry G_(mu, i) enters only (G x)_mu, with the factor  *)
(* x_i / sqrt N. So the pressure has three derivatives in each entry, and     *)
(* the third is at most (B3 + 6 B1 B2 + 6 B1^3) / (N^2 sqrt N) in absolute    *)
(* value (perceptron_pressure_derive3, from log_partition_derive3 of          *)
(* library/probability/log_partition.v). The coordinate replacement of        *)
(* library/probability/rademacher_lindeberg.v over the M N entries then       *)
(* gives perceptron_sign_compare: g |-> p_N(vec_mx g, f) is integrable        *)
(* against gauss (M * N), and                                                 *)
(*   |E_sign p_N - E_Gauss p_N| <= (B3 + 6 B1 B2 + 6 B1^3) / 2 M N^(-3/2).    *)
(* The average over the sign patterns indexed by 'I_M * 'I_N is the average   *)
(* over the rows of signs indexed by 'I_(M * N) (sign_pressureE).             *)
(*                                                                            *)
(* The manuscript takes f in C_c^infinity and states the error O_f(N^(-1/2))  *)
(* when M is of order N. Here the constant is explicit, depends only on B1,   *)
(* B2 and B3, and holds for every M.                                          *)
(*                                                                            *)
(* ```                                                                        *)
(* pressure_energy G x == sum_mu f ((G x)_mu / sqrt N), the energy of the     *)
(*                        spins x for the patterns G                          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Section pressure.
Context {R : realType}.
Variables (M N : nat) (f f1 f2 f3 : R -> R) (B0 B1 B2 B3 : R).
Hypothesis N0 : (0 < N)%N.
Hypothesis df : forall x : R, is_derive x 1 f (f1 x).
Hypothesis df1 : forall x : R, is_derive x 1 f1 (f2 x).
Hypothesis df2 : forall x : R, is_derive x 1 f2 (f3 x).
Hypothesis fB0 : forall x, `|f x| <= B0.
Hypothesis fB1 : forall x, `|f1 x| <= B1.
Hypothesis fB2 : forall x, `|f2 x| <= B2.
Hypothesis fB3 : forall x, `|f3 x| <= B3.

Local Notation sN := (Num.sqrt N%:R : R).

(* The energy of the spins x for the patterns G. *)
Definition pressure_energy (G : 'M[R]_(M, N)) (x : {ffun 'I_N -> bool}) :=
  \sum_(mu < M) f ((G *m spin_col R x) mu 0 / sN).

Lemma perceptron_pressureE (G : 'M[R]_(M, N)) :
  perceptron_pressure f G =
  N%:R^-1 * ln (\sum_x (2 ^+ N)^-1 * expR (pressure_energy G x)).
Proof. by rewrite /perceptron_pressure mulr_sumr. Qed.

Lemma perceptron_pressure_le (G : 'M[R]_(M, N)) :
  `|perceptron_pressure f G| <= M%:R * B0.
Proof.
rewrite perceptron_pressureE.
have B00 : 0 <= B0 := le_trans (normr_ge0 _) (fB0 0).
set K := M%:R * B0.
have K0 : 0 <= K by rewrite /K mulr_ge0 ?ler0n.
have Eb x : `|pressure_energy G x| <= K.
  rewrite /pressure_energy; apply: le_trans (ler_norm_sum _ _ _) _.
  apply: le_trans (ler_sum _ (fun mu _ => fB0 _)) _.
  by rewrite sumr_const card_ord /K mulr_natl.
have p0 : 0 < (2 ^+ N : R)^-1 by rewrite invr_gt0 exprn_gt0.
have avgc (c : R) : \sum_(x : {ffun 'I_N -> bool}) (2 ^+ N)^-1 * c = c.
  rewrite sumr_const card_ffun card_bool card_ord -[_ *+ _]mulr_natr natrX.
  by rewrite mulrAC mulVf ?expf_neq0 // mul1r.
set Z := \sum_x _.
have Zlo : expR (- K) <= Z.
  rewrite -[X in X <= _]avgc; apply: ler_sum => x _.
  rewrite ler_pM2l // ler_expR.
  by have := Eb x; rewrite ler_norml => /andP[].
have Zhi : Z <= expR K.
  rewrite -[X in _ <= X]avgc; apply: ler_sum => x _.
  rewrite ler_pM2l // ler_expR.
  by have := Eb x; rewrite ler_norml => /andP[].
have Z0 : 0 < Z := lt_le_trans (expR_gt0 _) Zlo.
have lZ : `|ln Z| <= K.
  rewrite ler_norml; apply/andP; split.
    by rewrite -[X in X <= _](expRK (- K)) ler_ln ?posrE ?expR_gt0.
  by rewrite -[X in _ <= X](expRK K) ler_ln ?posrE ?expR_gt0.
have N1 : 1 <= N%:R :> R by rewrite ler1n.
rewrite normrM ger0_norm ?invr_ge0 ?ler0n //.
apply: le_trans (ler_wpM2l _ lZ) _; first by rewrite invr_ge0 ler0n.
by rewrite ler_pdivrMl ?ltr0n // ler_peMl.
Qed.

Lemma measurable_perceptron_pressure :
  measurable_fun [set: 'rV[R]_(M * N)]
    (fun g => perceptron_pressure f (vec_mx g)).
Proof.
have mf : measurable_fun setT f.
  exact: continuous_measurable_fun (is_derive_continuous df).
have mv : measurable_fun [set: 'rV[R]_(M * N)] (fun g => vec_mx g).
  apply/measurable_fun_mxP => i j.
  under eq_fun do rewrite mxE.
  exact: measurable_mxentry.
rewrite /perceptron_pressure.
apply: measurable_funM => //.
apply: measurableT_comp; first exact: measurable_ln.
apply: measurable_funM => //.
apply: measurable_sum => x.
apply: measurableT_comp; first exact: measurable_expR.
apply: measurable_sum => mu.
apply: measurableT_comp mf _.
apply: measurable_funM => //.
apply: measurableT_comp (measurable_mxentry mu 0) _.
exact: measurable_mulmx.
Qed.

(* The pressure along one pattern entry has three derivatives, the third
   at most (B3 + 6 B1 B2 + 6 B1^3) / (N^2 sqrt N) in absolute value. *)
Lemma perceptron_pressure_derive3 (j : 'I_(M * N)) (g : 'rV[R]_(M * N)) :
  exists F1 F2 F3 : R -> R,
  [/\ forall t : R, is_derive t 1
        (fun t => perceptron_pressure f (vec_mx (t *: delta_mx 0 j + g)))
        (F1 t),
      forall t : R, is_derive t 1 F1 (F2 t),
      forall t : R, is_derive t 1 F2 (F3 t) &
      forall t, `|F3 t| <=
        (B3 + 6 * B1 * B2 + 6 * B1 ^+ 3) / (N%:R ^+ 2 * sN)].
Proof.
case/mxvec_indexP: j => mu0 i0.
have sN0 : 0 < sN by rewrite sqrtr_gt0 ltr0n.
have vE t : vec_mx (t *: delta_mx 0 (mxvec_index mu0 i0) + g) =
    t *: delta_mx mu0 i0 + vec_mx g.
  rewrite -(vec_mx_delta R mu0 i0).
  by apply/matrixP => i k; rewrite !mxE.
(* the argument of f in the row mu is a x mu * t + c x mu *)
pose a (x : {ffun 'I_N -> bool}) (mu : 'I_M) :=
  (delta_mx mu0 i0 *m spin_col R x) mu 0 / sN.
pose c (x : {ffun 'I_N -> bool}) (mu : 'I_M) :=
  (vec_mx g *m spin_col R x) mu 0 / sN.
have ac t x mu :
    ((t *: delta_mx mu0 i0 + vec_mx g) *m spin_col R x) mu 0 / sN =
    a x mu * t + c x mu.
  rewrite mulmxDl -scalemxAl /a /c.
  move: (delta_mx mu0 i0 *m spin_col R x) (vec_mx g *m spin_col R x).
  move=> P Q; have sNn := lt0r_neq0 sN0.
  by rewrite !mxE; field.
have aE x mu : a x mu = (mu == mu0)%:R * (if x i0 then 1 else -1) / sN.
  rewrite /a mxE (bigD1 i0) //= big1; last first.
    by rewrite !mxE eqxx andbT addr0.
  by move=> k ki0; rewrite !mxE (negbTE ki0) andbF mul0r.
have dterm (F F' : R -> R) (al ga : R) (k : nat) :
    (forall y : R, is_derive y 1 F (F' y)) -> forall t : R,
    is_derive t 1 (fun t => al ^+ k * F (al * t + ga))
      (al ^+ k.+1 * F' (al * t + ga)).
  move=> dF t.
  have dg : is_derive t 1 (fun t => al * t + ga) al.
    by apply: is_derive_eq; rewrite /GRing.scale /=; ring.
  have dc : is_derive t 1 (fun t => F (al * t + ga))
      (al * F' (al * t + ga)).
    by apply: is_derive_eq (is_derive1_comp (dF _) dg) _; rewrite mulrC.
  apply: is_derive_eq (is_deriveZ (al ^+ k) dc) _.
  by rewrite /GRing.scale /= exprS mulrA [al ^+ k * al]mulrC.
(* the k-th derivatives of the energies *)
pose hk (k : nat) (F : R -> R) (x : {ffun 'I_N -> bool}) (t : R) :=
  \sum_(mu < M) a x mu ^+ k * F (a x mu * t + c x mu).
have dhk k (F F' : R -> R) : (forall y : R, is_derive y 1 F (F' y)) ->
    forall x (t : R), is_derive t 1 (hk k F x) (hk k.+1 F' x t).
  move=> dF x t.
  by apply: (is_derive_fsum
    (F := fun mu t => a x mu ^+ k * F (a x mu * t + c x mu))
    (F' := fun mu t => a x mu ^+ k.+1 * F' (a x mu * t + c x mu))).
have X0 : (0 < #|{ffun 'I_N -> bool}|)%N.
  by rewrite card_ffun card_bool card_ord expn_gt0.
have w0 (x : {ffun 'I_N -> bool}) : 0 < (2 ^+ N : R)^-1.
  by rewrite invr_gt0 exprn_gt0.
have [L1 [L2 [L3 [dL0 dL1 dL2 bL]]]] :=
  log_partition_derive3 (w := fun _ => (2 ^+ N : R)^-1) w0 X0
    (dhk 0%N _ _ df) (dhk 1%N _ _ df1) (dhk 2%N _ _ df2).
have -> : (fun t => perceptron_pressure f
      (vec_mx (t *: delta_mx 0 (mxvec_index mu0 i0) + g))) =
    (fun t => N%:R^-1 * ln (\sum_x (2 ^+ N)^-1 * expR (hk 0%N f x t))).
  apply: funext => t; rewrite perceptron_pressureE vE /pressure_energy /hk.
  congr (_ * ln _); apply: eq_bigr => x _; congr (_ * expR _).
  by apply: eq_bigr => mu _; rewrite ac expr0 mul1r.
exists (fun t => N%:R^-1 * L1 t), (fun t => N%:R^-1 * L2 t),
  (fun t => N%:R^-1 * L3 t); split.
- by move=> t; apply: is_derive_eq (is_deriveZ (N%:R^-1) (dL0 t)) _.
- by move=> t; apply: is_derive_eq (is_deriveZ (N%:R^-1) (dL1 t)) _.
- by move=> t; apply: is_derive_eq (is_deriveZ (N%:R^-1) (dL2 t)) _.
move=> t.
(* only the row mu0 depends on t, with |a x mu0| = 1 / sqrt N *)
have hb k (F : R -> R) (B : R) : (0 < k)%N -> (forall y, `|F y| <= B) ->
    forall x, `|hk k F x t| <= sN^-1 ^+ k * B.
  move=> k0 FB x.
  rewrite /hk (bigD1 mu0) //= big1 ?addr0; last first.
    rewrite normrM normrX aE eqxx mul1r.
    have -> : `|(if x i0 then 1 else -1) / sN| = sN^-1.
      rewrite normrM normfV (gtr0_norm sN0).
      by case: (x i0); rewrite ?normr1 ?normrN1 mul1r.
    by apply: ler_wpM2l; [rewrite exprn_ge0 // invr_ge0 ltW | exact: FB].
  by move=> mu nmu; rewrite aE (negbTE nmu) !mul0r expr0n eqn0Ngt k0 mul0r.
have hL := bL t _ _ _ (hb 1%N f1 B1 erefl fB1) (hb 2%N f2 B2 erefl fB2)
  (hb 3%N f3 B3 erefl fB3).
rewrite normrM ger0_norm ?invr_ge0 ?ler0n //.
apply: le_trans (ler_wpM2l _ hL) _; first by rewrite invr_ge0 ler0n.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
have s2 : sN ^+ 2 = N%:R by rewrite sqr_sqrtr ?ler0n.
have sn0 := lt0r_neq0 sN0.
by move: s2 sn0; move: sN => s s2 sn0; rewrite -s2; field.
Qed.

(* The average over the sign patterns, indexed as rows of 'I_(M * N). *)
Lemma sign_pressureE : sign_pressure M N f = (2 ^+ (M * N))^-1 *
  \sum_(s : {ffun 'I_(M * N) -> bool})
    perceptron_pressure f (vec_mx (sign_row s)).
Proof.
pose h (s : {ffun 'I_(M * N) -> bool}) : {ffun 'I_M * 'I_N -> bool} :=
  [ffun q => s (mxvec_index q.1 q.2)].
have hinj : injective h.
  move=> s1 s2 e; apply/ffunP => k; case/mxvec_indexP: k => mu i.
  have := congr1 (fun F : {ffun 'I_M * 'I_N -> bool} => F (mu, i)) e.
  by rewrite /h !ffunE.
have hbij : bijective h.
  by apply: (inj_card_bij hinj); rewrite !card_ffun card_prod !card_ord.
rewrite /sign_pressure (reindex h) /=; first exact: onW_bij hbij.
congr (_ * _); apply: eq_bigr => s _; congr perceptron_pressure.
by apply/matrixP => mu i; rewrite !mxE ffunE.
Qed.

Theorem perceptron_sign_compare :
  (gauss (M * N)).-integrable setT
    (EFin \o (fun g : 'rV[R]_(M * N) => perceptron_pressure f (vec_mx g))) /\
  `|sign_pressure M N f - gauss_pressure M N f| <=
    (B3 + 6 * B1 * B2 + 6 * B1 ^+ 3) / 2 * M%:R * N%:R `^ (- (3 / 2)).
Proof.
have mP := measurable_perceptron_pressure.
have PC (g : 'rV[R]_(M * N)) :
    `|perceptron_pressure f (vec_mx g)| <= M%:R * B0.
  exact: perceptron_pressure_le.
split; first exact: (bounded_integrable _ mP PC).
have := rademacher_gauss_lindeberg mP PC
  (fun j x => perceptron_pressure_derive3 j x).
rewrite -sign_pressureE /gauss_pressure => h; apply: le_trans h _.
rewrite sumr_const card_ord -[_ *+ (M * N)]mulr_natl natrM.
have N0' : (N%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have sN0 : (Num.sqrt N%:R : R) != 0 by rewrite sqrtr_eq0 -ltNge ltr0n.
(* N^(-3/2) = 1 / (N sqrt N) *)
have p32 : N%:R `^ (- (3 / 2)) = (N%:R * Num.sqrt N%:R)^-1 :> R.
  have e32 : (3 / 2 : R) = 1 + 2^-1 by field.
  rewrite powRN e32 powRD; first by rewrite N0' implybT.
  by rewrite powRr1 ?ler0n // powR12_sqrt ?ler0n.
rewrite p32 le_eqVlt; apply/orP; left; apply/eqP.
by field.
Qed.

End pressure.
