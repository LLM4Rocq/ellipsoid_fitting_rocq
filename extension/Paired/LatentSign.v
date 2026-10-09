(* Exact fitting for the latent-sign law, from the finite-mixture theorem, at
   Stdlib's R: item 3 of phase 7 (AGENTS.md, section "Phase 7"). The
   definitions are those of LatentSignDefinitions: h = paired_kernel, and the
   density of a sample against the product of the uniform laws is the
   product over the points of
     (prod_j (1 + s h(x_j)) + prod_j (1 - s h(x_j))) / 2.

   1. The density as a mixture of two products. Component 0 has the
      parameter s and component 1 the parameter -s (latent_param); for
      0 <= s <= 1 both lie in [-1, 1], inside the range [-1, 7/3] where
      1 + a h is a density against the uniform law (latent_param_range).
      The density of a point is
        \sum_(c < 2) 2^-1 \prod_j (1 + latent_param s c h(x_j))
      (latent_point_density), and the density of a sample is the sum, over
      the tuples t of labels of the n points, of the product weights times
      the product over the n * d coordinates (latent_sample_mixture, by
      big_tuple_distr of library/probability/mixture.v and prod_flat of
      Paired/Law).
   2. latent_probability_mixture: for 0 <= s <= 1 and a law mu with
      paired_uniform_spec mu (the uniform law), on every measurable event,
      latent_probability s mu n d is the mixture_probability of two
      components of weight 1/2, whose coordinates have the laws
      paired_law mu s and paired_law mu (-s) of Paired/Uniform
      (latent_mu). The proof is that of paired_probability_mixture of
      Paired/Law: outside the null event where a coordinate leaves
      [-sqrt 3, sqrt 3] (paired_uniform_null), the factors 1 + a h are the
      densities paired_density, and the integral of their product over the
      event is the labelled law (tuple_prod_density of
      library/probability/density_law.v).
   3. latent_family, latent_fourth: for 0 <= s d <= 1 and the uniform law,
      the components are component laws with constant 3
      (paired_law_component), and every coordinate has the fourth moment
      9/5 under the mixture, since the fourth moments 9/5 + 8 s / 35 and
      9/5 - 8 s / 35 of the components (paired_law_fourth) average to 9/5.
   4. latent_sign_of_mixture: mixture_theorem_statement implies
      latent_sign_statement, as paired_of_mixture of Paired/Theorem. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg density_law mixture.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions.
From EllipsoidUniversality Require Import LatentSignStatement.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Paired Require Import Uniform Law.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The density as a mixture of two products. *)

(* The parameter of component c: s for c = 0, and -s otherwise. *)
Definition latent_param (s : R) (c : nat) : R := if c == 0%N then s else - s.

Lemma latent_param_range s c : 0 <= s <= 1 ->
  - 1 <= latent_param s c <= 7%:R / 3%:R.
Proof.
move=> /andP[s0 s1].
have h73 : 1 <= 7%:R / 3%:R :> R by rewrite ler_pdivlMr // mul1r ler_nat.
by rewrite /latent_param; case: eqP => _; apply/andP; split; lra.
Qed.

Lemma latent_point_density (s : R) (d : nat) (x : nat -> R) :
  (\prod_(j < d) (1 + s * paired_kernel (x j)) +
   \prod_(j < d) (1 - s * paired_kernel (x j))) / 2%:R =
  \sum_(c < 2) 2^-1 *
    \prod_(j < d) (1 + latent_param s c * paired_kernel (x j)).
Proof.
rewrite big_ord_recr big_ord1 /= /latent_param /=.
have -> : \prod_(j < d) (1 + - s * paired_kernel (x j)) =
    \prod_(j < d) (1 - s * paired_kernel (x j)).
  by apply: eq_bigr => j _; rewrite mulNr.
by rewrite -mulrDr mulrC.
Qed.

Lemma latent_sample_mixture (s : R) (n d : nat) (x : paper_main_sample n d) :
  latent_sample_density s n d x =
  \sum_(t : n.-tuple 'I_2) (\prod_(i < n) (2^-1 : R)) *
    \prod_(k < n * d)
      (1 + latent_param s (mixture_label t (k %/ d)) * paired_kernel (tnth x k)).
Proof.
have hp (i : 'I_n) :
    (\prod_(j < d)
       (1 + s * paired_kernel (List.nth (i * d + j) (tval x) 0)) +
     \prod_(j < d)
       (1 - s * paired_kernel (List.nth (i * d + j) (tval x) 0))) / 2%:R =
    \sum_(c < 2) 2^-1 *
      \prod_(j < d) (1 + latent_param s c *
                        paired_kernel (List.nth (i * d + j) (tval x) 0)).
  exact: (latent_point_density s d (fun j => List.nth (i * d + j) (tval x) 0)).
rewrite /latent_sample_density (eq_bigr _ (fun i _ => hp i)).
rewrite -(big_tuple_distr (fun (i : 'I_n) (c : 'I_2) => 2^-1 *
  \prod_(j < d) (1 + latent_param s c *
                    paired_kernel (List.nth (i * d + j) (tval x) 0)))).
apply: eq_bigr => t _; rewrite big_split /=; congr (_ * _).
have -> : \prod_(k < n * d) (1 + latent_param s (mixture_label t (k %/ d)) *
                                paired_kernel (tnth x k)) =
    \prod_(k < n * d) (1 + latent_param s (mixture_label t (k %/ d)) *
                          paired_kernel (List.nth k (tval x) 0)).
  by apply: eq_bigr => k _; rewrite (tnth_nth 0) List_nthE.
rewrite (prod_flat n d (fun k => 1 + latent_param s (mixture_label t (k %/ d)) *
  paired_kernel (List.nth k (tval x) 0))).
by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite mixture_label_flat.
Qed.

(* 2. The latent-sign law as a mixture of two product laws. *)

(* The law of coordinate j in component c. *)
Definition latent_mu (s : R) (mu : probability (measurableTypeR R) R)
    (c j : nat) : probability (measurableTypeR R) R :=
  paired_law mu (latent_param s c).

Section latent_mixture.
Variables (s : R) (mu : probability (measurableTypeR R) R).
Hypothesis hs : 0 <= s <= 1.
Hypothesis hmu : paired_uniform_spec mu.

Theorem latent_probability_mixture n d (E : set (paper_main_sample n d)) :
  measurable E ->
  latent_probability s mu n d E =
  mixture_probability 2 (fun=> 2^-1) (latent_mu s mu) n d E.
Proof.
move=> mE.
pose a (t : n.-tuple 'I_2) (k : nat) :=
  latent_param s (mixture_label t (k %/ d)).
have ha t k : - 1 <= a t k <= 7%:R / 3%:R by exact: latent_param_range.
pose W (t : n.-tuple 'I_2) := \prod_(i < n) (2^-1 : R).
have W0 t : 0 <= W t by apply: prodr_ge0 => i _; rewrite invr_ge0 ler0n.
pose D (x : paper_main_sample n d) := \sum_(t : n.-tuple 'I_2)
  W t * \prod_(k < n * d) (1 + a t k * paired_kernel (tnth x k)).
pose G t (x : paper_main_sample n d) :=
  \prod_(k < n * d) paired_density (a t k) (tnth x k).
have G0 t x : 0 <= G t x.
  by apply: prodr_ge0 => k _; exact: legendre_density_ge0.
have hD x : latent_sample_density s n d x = D x.
  exact: latent_sample_mixture.
(* the coordinates lie in [-sqrt 3, sqrt 3] almost surely *)
pose B (k : 'I_(n * d)) :=
  [set x : paper_main_sample n d | Num.sqrt 3%:R < `|tnth x k|].
have mB0 : measurable [set y : RR | Num.sqrt 3%:R < `|y|].
  by rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr.
have mB k : measurable (B k).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_tnth k) measurableT _ mB0.
pose Nul := \big[setU/set0]_(k <- enum 'I_(n * d)) B k.
have mN : measurable Nul by apply: bigsetU_measurable => k _; exact: mB.
have PN : universality_sample_law (fun=> mu) n d Nul = 0%E.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  apply: le_trans (measure_bigsetU_le _ _ mB) _.
  rewrite big1 // => k _.
  transitivity (mu [set y | Num.sqrt 3%:R < `|y|]).
    exact: (@tuple_prod_tnth _ _ (fun=> mu) (n * d) k _ mB0).
  exact: paired_uniform_null.
have DS x : ~ Nul x -> D x = \sum_t W t * G t x.
  move=> nx; apply: eq_bigr => t _; congr (_ * _); apply: eq_bigr => k _.
  have xk : `|tnth x k| <= Num.sqrt 3%:R.
    rewrite leNgt; apply/negP => hk; apply: nx.
    by apply: (bigsetU_mem (mem_enum _ k)).
  by rewrite /paired_density /legendre_density xk.
(* measurability *)
have mtn k : measurable_fun setT (fun x : paper_main_sample n d =>
    paired_kernel (tnth x k) : RR).
  exact: measurableT_comp measurable_paired_kernel (measurable_tnth k).
have mD : measurable_fun setT (fun x => (D x)%:E).
  apply/measurable_EFinP; apply: measurable_sum => t.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_prod => k _; apply: measurable_funD.
    exact: measurable_cst.
  by apply: measurable_funM; [exact: measurable_cst | exact: mtn].
have mG t : measurable_fun setT (fun x => (G t x)%:E).
  apply/measurable_EFinP; apply: measurable_prod => k _.
  exact: measurableT_comp (measurable_legendre_density _ _) (measurable_tnth k).
have mWG : measurable_fun setT (fun x => (\sum_t W t * G t x)%:E).
  apply/measurable_EFinP; apply: measurable_sum => t.
  apply: measurable_funM; first exact: measurable_cst.
  by apply/measurable_EFinP; exact: mG.
(* the integral *)
rewrite /latent_probability.
transitivity (\int[universality_sample_law (fun=> mu) n d]_(x in E)
    (D x)%:E)%E.
  by apply: eq_integral => x _; rewrite hD.
transitivity (\int[universality_sample_law (fun=> mu) n d]_(x in E)
    (\sum_t W t * G t x)%:E)%E.
  apply: ae_eq_integral => //.
  - exact: measurable_funS mD.
  - exact: measurable_funS mWG.
  - exists Nul; split => // x /= hx; apply: contrapT => nx; apply: hx => _.
    by rewrite DS.
under eq_integral do rewrite -sumEFin.
have mf t : measurable_fun E (fun x => (W t * G t x)%:E).
  apply: measurable_funTS; apply/measurable_EFinP.
  apply: measurable_funM; first exact: measurable_cst.
  by apply/measurable_EFinP; exact: mG.
have f0 t x : E x -> (0 <= (W t * G t x)%:E)%E.
  by move=> _; rewrite lee_fin mulr_ge0.
rewrite (ge0_integral_sum _ mE mf f0).
rewrite /mixture_probability; apply: eq_bigr => t _.
under eq_integral do rewrite EFinM.
have G0e x : E x -> (0 <= (G t x)%:E)%E by move=> _; rewrite lee_fin.
transitivity ((W t)%:E *
    \int[universality_sample_law (fun=> mu) n d]_(x in E) (G t x)%:E)%E.
  by apply: (ge0_integralZl_EFin _ mE G0e (measurable_funTS (mG t))); exact: W0.
congr (_ * _)%E.
rewrite /mixture_labelled_law /latent_mu /paired_law; symmetry.
exact: (tuple_prod_density (fun k _ => paired_prob_density mu hmu _ (ha t k)) mE).
Qed.

End latent_mixture.

(* 3. The family of mixtures and its fourth moment. *)

Section latent_family.
Variables (s : nat -> R) (mu : probability (measurableTypeR R) R).
Hypothesis hs : forall d, 0 <= s d <= 1.
Hypothesis hmu : paired_uniform_spec mu.

Lemma latent_family :
  mixture_family 3%:R (fun=> 2%N) (fun _ _ => 2^-1)
    (fun d => latent_mu (s d) mu).
Proof.
move=> d; split; first by move=> c _; rewrite invr_ge0 ler0n.
split; first by rewrite sumr_const card_ord -mulr_natr; field.
move=> c j _ _.
exact: (paired_law_component mu hmu _ (latent_param_range _ c (hs d))).
Qed.

Lemma latent_fourth :
  mixture_fourth_moment (9%:R / 5%:R) (fun=> 2%N) (fun _ _ => 2^-1)
    (fun d => latent_mu (s d) mu).
Proof.
move=> d j _ /=.
have hp : - 1 <= s d <= 7%:R / 3%:R := latent_param_range _ 0 (hs d).
have hn : - 1 <= - s d <= 7%:R / 3%:R := latent_param_range _ 1 (hs d).
rewrite big_ord_recr big_ord1 /= /latent_mu /latent_param /=.
rewrite (paired_law_fourth mu hmu _ hp) (paired_law_fourth mu hmu _ hn).
rewrite -!EFinM -EFinD; congr (_%:E).
(* kappa = 9 / 5, an argument of type R, is read in R_scope: Rdiv. *)
have -> : Rdiv 9%:R 5%:R = 9%:R / 5%:R :> R by [].
by field.
Qed.

(* The latent-sign law and the mixture agree on measurable events. *)
Lemma latent_mixtureE (n : nat -> nat)
    (E : forall d, set (paper_main_sample (n d) d)) :
  (forall d, measurable (E d)) ->
  (fun d => latent_probability (s d) mu (n d) d (E d)) =
  (fun d => mixture_probability 2 (fun=> 2^-1) (latent_mu (s d) mu)
              (n d) d (E d)).
Proof.
move=> mE; apply/funext => d.
exact: (latent_probability_mixture (s d) mu (hs d) hmu (n d) d (E d) (mE d)).
Qed.

End latent_family.

(* 4. The latent-sign statement from the finite-mixture theorem. *)

Theorem latent_sign_of_mixture :
  mixture_theorem_statement -> latent_sign_statement.
Proof.
move=> [hM hI] alpha a0.
have k1 : 1 < 9%:R / 5%:R :> R by rewrite ltr_pdivlMr // mul1r ltr_nat.
have K0 : 0 < 3%:R :> R by rewrite ltr0n.
have [h1 h2 [m3 h3]] := hM (9%:R / 5%:R) 3%:R alpha k1 K0 a0.
split.
- move=> ha; have [c [c1 [m1 [m2 h]]]] := h1 ha.
  exists c; split => //; split => //; split => // s hs mu hmu n hn.
  rewrite (latent_mixtureE _ _ hs hmu n _ (fun d => m1 (n d) d)).
  rewrite (latent_mixtureE _ _ hs hmu n _ (fun d => m2 (n d) d)).
  exact: h _ _ _ (latent_family _ _ hs hmu) (latent_fourth _ _ hs hmu) n hn.
- move=> ha; have [e0 [m0 h]] := h2 ha.
  split => //; split => // s hs mu hmu n hn.
  rewrite (latent_mixtureE _ _ hs hmu n _ (fun d => m0 (n d) d)).
  exact: h _ _ _ (latent_family _ _ hs hmu) (latent_fourth _ _ hs hmu) n hn.
- split => // s hs mu hmu n hn e e0.
  rewrite (latent_mixtureE _ _ hs hmu n _ (fun d => m3 (n d) d e)).
  exact: h3 _ _ _ (latent_family _ _ hs hmu) (latent_fourth _ _ hs hmu) n hn
    e e0.
- move=> ah; have [C [C0 hC]] := hI 3%:R alpha K0 a0 ah.
  exists C; split => // s hs mu hmu n hn e e0.
  have [D hD] := hC _ _ _ (latent_family _ _ hs hmu) n hn e e0.
  exists D => d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split => //.
  by rewrite (latent_probability_mixture (s d) mu (hs d) hmu (n d) d E mE).
Qed.
