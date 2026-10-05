(* The fourth trace moment of the centered diagonal block under the actual
   Gaussian law (G15, checkpoint B; manuscript lem:diagonal-feature-block,
   by a fourth trace moment in place of matrix Bernstein).
   Coordinates are lists. For a list ys of length d, u(ys) has the entries
   v(y_a) = y_a^2 - 1 and M(ys) = u u^T - 2 I. For a list xs of n * d
   coordinates, S_n(xs) = sum_(i < n) M(row i of xs). E_D is the iterated
   Gaussian expectation gaussian_iterated_expectation in dimension D.
   - One coordinate factors out: E_D [f(x_a) G] = E f * E_D G when G does
     not depend on x_a (pmdm_factor).
   - E v = 0, E v^2 = 2, E v^4 = 60 and E v^8 <= 2^21, from the polynomial
     moments moment_factor (pmdm_poly_exp).
   - One row: E M = 0, E M^2 = (4 d + 52) I and
     m4 = E tr M^4 <= 2^21 d^4 + 16 d.
   - E S_n = 0 and E tr S_n^2 = n d (4 d + 52), by induction over the rows
     with gaussian_iterated_suffix_expectation.
   - E tr S_n^4 <= n m4 + 3 n (n - 1) d (4 d + 52)^2, from the expansion of
     tr (S + M)^4 and tr (S M S M) <= tr (S^2 M^2) of
     PaperMainDiagonalBlockTrace.
   - For a sample x, D^T D - 2 N I = S_N (tval x) for the diagonal block D
     of PaperMainFeatureGramBlocks.
   Integrability comes from continuity with a polynomial bound
   (pmdf_regular, pmdf_bigsum). No probability premise. *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianExpectation GaussianIntegration GaussianLastDefinitions GaussianLastIntegration
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments PaperMainDefinitions
  PaperMainGeometryHeadCoefficients PaperMainConeConditionOperator
  PaperMainFeatureGramBlocks PaperMainDiagonalBlockTrace.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. One coordinate factors out of the iterated expectation. *)
Lemma pmdm_factor dd a (f : R -> R) (G : list R -> R) :
  (a < dd)%N -> gaussian_integral_exists f -> gaussian_iterated_integrable dd G ->
  (forall xs ys, length xs = dd -> length ys = dd ->
    (forall c, c <> a -> List.nth c xs 0 = List.nth c ys 0) -> G xs = G ys) ->
  gaussian_iterated_expectation dd (fun xs => f (List.nth a xs 0) * G xs) =
  gaussian_expectation f * gaussian_iterated_expectation dd G.
Proof.
elim: dd a G => [|dd IH] a G; first by rewrite ltn0.
move=> Ha Hf [HGs HGo] HG /=.
case: a Ha HG => [|a] Ha HG /=.
  pose g0 := gaussian_iterated_expectation dd (fun xs => G (0 :: xs)).
  have Hsec x : gaussian_iterated_expectation dd (fun xs => G (x :: xs)) = g0.
    apply: gaussian_iterated_expectation_ext => xs Hxs.
    apply: HG; rewrite /= ?Hxs //.
    by case=> [|c] Hc.
  have E1 : (fun x => gaussian_iterated_expectation dd (fun xs => f x * G (x :: xs))) =
      (fun x => g0 * f x).
    apply: functional_extensionality => x.
    rewrite -(Hsec x) [RHS]mulrC.
    exact: (proj2 (gaussian_iterated_scale dd (fun xs => G (x :: xs)) (f x) (HGs x))).
  have E2 : (fun x => gaussian_iterated_expectation dd (fun xs => G (x :: xs))) =
      (fun _ => g0).
    by apply: functional_extensionality => x; exact: Hsec.
  rewrite E1 E2 gaussian_expectation_of_constant [RHS]mulrC.
  exact: (gaussian_expectation_scale f g0 Hf).
have E1 : (fun x => gaussian_iterated_expectation dd
      (fun xs => f (List.nth a xs 0) * G (x :: xs))) =
    (fun x => gaussian_expectation f *
      gaussian_iterated_expectation dd (fun xs => G (x :: xs))).
  apply: functional_extensionality => x.
  apply: (IH a (fun xs => G (x :: xs)) Ha Hf (HGs x)).
  move=> xs ys Hxs Hys Hxy; apply: HG; rewrite /= ?Hxs ?Hys //.
  case=> [|c] Hc //=; apply: Hxy => Hca; apply: Hc; by rewrite Hca.
rewrite E1.
exact: (gaussian_expectation_scale _ (gaussian_expectation f) HGo).
Qed.

Lemma pmdm_marginal dd a (g : R -> R) :
  (a < dd)%N -> gaussian_integral_exists g ->
  gaussian_iterated_expectation dd (fun xs => g (List.nth a xs 0)) = gaussian_expectation g.
Proof.
move=> Ha Hg.
have [HI HE] := gaussian_iterated_constant dd 1%R.
transitivity (gaussian_iterated_expectation dd
  (fun xs => g (List.nth a xs 0) * (fun _ => 1%R) xs)).
  by apply: gaussian_iterated_expectation_ext => xs _; rewrite mulr1.
rewrite (pmdm_factor dd a g (fun _ => 1%R) Ha Hg HI) //.
by rewrite HE mulr1.
Qed.

(* 2. Polynomial moments of the standard Gaussian. *)
Fixpoint pmdm_poly (cs : seq (R * nat)) (x : R) : R :=
  if cs is p :: cs' then (p.1 * x ^+ p.2 + pmdm_poly cs' x)%R else 0%R.

Fixpoint pmdm_poly_moment (cs : seq (R * nat)) : R :=
  if cs is p :: cs' then (p.1 * moment_factor p.2 + pmdm_poly_moment cs')%R else 0%R.

Lemma pmdm_poly_cons c k cs x : pmdm_poly ((c, k) :: cs) x = c * x ^+ k + pmdm_poly cs x.
Proof. by []. Qed.

Lemma pmdm_poly_nil x : pmdm_poly [::] x = 0.
Proof. by []. Qed.

Lemma pmdm_poly_moment_cons c k cs :
  pmdm_poly_moment ((c, k) :: cs) = c * moment_factor k + pmdm_poly_moment cs.
Proof. by []. Qed.

Lemma pmdm_poly_moment_nil : pmdm_poly_moment [::] = 0.
Proof. by []. Qed.

Lemma pmdm_mf0 : moment_factor 0 = 1.
Proof. by []. Qed.

Lemma pmdm_mfS m : moment_factor m.+2 = m.+1%:R * moment_factor m.
Proof. by rewrite -INRE -RmultE. Qed.

Lemma pmdm_pow_moment k :
  gaussian_integral_exists (fun x => x ^+ k) /\
  gaussian_expectation (fun x => x ^+ k) = moment_factor k.
Proof.
have E : (fun x : R => x ^+ k) = (fun x => pow x k).
  by apply: functional_extensionality => x; rewrite RpowE.
have [_ [H1 [_ H2]]] := gaussian_power_moments k.
by rewrite E.
Qed.

Lemma pmdm_poly_exp cs :
  gaussian_integral_exists (pmdm_poly cs) /\
  gaussian_expectation (pmdm_poly cs) = pmdm_poly_moment cs.
Proof.
elim: cs => [|[c k] cs [HI HE]].
  split; first exact: (gaussian_integral_exists_constant 0).
  exact: (gaussian_expectation_of_constant 0).
have [Hk Ek] := pmdm_pow_moment k.
have Hs := gaussian_integral_exists_scale _ c Hk.
split; first exact: (gaussian_integral_exists_add _ _ Hs HI).
have -> : gaussian_expectation (pmdm_poly ((c, k) :: cs)) =
    gaussian_expectation (fun x => c * x ^+ k) + gaussian_expectation (pmdm_poly cs).
  exact: (gaussian_expectation_add _ _ Hs HI).
have -> : gaussian_expectation (fun x => c * x ^+ k) = c * gaussian_expectation (fun x => x ^+ k).
  exact: (gaussian_expectation_scale _ c Hk).
by rewrite HE Ek.
Qed.

(* 3. The moments of v = x^2 - 1. *)
Definition pmdm_v (x : R) : R := (x ^+ 2 - 1)%R.

Lemma pmdm_v_poly_exp k cs :
  (forall x, pmdm_v x ^+ k = pmdm_poly cs x) ->
  gaussian_integral_exists (fun x => pmdm_v x ^+ k) /\
  gaussian_expectation (fun x => pmdm_v x ^+ k) = pmdm_poly_moment cs.
Proof.
move=> H.
have -> : (fun x => pmdm_v x ^+ k) = pmdm_poly cs by exact: functional_extensionality H.
exact: pmdm_poly_exp.
Qed.

Lemma pmdm_v_moment1 :
  gaussian_integral_exists pmdm_v /\ gaussian_expectation pmdm_v = 0.
Proof.
have [HI HE] := pmdm_v_poly_exp 1 [:: (1, 2%N); (-1, 0%N)]
  ltac:(move=> x; rewrite !pmdm_poly_cons pmdm_poly_nil /pmdm_v; ring).
split; first exact: HI.
transitivity (pmdm_poly_moment [:: (1, 2%N); (-1, 0%N)]); first exact: HE.
rewrite !pmdm_poly_moment_cons pmdm_poly_moment_nil !pmdm_mfS !pmdm_mf0; ring.
Qed.

Lemma pmdm_v_moment2 :
  gaussian_integral_exists (fun x => pmdm_v x ^+ 2) /\
  gaussian_expectation (fun x => pmdm_v x ^+ 2) = 2.
Proof.
have [HI HE] := pmdm_v_poly_exp 2 [:: (1, 4%N); (-2, 2%N); (1, 0%N)]
  ltac:(move=> x; rewrite !pmdm_poly_cons pmdm_poly_nil /pmdm_v; ring).
split => //; rewrite HE !pmdm_poly_moment_cons pmdm_poly_moment_nil.
rewrite !pmdm_mfS !pmdm_mf0; ring.
Qed.

Lemma pmdm_v_moment3 : gaussian_integral_exists (fun x => pmdm_v x ^+ 3).
Proof.
have [HI _] := pmdm_v_poly_exp 3 [:: (1, 6%N); (-3, 4%N); (3, 2%N); (-1, 0%N)]
  ltac:(move=> x; rewrite !pmdm_poly_cons pmdm_poly_nil /pmdm_v; ring).
exact: HI.
Qed.

Lemma pmdm_v_moment4 :
  gaussian_integral_exists (fun x => pmdm_v x ^+ 4) /\
  gaussian_expectation (fun x => pmdm_v x ^+ 4) = 60.
Proof.
have [HI HE] := pmdm_v_poly_exp 4
  [:: (1, 8%N); (-4, 6%N); (6, 4%N); (-4, 2%N); (1, 0%N)]
  ltac:(move=> x; rewrite !pmdm_poly_cons pmdm_poly_nil /pmdm_v; ring).
split => //; rewrite HE !pmdm_poly_moment_cons pmdm_poly_moment_nil.
rewrite !pmdm_mfS !pmdm_mf0; ring.
Qed.

Lemma pmdm_v_moment8 :
  gaussian_integral_exists (fun x => pmdm_v x ^+ 8) /\
  gaussian_expectation (fun x => pmdm_v x ^+ 8) <= 2 ^+ 21.
Proof.
have [HI HE] := pmdm_v_poly_exp 8
  [:: (1, 16%N); (-8, 14%N); (28, 12%N); (-56, 10%N); (70, 8%N); (-56, 6%N);
      (28, 4%N); (-8, 2%N); (1, 0%N)]
  ltac:(move=> x; rewrite !pmdm_poly_cons pmdm_poly_nil /pmdm_v; ring).
split => //; rewrite HE !pmdm_poly_moment_cons pmdm_poly_moment_nil.
rewrite !pmdm_mfS !pmdm_mf0; lra.
Qed.

(* 4. Ring forms of linearity and of continuity with a polynomial bound. *)
Section Regular.
Variable D : nat.
Implicit Types (F G : list R -> R).

Lemma pmdm_reg_const c : pmdf_regular D (fun _ => c).
Proof. exact: pmdf_regular_const. Qed.

Lemma pmdm_reg_nth i : (i < D)%N -> pmdf_regular D (fun xs => List.nth i xs 0).
Proof. by move=> Hi; apply: pmdf_regular_nth; apply/ssrnat.ltP. Qed.

Lemma pmdm_reg_add F G :
  pmdf_regular D F -> pmdf_regular D G -> pmdf_regular D (fun xs => F xs + G xs).
Proof. exact: pmdf_regular_add. Qed.

Lemma pmdm_reg_mul F G :
  pmdf_regular D F -> pmdf_regular D G -> pmdf_regular D (fun xs => F xs * G xs).
Proof. exact: pmdf_regular_mult. Qed.

Lemma pmdm_reg_scale c F : pmdf_regular D F -> pmdf_regular D (fun xs => c * F xs).
Proof. exact: pmdf_regular_scale. Qed.

Lemma pmdm_reg_opp F : pmdf_regular D F -> pmdf_regular D (fun xs => - F xs).
Proof.
move=> HF; apply: (pmdf_regular_ext _ (fun xs => (-1) * F xs)) => [xs|].
  by rewrite mulN1r.
exact: pmdm_reg_scale.
Qed.

Lemma pmdm_reg_sub F G :
  pmdf_regular D F -> pmdf_regular D G -> pmdf_regular D (fun xs => F xs - G xs).
Proof. by move=> HF HG; apply: pmdm_reg_add => //; exact: pmdm_reg_opp. Qed.

Lemma pmdm_reg_exp F k : pmdf_regular D F -> pmdf_regular D (fun xs => F xs ^+ k).
Proof.
move=> HF; elim: k => [|k IH].
  apply: (pmdf_regular_ext _ (fun _ => 1)) => [xs|]; first by rewrite expr0.
  exact: pmdm_reg_const.
apply: (pmdf_regular_ext _ (fun xs => F xs * F xs ^+ k)) => [xs|]; first by rewrite exprS.
exact: pmdm_reg_mul.
Qed.

Lemma pmdm_reg_v i : (i < D)%N -> pmdf_regular D (fun xs => pmdm_v (List.nth i xs 0)).
Proof.
move=> Hi; rewrite /pmdm_v.
apply: pmdm_reg_sub; last exact: pmdm_reg_const.
by apply: pmdm_reg_exp; exact: pmdm_reg_nth.
Qed.

Lemma pmdm_E_const c : gaussian_iterated_expectation D (fun _ => c) = c.
Proof. exact: (proj2 (gaussian_iterated_constant D c)). Qed.

Lemma pmdm_E_add F G : pmdf_regular D F -> pmdf_regular D G ->
  gaussian_iterated_expectation D (fun xs => F xs + G xs) =
  gaussian_iterated_expectation D F + gaussian_iterated_expectation D G.
Proof.
move=> /pmdf_regular_integrable HF /pmdf_regular_integrable HG.
exact: (proj2 (gaussian_iterated_add D F G HF HG)).
Qed.

Lemma pmdm_E_scale c F : pmdf_regular D F ->
  gaussian_iterated_expectation D (fun xs => c * F xs) =
  c * gaussian_iterated_expectation D F.
Proof.
move=> /pmdf_regular_integrable HF.
exact: (proj2 (gaussian_iterated_scale D F c HF)).
Qed.

Lemma pmdm_E_le F G : pmdf_regular D F -> pmdf_regular D G ->
  (forall xs, length xs = D -> F xs <= G xs) ->
  gaussian_iterated_expectation D F <= gaussian_iterated_expectation D G.
Proof.
move=> /pmdf_regular_integrable HF /pmdf_regular_integrable HG H.
apply/RleP; apply: gaussian_iterated_monotone => // xs Hxs.
by apply/RleP; exact: H.
Qed.

Lemma pmdm_E_sum m (F : 'I_m -> list R -> R) :
  (forall i, pmdf_regular D (F i)) ->
  gaussian_iterated_expectation D (fun xs => \sum_(i < m) F i xs) =
  \sum_(i < m) gaussian_iterated_expectation D (F i).
Proof. by move=> HF; have [_ H] := pmdf_bigsum D m F HF. Qed.

Lemma pmdm_reg_sum m (F : 'I_m -> list R -> R) :
  (forall i, pmdf_regular D (F i)) -> pmdf_regular D (fun xs => \sum_(i < m) F i xs).
Proof. by move=> HF; have [H _] := pmdf_bigsum D m F HF. Qed.

(* Matrix-valued functions, entry by entry. *)
Definition pmdm_mreg {m k} (A : list R -> 'M[R]_(m, k)) : Prop :=
  forall a b, pmdf_regular D (fun xs => A xs a b).

Definition pmdm_mexp {m k} (A : list R -> 'M[R]_(m, k)) : 'M[R]_(m, k) :=
  \matrix_(a, b) gaussian_iterated_expectation D (fun xs => A xs a b).

Lemma pmdm_mreg_const {m k} (C : 'M[R]_(m, k)) : pmdm_mreg (fun _ => C).
Proof. by move=> a b; exact: pmdm_reg_const. Qed.

Lemma pmdm_mreg_add {m k} (A B : list R -> 'M[R]_(m, k)) :
  pmdm_mreg A -> pmdm_mreg B -> pmdm_mreg (fun xs => A xs + B xs).
Proof.
move=> HA HB a b; apply: (pmdf_regular_ext _ (fun xs => A xs a b + B xs a b)) => [xs|].
  by rewrite mxE.
exact: pmdm_reg_add.
Qed.

Lemma pmdm_mreg_sub {m k} (A B : list R -> 'M[R]_(m, k)) :
  pmdm_mreg A -> pmdm_mreg B -> pmdm_mreg (fun xs => A xs - B xs).
Proof.
move=> HA HB a b; apply: (pmdf_regular_ext _ (fun xs => A xs a b - B xs a b)) => [xs|].
  by rewrite !mxE.
exact: pmdm_reg_sub.
Qed.

Lemma pmdm_mreg_scale {m k} c (A : list R -> 'M[R]_(m, k)) :
  pmdm_mreg A -> pmdm_mreg (fun xs => c *: A xs).
Proof.
move=> HA a b; apply: (pmdf_regular_ext _ (fun xs => c * A xs a b)) => [xs|].
  by rewrite mxE.
exact: pmdm_reg_scale.
Qed.

Lemma pmdm_mreg_mul {m k l} (A : list R -> 'M[R]_(m, k)) (B : list R -> 'M[R]_(k, l)) :
  pmdm_mreg A -> pmdm_mreg B -> pmdm_mreg (fun xs => A xs *m B xs).
Proof.
move=> HA HB a b.
apply: (pmdf_regular_ext _ (fun xs => \sum_(c < k) A xs a c * B xs c b)) => [xs|].
  by rewrite mxE.
by apply: pmdm_reg_sum => c; exact: pmdm_reg_mul.
Qed.

Lemma pmdm_mreg_trmx {m k} (A : list R -> 'M[R]_(m, k)) :
  pmdm_mreg A -> pmdm_mreg (fun xs => (A xs)^T).
Proof.
move=> HA a b; apply: (pmdf_regular_ext _ (fun xs => A xs b a)) => [xs|].
  by rewrite mxE.
exact: HA.
Qed.

Lemma pmdm_mreg_sum {m k} n (A : 'I_n -> list R -> 'M[R]_(m, k)) :
  (forall i, pmdm_mreg (A i)) -> pmdm_mreg (fun xs => \sum_(i < n) A i xs).
Proof.
move=> HA a b; apply: (pmdf_regular_ext _ (fun xs => \sum_(i < n) A i xs a b)) => [xs|].
  by rewrite summxE.
by apply: pmdm_reg_sum => i; exact: HA.
Qed.

Lemma pmdm_mreg_tr {m} (A : list R -> 'M[R]_m) :
  pmdm_mreg A -> pmdf_regular D (fun xs => \tr (A xs)).
Proof.
move=> HA; apply: (pmdf_regular_ext _ (fun xs => \sum_(a < m) A xs a a)) => [xs //|].
by apply: pmdm_reg_sum => a; exact: HA.
Qed.

Lemma pmdm_E_tr_mul {m k} (C : 'M[R]_(m, k)) (A : list R -> 'M[R]_(k, m)) :
  pmdm_mreg A ->
  gaussian_iterated_expectation D (fun xs => \tr (C *m A xs)) = \tr (C *m pmdm_mexp A).
Proof.
move=> HA.
have Hc a : forall c, pmdf_regular D (fun xs => C a c * A xs c a).
  by move=> c; exact: pmdm_reg_scale.
have Ha : forall a, pmdf_regular D (fun xs => \sum_(c < k) C a c * A xs c a).
  by move=> a; apply: pmdm_reg_sum; exact: Hc.
transitivity (gaussian_iterated_expectation D
  (fun xs => \sum_(a < m) \sum_(c < k) C a c * A xs c a)).
  by apply: gaussian_iterated_expectation_ext => xs _; apply: eq_bigr => a _; rewrite mxE.
rewrite (pmdm_E_sum _ _ Ha); apply: eq_bigr => a _; rewrite mxE (pmdm_E_sum _ _ (Hc a)).
by apply: eq_bigr => c _; rewrite pmdm_E_scale // mxE.
Qed.

(* Splitting off the last k coordinates. *)
Lemma pmdm_split_eq k (F G : list R -> R) :
  (forall xs, length xs = D ->
    gaussian_iterated_expectation k (fun ys => F (xs ++ ys)) = G xs) ->
  gaussian_iterated_expectation (Nat.add D k) F = gaussian_iterated_expectation D G.
Proof.
move=> H; rewrite gaussian_iterated_suffix_expectation.
exact: gaussian_iterated_expectation_ext.
Qed.

Lemma pmdm_split_le k (F G : list R -> R) :
  pmdf_regular (Nat.add D k) F -> pmdf_regular D G ->
  (forall xs, length xs = D ->
    gaussian_iterated_expectation k (fun ys => F (xs ++ ys)) <= G xs) ->
  gaussian_iterated_expectation (Nat.add D k) F <= gaussian_iterated_expectation D G.
Proof.
move=> /pmdf_regular_integrable HF /pmdf_regular_integrable HG H.
rewrite gaussian_iterated_suffix_expectation.
have [_ HM] := proj1 (gaussian_iterated_suffix_integrable D k F) HF.
apply/RleP; apply: gaussian_iterated_monotone => // xs Hxs.
by apply/RleP; exact: H.
Qed.

End Regular.

(* 5. One row: the definitions. *)
Section Row.
Variable d : nat.

Definition pmdm_u (ys : list R) : 'cV[R]_d := \col_(a < d) pmdm_v (List.nth a ys 0).

Definition pmdm_M (ys : list R) : 'M[R]_d := pmdm_u ys *m (pmdm_u ys)^T - 2 *: 1%:M.

Definition pmdm_K : R := (4 * d%:R + 52)%R.

Lemma pmdm_u_reg : pmdm_mreg d pmdm_u.
Proof.
move=> a b; apply: (pmdf_regular_ext _ (fun ys => pmdm_v (List.nth a ys 0))) => [ys|].
  by rewrite mxE.
exact: pmdm_reg_v.
Qed.

Lemma pmdm_M_reg : pmdm_mreg d pmdm_M.
Proof.
apply: pmdm_mreg_sub; last exact: pmdm_mreg_const.
by apply: pmdm_mreg_mul; [exact: pmdm_u_reg | apply: pmdm_mreg_trmx; exact: pmdm_u_reg].
Qed.

Lemma pmdm_M_sym ys : (pmdm_M ys)^T = pmdm_M ys.
Proof. by rewrite /pmdm_M linearB /= trmx_mul trmxK linearZ /= trmx1. Qed.

Lemma pmdm_M_entry ys (a b : 'I_d) :
  pmdm_M ys a b = pmdm_v (List.nth a ys 0) * pmdm_v (List.nth b ys 0) - 2 * (a == b)%:R.
Proof. by rewrite !mxE big_ord1 !mxE. Qed.

Lemma pmdm_neq (a b : 'I_d) : b != a -> (b : nat) <> a.
Proof. by move=> /eqP Hba Hc; apply: Hba; exact: val_inj. Qed.

End Row.

(* 6. Rows of a list of n * d coordinates. *)
Section Rows.
Variable d : nat.

Definition pmdm_urow (i : nat) (xs : list R) : 'cV[R]_d :=
  \col_(a < d) pmdm_v (List.nth (i * d + a)%N xs 0).

Definition pmdm_S (n : nat) (xs : list R) : 'M[R]_d :=
  \sum_(i < n) (pmdm_urow i xs *m (pmdm_urow i xs)^T - 2 *: 1%:M).

Lemma pmdm_index_lt n i a : (i < n)%N -> (a < d)%N -> (i * d + a < n * d)%N.
Proof.
move=> Hi Ha; apply: (@leq_trans (i.+1 * d)).
  by rewrite mulSn addnC ltn_add2r.
by rewrite leq_mul2r Hi orbT.
Qed.

Lemma pmdm_urow_reg n i : (i < n)%N -> pmdm_mreg (n * d) (pmdm_urow i).
Proof.
move=> Hi a b.
apply: (pmdf_regular_ext _ (fun xs => pmdm_v (List.nth (i * d + a)%N xs 0))) => [xs|].
  by rewrite mxE.
exact: (pmdm_reg_v _ _ (pmdm_index_lt n i a Hi (ltn_ord a))).
Qed.

Lemma pmdm_S_reg n : pmdm_mreg (n * d) (pmdm_S n).
Proof.
apply: pmdm_mreg_sum => i.
apply: pmdm_mreg_sub; last exact: pmdm_mreg_const.
apply: pmdm_mreg_mul; first exact: (pmdm_urow_reg n i (ltn_ord i)).
by apply: pmdm_mreg_trmx; exact: (pmdm_urow_reg n i (ltn_ord i)).
Qed.

Lemma pmdm_S_sym n xs : (pmdm_S n xs)^T = pmdm_S n xs.
Proof.
rewrite /pmdm_S raddf_sum; apply: eq_bigr => i _ /=.
by rewrite linearB /= trmx_mul trmxK linearZ /= trmx1.
Qed.

Lemma pmdm_urow_app_lt n i xs ys : length xs = (n * d)%N -> (i < n)%N ->
  pmdm_urow i (xs ++ ys) = pmdm_urow i xs.
Proof.
move=> Hxs Hi; apply/matrixP => a b; rewrite !mxE List.app_nth1 //.
by rewrite Hxs; apply/ssrnat.ltP; exact: (pmdm_index_lt n i a Hi (ltn_ord a)).
Qed.

Lemma pmdm_urow_app_last n xs ys : length xs = (n * d)%N ->
  pmdm_urow n (xs ++ ys) = pmdm_u d ys.
Proof.
move=> Hxs; apply/matrixP => a b; rewrite !mxE -Hxs -plusE.
by rewrite List.app_nth2_plus.
Qed.

Lemma pmdm_S_app n xs ys : length xs = (n * d)%N ->
  pmdm_S n.+1 (xs ++ ys) = pmdm_S n xs + pmdm_M d ys.
Proof.
move=> Hxs; rewrite /pmdm_S big_ord_recr /= (pmdm_urow_app_last n xs ys Hxs) /pmdm_M.
congr (_ + _); apply: eq_bigr => i _.
by rewrite (pmdm_urow_app_lt n i xs ys Hxs (ltn_ord i)).
Qed.

Lemma pmdm_S0 xs : pmdm_S 0 xs = 0.
Proof. by rewrite /pmdm_S big_ord0. Qed.

End Rows.

(* Regularity goals for the polynomial matrix functions. *)
Ltac pmdm_regt :=
  repeat first
    [ exact: pmdm_reg_const | exact: pmdm_mreg_const
    | exact: pmdm_M_reg | exact: pmdm_u_reg | exact: pmdm_S_reg
    | exact: (pmdm_reg_v _ _ (ltn_ord _))
    | apply: pmdm_mreg_tr | apply: pmdm_mreg_mul | apply: pmdm_mreg_add
    | apply: pmdm_mreg_sub | apply: pmdm_mreg_scale | apply: pmdm_mreg_trmx
    | apply: pmdm_reg_add | apply: pmdm_reg_mul | apply: pmdm_reg_sub
    | apply: pmdm_reg_exp ].

(* 7. One-row moments. *)
Section Moments.
Variable d : nat.
Local Notation M := (pmdm_M d).
Local Notation K := (pmdm_K d).

Lemma pmdm_row_mean1 (b : 'I_d) :
  gaussian_iterated_expectation d (fun ys => pmdm_v (List.nth b ys 0)) = 0.
Proof.
have [H1 E1] := pmdm_v_moment1.
by rewrite (pmdm_marginal d b pmdm_v (ltn_ord b) H1) E1.
Qed.

(* E v_a v_b = 2 delta_ab. *)
Lemma pmdm_row_moment2 (a b : 'I_d) :
  gaussian_iterated_expectation d
    (fun ys => pmdm_v (List.nth a ys 0) * pmdm_v (List.nth b ys 0)) = 2 * (a == b)%:R.
Proof.
have [H1 E1] := pmdm_v_moment1.
have [H2 E2] := pmdm_v_moment2.
case: (eqVneq a b) => [<-|Hab] /=.
  transitivity (gaussian_iterated_expectation d
    (fun ys => (fun x => pmdm_v x ^+ 2) (List.nth a ys 0))).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite -expr2.
  by rewrite (pmdm_marginal d a _ (ltn_ord a) H2) E2 mulr1.
have Hba : b != a by rewrite eq_sym.
rewrite (pmdm_factor d a pmdm_v (fun ys => pmdm_v (List.nth b ys 0)) (ltn_ord a) H1
  (pmdf_regular_integrable (pmdm_reg_v d b (ltn_ord b)))).
  by move=> xs ys _ _ Hxy; congr (pmdm_v _); exact: (Hxy _ (pmdm_neq d a b Hba)).
by rewrite E1 mul0r mulr0.
Qed.

Lemma pmdm_M_mean : pmdm_mexp d M = 0.
Proof.
apply/matrixP => a b; rewrite !mxE.
transitivity (gaussian_iterated_expectation d (fun ys =>
  pmdm_v (List.nth a ys 0) * pmdm_v (List.nth b ys 0) + (- (2 * (a == b)%:R)))).
  by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmdm_M_entry.
rewrite pmdm_E_add; [by pmdm_regt | exact: pmdm_reg_const |].
by rewrite pmdm_E_const pmdm_row_moment2 subrr.
Qed.

(* E v_c^2 v_a v_b = delta_ab (4 + 56 delta_ca). *)
Lemma pmdm_row_moment4 (a b c : 'I_d) :
  gaussian_iterated_expectation d (fun ys =>
    pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0) *
    (pmdm_v (List.nth a ys 0) * pmdm_v (List.nth b ys 0))) =
  (a == b)%:R * (4 + 56 * (c == a)%:R).
Proof.
have [H1 E1] := pmdm_v_moment1.
have [H2 E2] := pmdm_v_moment2.
have H3 := pmdm_v_moment3.
have [H4 E4] := pmdm_v_moment4.
case: (eqVneq a b) => [<-|Hab] /=.
  case: (eqVneq c a) => [->|Hca] /=.
    transitivity (gaussian_iterated_expectation d
      (fun ys => (fun x => pmdm_v x ^+ 4) (List.nth a ys 0))).
      by apply: gaussian_iterated_expectation_ext => ys _; cbv beta; ring.
    rewrite (pmdm_marginal d a _ (ltn_ord a) H4) E4; ring.
  transitivity (gaussian_iterated_expectation d (fun ys =>
    (fun x => pmdm_v x ^+ 2) (List.nth a ys 0) *
    (pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0)))).
    by apply: gaussian_iterated_expectation_ext => ys _; cbv beta; ring.
  rewrite (pmdm_factor d a _ (fun ys => pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0))
    (ltn_ord a) H2).
  - by apply: pmdf_regular_integrable; pmdm_regt.
  - by move=> xs ys _ _ Hxy; rewrite (Hxy _ (pmdm_neq d a c Hca)).
  by rewrite E2 pmdm_row_moment2 eqxx /=; ring.
rewrite mul0r.
have Hba : b != a by rewrite eq_sym.
case: (eqVneq c a) => [->|Hca].
  transitivity (gaussian_iterated_expectation d (fun ys =>
    (fun x => pmdm_v x ^+ 3) (List.nth a ys 0) * pmdm_v (List.nth b ys 0))).
    by apply: gaussian_iterated_expectation_ext => ys _; cbv beta; ring.
  rewrite (pmdm_factor d a _ (fun ys => pmdm_v (List.nth b ys 0)) (ltn_ord a) H3
    (pmdf_regular_integrable (pmdm_reg_v d b (ltn_ord b)))).
    by move=> xs ys _ _ Hxy; rewrite (Hxy _ (pmdm_neq d a b Hba)).
  by rewrite pmdm_row_mean1 mulr0.
transitivity (gaussian_iterated_expectation d (fun ys =>
  pmdm_v (List.nth a ys 0) *
  (pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0) * pmdm_v (List.nth b ys 0)))).
  by apply: gaussian_iterated_expectation_ext => ys _; ring.
rewrite (pmdm_factor d a pmdm_v (fun ys =>
  pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0) * pmdm_v (List.nth b ys 0))
  (ltn_ord a) H1).
- by apply: pmdf_regular_integrable; pmdm_regt.
- move=> xs ys _ _ Hxy.
  by rewrite (Hxy _ (pmdm_neq d a c Hca)) (Hxy _ (pmdm_neq d a b Hba)).
by rewrite E1 mul0r.
Qed.

Lemma pmdm_M_sq_mean : pmdm_mexp d (fun ys => M ys *m M ys) = K *: 1%:M.
Proof.
apply/matrixP => a b; rewrite !mxE.
pose X (c : 'I_d) ys := pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0) *
  (pmdm_v (List.nth a ys 0) * pmdm_v (List.nth b ys 0)).
transitivity (gaussian_iterated_expectation d (fun ys =>
  \sum_(c < d) X c ys +
  ((-4) * (pmdm_v (List.nth a ys 0) * pmdm_v (List.nth b ys 0)) + 4 * (a == b)%:R))).
  apply: gaussian_iterated_expectation_ext => ys _.
  rewrite /pmdm_M pmdb_rank1_sq !mxE big_ord1 !mxE /X -mulr_suml.
  have -> : \sum_(j < d) (pmdm_u d ys)^T 0 j * pmdm_u d ys j 0 =
      \sum_(c < d) pmdm_v (List.nth c ys 0) * pmdm_v (List.nth c ys 0).
    by apply: eq_bigr => c _; rewrite !mxE.
  ring.
have RX c : pmdf_regular d (X c) by rewrite /X; pmdm_regt.
rewrite pmdm_E_add; [exact: (pmdm_reg_sum d d X RX) | by pmdm_regt |].
rewrite (pmdm_E_sum d d X RX).
rewrite pmdm_E_add; [by pmdm_regt | exact: pmdm_reg_const |].
rewrite pmdm_E_scale; [by pmdm_regt |].
rewrite pmdm_E_const pmdm_row_moment2.
have -> : \sum_(c < d) gaussian_iterated_expectation d (X c) =
    \sum_(c < d) ((a == b)%:R * (4 + 56 * (c == a)%:R)).
  by apply: eq_bigr => c _; exact: pmdm_row_moment4.
rewrite -mulr_sumr big_split /= sumr_const card_ord -mulr_sumr.
have -> : \sum_(c < d) (c == a)%:R = 1 :> R.
  rewrite (bigD1 a) //= eqxx big1 ?addr0 // => c Hc.
  by rewrite (negbTE Hc).
rewrite /pmdm_K -mulr_natr; ring.
Qed.

(* The step for the first moment. *)
Lemma pmdm_step1 (S : 'M[R]_d) a b :
  gaussian_iterated_expectation d (fun ys => (S + M ys) a b) = S a b.
Proof.
transitivity (gaussian_iterated_expectation d (fun ys => S a b + M ys a b)).
  by apply: gaussian_iterated_expectation_ext => ys _; rewrite mxE.
rewrite pmdm_E_add; [exact: pmdm_reg_const | exact: (pmdm_M_reg d a b) |].
rewrite pmdm_E_const.
by move: pmdm_M_mean => /matrixP/(_ a b); rewrite !mxE => ->; rewrite addr0.
Qed.

(* The step for the second trace moment. *)
Lemma pmdm_step2 (S : 'M[R]_d) :
  gaussian_iterated_expectation d (fun ys => \tr ((S + M ys) *m (S + M ys))) =
  \tr (S *m S) + d%:R * K.
Proof.
transitivity (gaussian_iterated_expectation d (fun ys =>
  \tr (S *m S) + (2 * \tr (S *m M ys) + \tr (1%:M *m (M ys *m M ys))))).
  apply: gaussian_iterated_expectation_ext => ys _.
  rewrite mulmxDl (mulmxDr S S (M ys)) (mulmxDr (M ys) S (M ys)) !mxtraceD mul1mx.
  rewrite (mxtrace_mulC (M ys) S); ring.
rewrite pmdm_E_add; try by pmdm_regt.
rewrite pmdm_E_const pmdm_E_add; try by pmdm_regt.
rewrite pmdm_E_scale; try by pmdm_regt.
rewrite !pmdm_E_tr_mul; try by pmdm_regt.
rewrite pmdm_M_mean pmdm_M_sq_mean mulmx0 mul1mx pmdb_tr_scalar mxtrace0; ring.
Qed.

Definition pmdm_m4 : R :=
  gaussian_iterated_expectation d (fun ys => \tr (M ys *m M ys *m M ys *m M ys)).

Definition pmdm_C3 : 'M[R]_d := pmdm_mexp d (fun ys => M ys *m M ys *m M ys).

(* The step for the fourth trace moment. *)
Lemma pmdm_step4 (S : 'M[R]_d) : S^T = S ->
  gaussian_iterated_expectation d (fun ys =>
    \tr ((S + M ys) *m (S + M ys) *m (S + M ys) *m (S + M ys))) <=
  \tr (S *m S *m S *m S) + 6 * K * \tr (S *m S) + 4 * \tr (S *m pmdm_C3) + pmdm_m4.
Proof.
move=> HS.
pose H ys := \tr (S *m S *m S *m S) +
  (4 * \tr ((S *m S *m S) *m M ys) + (6 * \tr ((S *m S) *m (M ys *m M ys)) +
  (4 * \tr (S *m (M ys *m M ys *m M ys)) + \tr (M ys *m M ys *m M ys *m M ys)))).
have RH : pmdf_regular d H by rewrite /H; pmdm_regt.
have HE : gaussian_iterated_expectation d H =
    \tr (S *m S *m S *m S) + 6 * K * \tr (S *m S) + 4 * \tr (S *m pmdm_C3) + pmdm_m4.
  rewrite /H pmdm_E_add; [exact: pmdm_reg_const | by pmdm_regt |].
  rewrite pmdm_E_const pmdm_E_add; [by pmdm_regt | by pmdm_regt |].
  rewrite pmdm_E_scale; [by pmdm_regt |].
  rewrite pmdm_E_add; [by pmdm_regt | by pmdm_regt |].
  rewrite pmdm_E_scale; [by pmdm_regt |].
  rewrite pmdm_E_add; [by pmdm_regt | by pmdm_regt |].
  rewrite pmdm_E_scale; [by pmdm_regt |].
  rewrite !pmdm_E_tr_mul; try by pmdm_regt.
  rewrite pmdm_M_mean pmdm_M_sq_mean mulmx0 mxtrace0 -scalemxAr mulmx1 mxtraceZ.
  rewrite /pmdm_m4 /pmdm_C3; ring.
rewrite -HE; apply: pmdm_E_le => [| |ys _]; [by pmdm_regt | exact: RH |].
rewrite paper_main_trace_fourth_expand /H.
have Hab := paper_main_trace_abab d S (M ys) HS (pmdm_M_sym d ys).
rewrite !mulmxA in Hab *.
lra.
Qed.

(* m4 <= 2^21 d^4 + 16 d. *)
Lemma pmdm_sum_sq m (w : 'I_m -> R) : (\sum_i w i) ^+ 2 <= m%:R * \sum_i w i ^+ 2.
Proof.
have CS := pmco_vec_cauchy_schwarz m (const_mx 1) (\col_i w i).
rewrite !pmh_vec_dot in CS.
have E1 : \sum_(i < m) (const_mx 1 : 'cV[R]_m) i 0 * (\col_i w i) i 0 = \sum_i w i.
  by apply: eq_bigr => i _; rewrite !mxE mul1r.
have E2 : \sum_(i < m) (const_mx 1 : 'cV[R]_m) i 0 * (const_mx 1 : 'cV[R]_m) i 0 = m%:R.
  rewrite (eq_bigr (fun _ => 1)); first by move=> i _; rewrite !mxE mulr1.
  by rewrite sumr_const card_ord.
have E3 : \sum_(i < m) (\col_i w i) i 0 * (\col_i w i) i 0 = \sum_i w i ^+ 2.
  by apply: eq_bigr => i _; rewrite !mxE expr2.
by rewrite E1 E2 E3 in CS.
Qed.

Lemma pmdm_sum_pow4 m (w : 'I_m -> R) : (\sum_i w i) ^+ 4 <= m%:R ^+ 3 * \sum_i w i ^+ 4.
Proof.
have H1 := pmdm_sum_sq m w.
have H2 := pmdm_sum_sq m (fun i => w i ^+ 2).
have Hm : 0 <= m%:R :> R by exact: ler0n.
have HA : 0 <= (\sum_i w i) ^+ 2 by exact: sqr_ge0.
have HB : 0 <= \sum_i w i ^+ 2 by apply: sumr_ge0 => i _; exact: sqr_ge0.
have E4 : \sum_i (w i ^+ 2) ^+ 2 = \sum_i w i ^+ 4.
  by apply: eq_bigr => i _; rewrite -exprM.
rewrite E4 in H2.
have -> : (\sum_i w i) ^+ 4 = ((\sum_i w i) ^+ 2) ^+ 2 by rewrite -exprM.
set A := (\sum_i w i) ^+ 2 in H1 HA *.
set B := \sum_i w i ^+ 2 in H1 H2 HB *.
set C := \sum_i w i ^+ 4 in H2 *.
have HAB : A ^+ 2 <= (m%:R * B) ^+ 2.
  by rewrite ler_sqr ?nnegrE //; apply: mulr_ge0.
have HB2 : (m%:R * B) ^+ 2 <= m%:R ^+ 3 * C.
  have -> : (m%:R * B) ^+ 2 = m%:R ^+ 2 * B ^+ 2 by ring.
  have -> : m%:R ^+ 3 * C = m%:R ^+ 2 * (m%:R * C) by ring.
  by apply: ler_wpM2l => //; exact: exprn_ge0.
exact: le_trans HAB HB2.
Qed.

Lemma pmdm_m4_bound : pmdm_m4 <= 2 ^+ 21 * d%:R ^+ 4 + 16 * d%:R.
Proof.
have [H8 E8] := pmdm_v_moment8.
pose H ys := d%:R ^+ 3 * \sum_(a < d) pmdm_v (List.nth a ys 0) ^+ 8 + 16 * d%:R.
have R8 : forall a : 'I_d, pmdf_regular d (fun ys => pmdm_v (List.nth a ys 0) ^+ 8).
  by move=> a; apply: pmdm_reg_exp; exact: pmdm_reg_v.
have RH : pmdf_regular d H.
  rewrite /H; apply: pmdm_reg_add; last exact: pmdm_reg_const.
  apply: pmdm_reg_mul; first exact: pmdm_reg_const.
  exact: pmdm_reg_sum.
apply: (@le_trans _ _ (gaussian_iterated_expectation d H)).
  apply: pmdm_E_le => [| |ys _]; [by pmdm_regt | exact: RH |].
  rewrite /M /pmdm_M paper_main_rank_one_trace_fourth pmh_vec_dot /H.
  set s := \sum_(i < d) pmdm_u d ys i 0 * pmdm_u d ys i 0.
  have Hs : s = \sum_(a < d) pmdm_v (List.nth a ys 0) * pmdm_v (List.nth a ys 0).
    by apply: eq_bigr => a _; rewrite !mxE.
  have Hs0 : 0 <= s.
    by rewrite Hs; apply: sumr_ge0 => a _; rewrite -expr2; exact: sqr_ge0.
  have Hs4 : (s - 2) ^+ 4 <= s ^+ 4 + 16.
    have Hh : 0 <= s * (2 * s - 3) ^+ 2 by apply: mulr_ge0 => //; exact: sqr_ge0.
    nra.
  have Hpm : s ^+ 4 <= d%:R ^+ 3 * \sum_(a < d) pmdm_v (List.nth a ys 0) ^+ 8.
    have E8' : \sum_(a < d) (pmdm_v (List.nth a ys 0) * pmdm_v (List.nth a ys 0)) ^+ 4 =
        \sum_(a < d) pmdm_v (List.nth a ys 0) ^+ 8.
      by apply: eq_bigr => a _; ring.
    rewrite Hs -E8'; exact: pmdm_sum_pow4.
  lra.
rewrite /H pmdm_E_add; [| exact: pmdm_reg_const |].
  by apply: pmdm_reg_mul; [exact: pmdm_reg_const | exact: pmdm_reg_sum].
rewrite pmdm_E_scale; [exact: (pmdm_reg_sum d d _ R8) |].
rewrite (pmdm_E_sum d d _ R8) pmdm_E_const.
have -> : \sum_(a < d) gaussian_iterated_expectation d
    (fun ys => pmdm_v (List.nth a ys 0) ^+ 8) =
    \sum_(a < d) gaussian_expectation (fun x => pmdm_v x ^+ 8).
  by apply: eq_bigr => a _; exact: (pmdm_marginal d a (fun x => pmdm_v x ^+ 8) (ltn_ord a) H8).
rewrite sumr_const card_ord -[gaussian_expectation _ *+ d]mulr_natr.
have Hd : 0 <= d%:R :> R by exact: ler0n.
have Hd3 : 0 <= d%:R ^+ 3 :> R by exact: exprn_ge0.
have Hb : d%:R ^+ 3 * (gaussian_expectation (fun x => pmdm_v x ^+ 8) * d%:R) <=
    d%:R ^+ 3 * (2 ^+ 21 * d%:R).
  by apply: ler_wpM2l => //; apply: ler_wpM2r.
have -> : 2 ^+ 21 * d%:R ^+ 4 = d%:R ^+ 3 * (2 ^+ 21 * d%:R) :> R by ring.
lra.
Qed.

End Moments.

(* 8. The induction over the rows. *)
Section Induction.
Variable d : nat.
Local Notation S := (pmdm_S d).
Local Notation K := (pmdm_K d).

Lemma pmdm_dim n : (n.+1 * d)%N = Nat.add (n * d)%N d.
Proof. by rewrite mulSnr. Qed.

Lemma pmdm_S_mean n : pmdm_mexp (n * d) (S n) = 0.
Proof.
elim: n => [|n IH].
  apply/matrixP => a b; rewrite !mxE mul0n /=.
  by rewrite pmdm_S0 mxE.
apply/matrixP => a b; rewrite !mxE pmdm_dim.
have Hstep : forall xs, length xs = (n * d)%N ->
    gaussian_iterated_expectation d (fun ys => S n.+1 (xs ++ ys) a b) = S n xs a b.
  move=> xs Hxs.
  transitivity (gaussian_iterated_expectation d (fun ys => (S n xs + pmdm_M d ys) a b)).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmdm_S_app.
  exact: pmdm_step1.
rewrite (pmdm_split_eq _ _ _ _ Hstep).
transitivity (pmdm_mexp (n * d) (S n) a b); first by rewrite mxE.
by rewrite IH mxE.
Qed.

Lemma pmdm_S_trace2 n :
  gaussian_iterated_expectation (n * d) (fun xs => \tr (S n xs *m S n xs)) =
  n%:R * (d%:R * K).
Proof.
elim: n => [|n IH].
  by rewrite mul0n /= pmdm_S0 mul0mx mxtrace0 mul0r.
have Hstep : forall xs, length xs = (n * d)%N ->
    gaussian_iterated_expectation d (fun ys => \tr (S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys))) =
    \tr (S n xs *m S n xs) + d%:R * K.
  move=> xs Hxs.
  transitivity (gaussian_iterated_expectation d (fun ys =>
    \tr ((S n xs + pmdm_M d ys) *m (S n xs + pmdm_M d ys)))).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmdm_S_app.
  exact: pmdm_step2.
rewrite pmdm_dim (pmdm_split_eq _ _ _ _ Hstep).
rewrite pmdm_E_add; [by pmdm_regt | exact: pmdm_reg_const |].
by rewrite pmdm_E_const IH mulrSr; ring.
Qed.

Lemma pmdm_S_trace4 n :
  gaussian_iterated_expectation (n * d)
    (fun xs => \tr (S n xs *m S n xs *m S n xs *m S n xs)) <=
  n%:R * pmdm_m4 d + 3 * n%:R * (n%:R - 1) * d%:R * K ^+ 2.
Proof.
elim: n => [|n IH].
  rewrite mul0n /= pmdm_S0 !mul0mx mxtrace0; lra.
have HF : pmdf_regular (Nat.add (n * d)%N d)
    (fun xs => \tr (S n.+1 xs *m S n.+1 xs *m S n.+1 xs *m S n.+1 xs)).
  by rewrite -pmdm_dim; pmdm_regt.
pose G xs := \tr (S n xs *m S n xs *m S n xs *m S n xs) +
  6 * K * \tr (S n xs *m S n xs) + 4 * \tr (pmdm_C3 d *m S n xs) + pmdm_m4 d.
have RG : pmdf_regular (n * d) G by rewrite /G; pmdm_regt.
have Hstep : forall xs, length xs = (n * d)%N ->
    gaussian_iterated_expectation d (fun ys =>
      \tr (S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys)))
    <= G xs.
  move=> xs Hxs.
  have -> : gaussian_iterated_expectation d (fun ys =>
      \tr (S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys) *m S n.+1 (xs ++ ys))) =
    gaussian_iterated_expectation d (fun ys =>
    \tr ((S n xs + pmdm_M d ys) *m (S n xs + pmdm_M d ys) *m
         (S n xs + pmdm_M d ys) *m (S n xs + pmdm_M d ys))).
    by apply: gaussian_iterated_expectation_ext => ys _; rewrite pmdm_S_app.
  rewrite /G (mxtrace_mulC (pmdm_C3 d) (S n xs)).
  exact: pmdm_step4 (pmdm_S_sym d n xs).
rewrite pmdm_dim.
apply: (le_trans (pmdm_split_le _ _ _ G HF RG Hstep)).
rewrite /G pmdm_E_add; [by pmdm_regt | exact: pmdm_reg_const |].
rewrite pmdm_E_add; [by pmdm_regt | by pmdm_regt |].
rewrite pmdm_E_add; [by pmdm_regt | by pmdm_regt |].
rewrite pmdm_E_scale; [by pmdm_regt |].
rewrite pmdm_E_scale; [by pmdm_regt |].
rewrite pmdm_E_tr_mul; [by pmdm_regt |].
rewrite pmdm_S_mean mulmx0 mxtrace0 pmdm_E_const pmdm_S_trace2.
rewrite mulrSr; lra.
Qed.

(* The main moment bound: E tr Z^4 for Z = S_N. *)
Theorem paper_main_diag_trace_moment N :
  gaussian_iterated_expectation (N * d)
    (fun xs => \tr (S N xs *m S N xs *m S N xs *m S N xs)) <=
  N%:R * (2 ^+ 21 * d%:R ^+ 4 + 16 * d%:R) +
  3 * N%:R * (N%:R - 1) * d%:R * (4 * d%:R + 52) ^+ 2.
Proof.
apply: (le_trans (pmdm_S_trace4 N)); rewrite /pmdm_K lerD2r.
by apply: ler_wpM2l; [exact: ler0n | exact: pmdm_m4_bound].
Qed.

Lemma paper_main_diag_trace4_regular N :
  pmdf_regular (N * d) (fun xs => \tr (S N xs *m S N xs *m S N xs *m S N xs)).
Proof. by pmdm_regt. Qed.

Lemma paper_main_diag_trace4_ge0 N xs :
  0 <= \tr (S N xs *m S N xs *m S N xs *m S N xs).
Proof.
have E : (S N xs *m S N xs)^T = S N xs *m S N xs by rewrite trmx_mul pmdm_S_sym.
by rewrite -mulmxA -[X in _ *m X]E; exact: pmdb_trace_gram_ge0.
Qed.

(* The centered Gram of the diagonal block of an actual sample. *)
Lemma paper_main_diag_block_centered N (x : paper_main_sample N d) :
  (paper_main_diag_block N d x)^T *m paper_main_diag_block N d x - (2 * N%:R) *: 1%:M =
  S N (tval x).
Proof.
rewrite paper_main_centered_gram_rows /pmdm_S; apply: eq_bigr => i _.
have E : (row i (paper_main_diag_block N d x))^T = pmdm_urow d i (tval x).
  by apply/matrixP => a b; rewrite !mxE /pmdm_v.
by rewrite -E trmxK.
Qed.

End Induction.
