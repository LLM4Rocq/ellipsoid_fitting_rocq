(* Sign symmetry of the standard Gaussian. On a symmetric segment, the
   reflection substitution of MathComp (integration_by_substitution_oppr)
   and the evenness of the kernel give the reflected cutoff integral; the
   checked cutoff limits then give E g(-z) = E g(z) for continuous g whose
   Gaussian integrals exist. The iterated form E_d[F(-xs)] = E_d[F(xs)]
   for continuous, polynomially bounded F follows by induction through the
   last marginal. No symmetry of the law is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import realfun derive ftc.
From EllipsoidFitting Require Import AnalysisBridge2 AnalysisIntegralDefinitions GaussianDefinitions
  GaussianKernel GaussianMass GaussianCutoffDefinitions GaussianCutoff ImproperCutoff
  GaussianFubiniLebesgue GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianLastDefinitions GaussianLastIntegration GaussianCoordinateMarginals
  GaussianPermutationContinuity.
Import ListNotations GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gaussian_segment_reflect (g : R -> R) (A : R) :
  0 <= A -> continuous g ->
  Rintegral lebesgue_measure `[- A, A] (fun x => g (- x) * gaussian_kernel x) =
  Rintegral lebesgue_measure `[- A, A] (fun x => g x * gaussian_kernel x).
Proof.
move=> HA Hg.
have HGc : continuous (fun x => g x * gaussian_kernel x).
  move=> x; apply: continuousM; [exact: Hg|exact: gaussian_kernel_continuous].
have Hab : (- A <= A)%R by apply/RleP; change (- A <= A); lra.
have H := @integration_by_substitution_oppr R (fun x => g x * gaussian_kernel x)
  (- A) A Hab (continuous_subspaceT HGc).
rewrite opprK in H.
rewrite /Rintegral H.
congr fine; apply: eq_integral => x _ /=.
by rewrite gaussian_kernel_even.
Qed.

Lemma paper_main_gaussian_cutoff_reflect (g : R -> R) (A : R) :
  0 <= A -> continuous g ->
  gaussian_cutoff_integral (fun x => g (- x)) A = gaussian_cutoff_integral g A.
Proof.
move=> HA Hg; rewrite /gaussian_cutoff_integral.
rewrite (fubini_oriented_symmetric _ _ HA) (fubini_oriented_symmetric _ _ HA).
exact: paper_main_gaussian_segment_reflect.
Qed.

Lemma paper_main_gaussian_integral_reflect (g : R -> R) :
  continuous g -> gaussian_integral_exists g ->
  gaussian_integral_exists (fun x => g (- x)) ->
  gaussian_integral (fun x => g (- x)) = gaussian_integral g.
Proof.
move=> Hg Hi Hi'.
have L1 := gaussian_cutoff_integral_limit _ Hi'.
have L2 := gaussian_cutoff_integral_limit _ Hi.
have L3 : (gaussian_cutoff_integral g A @[A --> +oo%R] -->
    gaussian_integral (fun x => g (- x)))%classic.
  apply: (cvg_trans _ L1); apply: near_eq_cvg.
  exists 0%R; split; [exact: num_real|] => A /RltP HA /=.
  by rewrite (paper_main_gaussian_cutoff_reflect g A (Rlt_le _ _ HA) Hg).
exact: (@cvg_unique _ (@Rhausdorff _) _ _ _ _ L3 L2).
Qed.

Theorem paper_main_gaussian_expectation_reflect (g : R -> R) :
  continuous g -> gaussian_integral_exists g ->
  gaussian_integral_exists (fun x => g (- x)) ->
  gaussian_expectation (fun x => g (- x)) = gaussian_expectation g.
Proof.
move=> Hg Hi Hi'; rewrite /gaussian_expectation.
by rewrite (paper_main_gaussian_integral_reflect g Hg Hi Hi').
Qed.

(* Negation of a coordinate list. *)

Lemma paper_main_gaussian_neg_length (xs : list R) :
  List.length (List.map Ropp xs) = List.length xs.
Proof. exact: List.length_map. Qed.

Lemma paper_main_gaussian_neg_weight p (xs : list R) :
  gaussian_coordinate_product_weight p (List.map Ropp xs) =
    gaussian_coordinate_product_weight p xs.
Proof.
elim: xs => [|x xs IH] //=.
by rewrite IH /gaussian_coordinate_weight Rabs_Ropp.
Qed.

Lemma paper_main_gaussian_neg_polynomial_bound d C p F :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => F (List.map Ropp xs)).
Proof.
move=> [HC HF]; split; first exact: HC.
move=> xs Hxs.
rewrite -(paper_main_gaussian_neg_weight p xs).
apply: HF; by rewrite paper_main_gaussian_neg_length.
Qed.

Lemma paper_main_gaussian_neg_forall2 (e : R) xs ys :
  List.Forall2 (fun x y => Rabs (x - y) < e) xs ys ->
  List.Forall2 (fun x y => Rabs (x - y) < e) (List.map Ropp xs) (List.map Ropp ys).
Proof.
elim=> [|x y xs' ys' Hxy _ IH] /=; constructor => //.
by rewrite -Rabs_Ropp; replace (- (- x - - y)) with (x - y) by ring.
Qed.

Lemma paper_main_gaussian_neg_continuous d F :
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => F (List.map Ropp xs)).
Proof.
move=> HF.
apply: (finite_joint_continuous_list_map d d (List.map Ropp) F) => //.
- by move=> xs Hxs; rewrite paper_main_gaussian_neg_length.
- by move=> e xs ys _ _ H; exact: paper_main_gaussian_neg_forall2.
Qed.

(* The iterated sign symmetry. *)
Theorem paper_main_gaussian_iterated_reflect d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_expectation d (fun xs => F (List.map Ropp xs)) =
    gaussian_iterated_expectation d F.
Proof.
elim: d F C p => [|d IH] F C p HF HB; first by [].
rewrite (gaussian_iterated_last_expectation d (fun xs => F (List.map Ropp xs))).
rewrite (gaussian_iterated_last_expectation d F).
transitivity (gaussian_iterated_expectation d
  (fun xs => gaussian_last_marginal F (List.map Ropp xs))).
- apply: gaussian_iterated_expectation_ext => xs Hxs.
  rewrite /gaussian_last_marginal.
  have Hlen : List.length (List.map Ropp xs) = d by rewrite paper_main_gaussian_neg_length.
  have Hcont : continuous (fun u => F (List.map Ropp xs ++ [u])%list).
    by move=> t; exact: (finite_joint_continuous_last_section d F _ HF Hlen t).
  have [Hi _] := gaussian_last_section_admissible d F C p _ HF HB Hlen.
  have [Hi' _] := gaussian_last_section_admissible d (fun ys => F (List.map Ropp ys)) C p xs
    (paper_main_gaussian_neg_continuous (S d) F HF)
    (paper_main_gaussian_neg_polynomial_bound (S d) C p F HB) Hxs.
  have Heq : (fun t => F (List.map Ropp (xs ++ [t])%list)) =
      (fun t => (fun u => F (List.map Ropp xs ++ [u])%list) (- t)).
    by apply: funext => t; rewrite List.map_app.
  rewrite Heq; rewrite Heq in Hi'.
  exact: (paper_main_gaussian_expectation_reflect _ Hcont Hi Hi').
- exact: (IH (gaussian_last_marginal F) (C * gaussian_coordinate_weight_moment p) p
    (gaussian_last_marginal_continuous d F C p HF HB)
    (gaussian_last_marginal_polynomial_bound d F C p HF HB)).
Qed.
