(* A finite contained section net and the actual Gaussian width of the head
   section (PaperMainHeadSectionWidthLaw). Let D = paper_main_symmetric_dimension n,
   z a D-tuple of Gaussian coordinates under gaussian_product_law D, Zp(z) the
   public symmetric Gaussian matrix with these exact coordinates, and h a head
   sample with features W k = paper_main_head_feature h k.
   - For a nonempty section, the A18 width
       paper_main_head_section_width n m kappa h = E[support (Zp z) section]
     equals the Gordon set width of the code set of the section
     (paper_main_cone_code_set), by the Gaussian law transport of the
     continuous support function with the norm bound.
   - For finitely many symmetric unit matrices B t (t < s, s > 0), the
     integral of max_t <Zp z, B t> equals the Gordon width of their codes.
   - If B is a Frobenius eps-net of the section contained in it
     (paper_main_head_section_net), then the width is a real number w with
       gordon_width(codes of B) <= w <= gordon_width(codes of B) + eps sqrt D,
     equivalently E[max_t <Zp z, B t>] <= width <= E[max_t <Zp z, B t>] + eps sqrt D.
   The section lower bounds themselves are not re-proved here. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianProbabilityProductDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth
  PaperMainGaussianNorm PaperMainGaussianSmoothLaw PaperMainGaussianFeatureCoordinates
  PaperMainGaussianSymmetricLawPublic
  PaperMainGordonProcessCovariance PaperMainGordonProcesses PaperMainGordonSetWidth
  PaperMainGordonWidth PaperMainGordonNets PaperMainGordonEntropy
  PaperMainConeGaussianCoordinates PaperMainConeGaussianCoordinatesSpheres
  PaperMainHeadSectionMeasurable PaperMainHeadSectionWidthLaw PaperMainHeadSectionMinimax
  PaperMainHeadSectionApprox PaperMainHeadSectionApproxNets.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* Polynomial bounds for the law transport. *)

Lemma paper_main_head_section_set_support_polynomial d (A : (nat -> R) -> Prop) :
  (exists u, A u) -> (forall u, A u -> paper_main_gordon_dot d u u = 1) ->
  finite_polynomial_bound d (1 + INR d) 2%nat (paper_main_gordon_set_support d A).
Proof.
intros HA HU.
destruct (paper_main_gaussian_norm_polynomial d) as [HC HB]; split; [exact HC|].
intros xs Hxs.
pose proof (paper_main_gordon_set_support_abs d A xs Hxs HA HU) as HS.
specialize (HB xs Hxs).
rewrite (Rabs_pos_eq _ (paper_main_gaussian_norm_nonnegative xs)) in HB.
lra.
Qed.

Lemma paper_main_head_section_support_polynomial d (v : nat -> nat -> R) (S : list nat) :
  S <> nil -> (forall t, In t S -> paper_main_gordon_dot d (v t) (v t) = 1) ->
  finite_polynomial_bound d (1 + INR d) 2%nat (paper_main_gordon_support d v S).
Proof.
intros HS Hv.
destruct (paper_main_gaussian_norm_polynomial d) as [HC HB]; split; [exact HC|].
intros xs Hxs.
pose proof (paper_main_gordon_support_abs_bound d v S xs HS Hxs Hv) as H.
specialize (HB xs Hxs).
rewrite (Rabs_pos_eq _ (paper_main_gaussian_norm_nonnegative xs)) in HB.
lra.
Qed.

Local Open Scope ring_scope.

(* The A18 width of a nonempty section is the Gordon set width of its code
   set. *)

Theorem paper_main_head_section_width_set_width n m (kappa : R)
    (h : paper_main_sample m (S n)) :
  1 <= kappa ->
  (exists P, paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P) ->
  paper_main_head_section_width n m kappa h =
  (paper_main_gordon_set_width (paper_main_symmetric_dimension n)
    (paper_main_cone_code_set n
      (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k))))%:E.
Proof.
move=> Hk HA.
have [HT HU] := paper_main_cone_section_code_set n m kappa _ HA.
have [_ HE] := paper_main_gaussian_law_transport (paper_main_symmetric_dimension n)
  (paper_main_gordon_set_support (paper_main_symmetric_dimension n)
    (paper_main_cone_code_set n
      (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k))))
  _ _ (paper_main_gordon_set_support_continuous _ _ HT HU)
  (paper_main_head_section_set_support_polynomial _ _ HT HU).
rewrite /paper_main_gordon_set_width -HE /paper_main_head_section_width.
apply: eq_integral => z _.
rewrite /paper_main_head_section_support_value.
by rewrite (paper_main_cone_section_support n m kappa _ (tval z) HA (size_tuple z)).
Qed.

(* The Gaussian width of a finite family of symmetric unit matrices, with the
   exact public coordinates. *)

Theorem paper_main_head_section_net_width_law n (B : nat -> 'M[R]_n.+1) (s : nat) :
  (0 < s)%N ->
  (forall t, (t < s)%N -> paper_main_symmetric (B t) /\ paper_main_frobenius (B t) = 1) ->
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun z => (finite_max (fun t => paper_main_pairing
      (paper_main_public_symmetric_gaussian n (tval z)) (B t)) (List.seq 0 s))%:E) /\
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_z
    (finite_max (fun t => paper_main_pairing
      (paper_main_public_symmetric_gaussian n (tval z)) (B t)) (List.seq 0 s))%:E =
  (paper_main_gordon_width (paper_main_symmetric_dimension n)
    (fun t => paper_main_cone_code n (B t)) (List.seq 0 s))%:E)%E.
Proof.
move=> Hs HB.
have Hne := paper_main_head_section_seq_ne s Hs.
have HV : forall t, List.In t (List.seq 0 s) ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n)
      (paper_main_cone_code n (B t)) (paper_main_cone_code n (B t)) = 1.
  move=> t Ht; have [Hsym H1] := HB t (proj1 (paper_main_head_section_seq_lt t s) Ht).
  exact: paper_main_cone_code_unit.
have [HI HE] := paper_main_gaussian_law_transport (paper_main_symmetric_dimension n)
  (paper_main_gordon_support (paper_main_symmetric_dimension n)
    (fun t => paper_main_cone_code n (B t)) (List.seq 0 s)) _ _
  (paper_main_gordon_support_continuous _ _ _)
  (paper_main_head_section_support_polynomial _ _ _ Hne HV).
have Heq : (fun z : (paper_main_symmetric_dimension n).-tuple T =>
    (finite_max (fun t => paper_main_pairing
      (paper_main_public_symmetric_gaussian n (tval z)) (B t)) (List.seq 0 s))%:E) =
  (fun z => (paper_main_gordon_support (paper_main_symmetric_dimension n)
    (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) (tval z))%:E).
  apply: funext => z; congr (_%:E).
  rewrite /paper_main_gordon_support; apply: paper_main_gordon_finite_max_ext => t Ht.
  have [Hsym _] := HB t (proj1 (paper_main_head_section_seq_lt t s) Ht).
  by rewrite (paper_main_cone_code_gaussian n (B t) (tval z) Hsym).
rewrite Heq; split; [exact: HI | exact: HE].
Qed.

(* A contained Frobenius eps-net of the section: width error at most
   eps sqrt D. *)

Theorem paper_main_head_section_net_width n m (kappa : R) (h : paper_main_sample m (S n))
    (B : nat -> 'M[R]_n.+1) (s : nat) (eps : R) :
  1 <= kappa -> (0 < s)%N ->
  paper_main_head_section_net kappa (fun k : 'I_m => paper_main_head_feature h k) B s eps ->
  exists w : R, paper_main_head_section_width n m kappa h = w%:E /\
    paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) <= w /\
    w <= paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) +
      eps * sqrt (INR (paper_main_symmetric_dimension n)).
Proof.
move=> Hk Hs Hnet.
have HA : exists P,
    paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P.
  by exists (B 0%N); exact: (proj1 Hnet).
have [HT HU] := paper_main_cone_section_code_set n m kappa _ HA.
have He : 0 <= eps.
  have [t [_ Ht]] := (proj2 Hnet) (B 0%N) ((proj1 Hnet) 0%N Hs).
  exact: le_trans (pmh_frobenius_ge0 _ _) Ht.
have He' : Rle 0 eps by apply/RleP.
have [H1 H2] := paper_main_gordon_net_width_error (paper_main_symmetric_dimension n) _ _ _ eps
  He' HT HU (paper_main_head_section_net_code n m kappa _ B s eps Hnet).
exists (paper_main_gordon_set_width (paper_main_symmetric_dimension n)
  (paper_main_cone_code_set n
    (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k)))).
split; first exact: paper_main_head_section_width_set_width.
split.
- by rewrite -subr_ge0; apply/RleP.
- by rewrite -lerBlDl; apply/RleP.
Qed.

Corollary paper_main_head_section_net_width_integral n m (kappa : R)
    (h : paper_main_sample m (S n)) (B : nat -> 'M[R]_n.+1) (s : nat) (eps : R) :
  1 <= kappa -> (0 < s)%N ->
  paper_main_head_section_net kappa (fun k : 'I_m => paper_main_head_feature h k) B s eps ->
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_z
      (finite_max (fun t => paper_main_pairing
        (paper_main_public_symmetric_gaussian n (tval z)) (B t)) (List.seq 0 s))%:E <=
    paper_main_head_section_width n m kappa h)%E /\
  (paper_main_head_section_width n m kappa h <=
    \int[gaussian_product_law (paper_main_symmetric_dimension n)]_z
      (finite_max (fun t => paper_main_pairing
        (paper_main_public_symmetric_gaussian n (tval z)) (B t)) (List.seq 0 s))%:E +
    (eps * sqrt (INR (paper_main_symmetric_dimension n)))%:E)%E.
Proof.
move=> Hk Hs Hnet.
have HB : forall t, (t < s)%N ->
    paper_main_symmetric (B t) /\ paper_main_frobenius (B t) = 1.
  move=> t Ht; have HBt := (proj1 Hnet) t Ht; split.
  - exact: (paper_main_cone_section_symmetric n m kappa _ _ HBt).
  - exact: (paper_main_head_section_unit kappa _ _ HBt).
have [_ HE] := paper_main_head_section_net_width_law n B s Hs HB.
have [w [Hw [H1 H2]]] := paper_main_head_section_net_width n m kappa h B s eps Hk Hs Hnet.
by rewrite HE Hw -EFinD !lee_fin; split.
Qed.

(* The combined existence corollary for a head sample: actual nets from the
   fixed entropy grids, chosen before the linear map V, the width error, and
   the two-sided soft bridge for every V with an operator bound, with no net
   or cardinality premise. *)

Corollary paper_main_head_section_approx_width_exists n m (kappa : R) q
    (Y : (nat -> R) -> Prop) (h : paper_main_sample m (S n)) (eps : R) :
  1 <= kappa -> 0 < eps ->
  (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot q y y = 1) ->
  (exists P, paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature h k) P) ->
  let r := List.length (paper_main_gordon_entropy_grid q eps) in
  let s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n) eps) in
  (0 < r)%N /\ (0 < s)%N /\
  exists (z : nat -> nat -> R) (B : nat -> 'M[R]_n.+1),
    paper_main_gordon_finite_net q Y z (List.seq 0 r) eps /\
    paper_main_head_section_net kappa (fun k : 'I_m => paper_main_head_feature h k) B s eps /\
    ln (INR r) <= paper_main_gordon_entropy_constant eps * INR q /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps * INR (paper_main_symmetric_dimension n) /\
    (exists w : R, paper_main_head_section_width n m kappa h = w%:E /\
      paper_main_gordon_width (paper_main_symmetric_dimension n)
        (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) <= w /\
      w <= paper_main_gordon_width (paper_main_symmetric_dimension n)
        (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) +
        eps * sqrt (INR (paper_main_symmetric_dimension n))) /\
    forall (V : nat -> 'M[R]_n.+1) (L beta gamma : R),
      paper_main_head_section_operator_bound q V L -> 0 < beta -> 0 < gamma ->
      soft_minimax beta gamma
          (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
          (List.seq 0 r) (List.seq 0 s) -
        paper_main_gordon_entropy_constant eps * INR (paper_main_symmetric_dimension n) / gamma -
        L * eps <=
        paper_main_head_section_minimax kappa q Y (fun k : 'I_m => paper_main_head_feature h k) V /\
      paper_main_head_section_minimax kappa q Y (fun k : 'I_m => paper_main_head_feature h k) V <=
        soft_minimax beta gamma
          (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
          (List.seq 0 r) (List.seq 0 s) +
        paper_main_gordon_entropy_constant eps * INR q / beta + L * eps.
Proof.
move=> Hk He HY HU HA r s.
have [Hr [Hs [z [B [Hz [HB [Hlr [Hls Hsoft]]]]]]]] :=
  paper_main_head_section_approx_exists n m kappa q Y _ eps He HY HU HA.
split => //; split => //; exists z, B.
split => //; split => //; split => //; split => //.
split; first exact: (paper_main_head_section_net_width n m kappa h B s eps Hk Hs HB).
exact: Hsoft.
Qed.
