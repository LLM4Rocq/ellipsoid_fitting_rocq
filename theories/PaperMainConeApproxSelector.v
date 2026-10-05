(* Approximate maximizers on the bounded-condition cone sphere from finite
   nets. Let K = paper_main_head_cone_sphere kappa in 'M[R]_(S n), 1 <= kappa.
   - Net family (paper_main_cone_net_family). For eps > 0 there are a finite
     family B t, t < s, s > 0, of members of K such that every P in K has
     some t with |P - B t|_F <= eps. The net comes from the checked
     paper_main_gordon_finite_net_exists applied to the coordinate image of K
     (PaperMainConeGaussianCoordinates, whose dot product is the Frobenius
     pairing); each net point is turned back into a member of K by a fixed
     classical choice (xget). This is a choice of finitely many fixed
     matrices, not a measurable choice.
   - Selector (paper_main_cone_selector B s Z): the first maximizer of
     <Z, B t> over t < s (PaperMainFiniteSupportSelector). It lies in K, so it
     is symmetric, has Frobenius norm 1 and satisfies the public bilinear
     bound paper_main_cone_opnorm_le with kappa / sqrt d, and
       support(Z, K) - eps |Z|_F <= <Z, P(Z)> <= support(Z, K),
     where support(Z, K) = paper_main_head_support Z K.
   - Gaussian version (paper_main_cone_selector_gaussian). For the actual
     public symmetric Gaussian matrix Z(xs) of PaperMainGaussianSymmetricLawPublic,
     the entries of x |-> P(Z(tval x)) are measurable, since the entries of Z
     are 1-Lipschitz in the coordinates. No measurable maximum or selector
     premise is used. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianCoordinateDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadSpectral PaperMainGeometryHeadWidth
  PaperMainConeConditionOperator PaperMainMatrixOperatorTransport
  PaperMainGordonProcessCovariance PaperMainGordonLipschitz PaperMainGordonNets
  PaperMainGordonNetExistence PaperMainGaussianLipschitzClip
  PaperMainGaussianFeatureCoordinates PaperMainGaussianSymmetricLawPublic
  PaperMainConeGaussianCoordinates PaperMainConeGaussianCoordinatesSpheres
  PaperMainSymmetricDiagonalization PaperMainFiniteSupportSelector.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* Facts on the cone sphere. *)

Lemma paper_main_cone_selector_opnorm n (kappa : R) (P : 'M[R]_(S n)) :
  1 <= kappa -> paper_main_head_cone_sphere kappa P ->
  paper_main_cone_opnorm_le P (kappa / Num.sqrt (S n)%:R).
Proof.
move=> Hk [Hcond HF].
have [_ Hup] := paper_main_head_condition_box (S n) P kappa (ltn0Sn n) Hcond HF.
have Hs : 0 < Num.sqrt ((S n)%:R : R) by rewrite sqrtr_gt0 ltr0n.
have Hk0 : 0 < kappa by apply: lt_le_trans Hk; exact: ltr01.
have Hb : 0 <= kappa / Num.sqrt (S n)%:R by rewrite divr_ge0 // ltW.
have [lam [Hlam [Hlow _]]] := Hcond.
have Hpsd := pmh_loewner_psd _ P lam (ltW Hlam) Hlow.
exact: (paper_main_cone_opnorm_of_loewner _ P _ (proj1 Hpsd) Hb
  (pmmo_psd_lower n P _ Hpsd Hb) Hup).
Qed.

Lemma paper_main_cone_selector_entry_bound d (A : 'M[R]_d) (i j : 'I_d) :
  `|A i j| <= paper_main_frobenius A.
Proof.
rewrite -sqrtr_sqr /paper_main_frobenius; apply: ler_wsqrtr.
rewrite /paper_main_pairing (bigD1 i) //= (bigD1 j) //= expr2 -addrA lerDl.
apply: addr_ge0.
  by apply: sumr_ge0 => k _; rewrite -expr2 sqr_ge0.
by apply: sumr_ge0 => k _; apply: sumr_ge0 => l _; rewrite -expr2 sqr_ge0.
Qed.

(* A finite Frobenius net of the cone sphere made of members of it. *)

Theorem paper_main_cone_net_family n (kappa eps : R) :
  1 <= kappa -> 0 < eps ->
  exists (B : nat -> 'M[R]_(S n)) (s : nat), (0 < s)%N /\
    (forall t, (t < s)%N -> paper_main_head_cone_sphere kappa (B t)) /\
    (forall P, paper_main_head_cone_sphere kappa P ->
      exists t, (t < s)%N /\ paper_main_frobenius (P - B t) <= eps).
Proof.
move=> Hk He.
set K := paper_main_head_cone_sphere kappa : set 'M[R]_(S n).
set D := paper_main_symmetric_dimension n.
have [P0 HP0] := paper_main_cone_condition_sphere_nonempty n kappa (elimT RleP Hk).
have Hsym : forall S, K S -> paper_main_symmetric S.
  exact: paper_main_cone_condition_sphere_symmetric.
have Hunit : forall S, K S -> paper_main_frobenius S = 1.
  exact: paper_main_cone_condition_sphere_unit.
have HTne := paper_main_cone_code_set_nonempty n K (ex_intro _ P0 HP0).
have HTunit := paper_main_cone_code_set_unit n K Hsym Hunit.
have [s [v [Hs [Hin Hcov]]]] :=
  paper_main_gordon_finite_net_exists D (paper_main_cone_code_set n K) eps
    (elimT RltP He) HTne HTunit.
pose good t := [set S : 'M[R]_(S n) | K S /\
  forall k, (k < D)%coq_nat -> v t k = paper_main_cone_code n S k].
pose B t := xget P0 (good t).
have HB : forall t, (t < s)%N -> good t (B t).
  move=> t Ht; apply: xgetPex.
  have [S [HS Hagree]] := Hin t (proj2 (List.in_seq _ _ _) (conj (Nat.le_0_l t)
    (elimT ssrnat.ltP Ht))).
  by exists S; split.
exists B, s; split; first exact/ssrnat.ltP.
split; first by move=> t Ht; have [] := HB t Ht.
move=> P HP.
have HTP : paper_main_cone_code_set n K (paper_main_cone_code n P) by exists P; split.
have [t [Ht Hdist]] := Hcov _ HTP.
have Ht' : (t < s)%N by have := proj1 (List.in_seq _ _ _) Ht => -[_ ?]; exact/ssrnat.ltP.
exists t; split; first exact: Ht'.
have [HBt Hagree] := HB t Ht'.
have HPB : paper_main_symmetric (P - B t) by apply: pmh_symmetricB; [exact: Hsym | exact: Hsym].
have Hsq : paper_main_pairing (P - B t) (P - B t) <= eps ^+ 2.
  rewrite -(paper_main_cone_code_dot n _ _ HPB HPB).
  apply/RleP; rewrite -RpowE.
  apply: Rle_trans Hdist; right.
  rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk'.
  have HkD : (k < D)%coq_nat by have := proj1 (List.in_seq _ _ _) Hk'; lia.
  rewrite (paper_main_cone_code_basis n _ k HPB) pmh_pairingBr.
  rewrite -(paper_main_cone_code_basis n _ k (Hsym P HP)).
  rewrite -(paper_main_cone_code_basis n _ k (Hsym _ HBt)) -(Hagree k HkD).
  by [].
have He0 : 0 <= eps by exact: ltW.
rewrite -(ger0_norm He0) -sqrtr_sqr /paper_main_frobenius.
exact: ler_wsqrtr.
Qed.

(* The selector and its support approximation. *)

Definition paper_main_cone_selector {d : nat} (B : nat -> 'M[R]_d) (s : nat)
    (Z : 'M[R]_d) : 'M[R]_d :=
  paper_main_finite_argmax B Z 0 (iota 1 s.-1).

Theorem paper_main_cone_selector_spec n (kappa eps : R) (B : nat -> 'M[R]_(S n)) s
    (Z : 'M[R]_(S n)) :
  1 <= kappa -> (0 < s)%N ->
  (forall t, (t < s)%N -> paper_main_head_cone_sphere kappa (B t)) ->
  (forall P, paper_main_head_cone_sphere kappa P ->
    exists t, (t < s)%N /\ paper_main_frobenius (P - B t) <= eps) ->
  [/\ paper_main_head_cone_sphere kappa (paper_main_cone_selector B s Z),
    paper_main_symmetric (paper_main_cone_selector B s Z),
    paper_main_frobenius (paper_main_cone_selector B s Z) = 1,
    paper_main_cone_opnorm_le (paper_main_cone_selector B s Z) (kappa / Num.sqrt (S n)%:R) &
    paper_main_head_support Z (paper_main_head_cone_sphere kappa) -
      eps * paper_main_frobenius Z <= paper_main_pairing Z (paper_main_cone_selector B s Z) /\
    paper_main_pairing Z (paper_main_cone_selector B s Z) <=
      paper_main_head_support Z (paper_main_head_cone_sphere kappa)].
Proof.
move=> Hk Hs HB Hcov.
set K := paper_main_head_cone_sphere kappa : set 'M[R]_(S n).
set P := paper_main_cone_selector B s Z.
have Hlist : forall t, (t \in 0%N :: iota 1 s.-1) = (t < s)%N.
  by move=> t; rewrite -[s in RHS](prednK Hs) in_cons mem_iota /= add1n ltnS;
    case: t.
have HK : K P.
  rewrite /P /paper_main_cone_selector /paper_main_finite_argmax.
  apply: HB; rewrite -Hlist; exact: paper_main_finite_argmax_index_mem.
have Hunit : forall S, K S -> paper_main_frobenius S = 1.
  exact: paper_main_cone_condition_sphere_unit.
split.
- exact: HK.
- exact: (paper_main_cone_condition_sphere_symmetric _ _ _ HK).
- exact: Hunit.
- exact: paper_main_cone_selector_opnorm.
split; last exact: (pmh_support_ge _ Z K P Hunit HK).
rewrite lerBlDr.
apply: ge_sup.
  by exists (paper_main_pairing Z P), P.
move=> _ [Q HQ <-].
have [t [Ht HQt]] := Hcov Q HQ.
have Hmax : paper_main_pairing Z (B t) <= paper_main_pairing Z P.
  by apply: paper_main_finite_argmax_max; rewrite Hlist.
have Hdiff : paper_main_pairing Z Q - paper_main_pairing Z (B t) <=
    paper_main_frobenius Z * paper_main_frobenius (Q - B t).
  rewrite -pmh_pairingBr; apply: le_trans (ler_norm _) _.
  exact: pmh_pairing_frobenius_bound.
have HZ0 := pmh_frobenius_ge0 _ Z.
have Heps : paper_main_frobenius Z * paper_main_frobenius (Q - B t) <=
    eps * paper_main_frobenius Z.
  by rewrite mulrC; apply: ler_wpM2r.
have := le_trans Hdiff Heps; rewrite lerBlDr => H.
apply: le_trans H _; rewrite addrC lerD2r; exact: Hmax.
Qed.

(* The actual Gaussian matrix. *)

Lemma paper_main_cone_selector_gaussian_entry_measurable n (a b : 'I_(S n)) :
  measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
    ((fun x => paper_main_public_symmetric_gaussian n (tval x) a b) : _ -> T).
Proof.
apply: (gpp_joint_measurable _ (fun xs => paper_main_public_symmetric_gaussian n xs a b)).
apply: (paper_main_gaussian_lipschitz_continuous _ _ 1); first exact: Rle_0_1.
move=> xs ys _ _.
rewrite Rmult_1_l -paper_main_public_symmetric_gaussian_isometry.
have := paper_main_cone_selector_entry_bound _
  (paper_main_public_symmetric_gaussian n xs - paper_main_public_symmetric_gaussian n ys) a b.
by rewrite paper_main_symmetric_entryB -RabsE => /RleP.
Qed.

Theorem paper_main_cone_selector_gaussian n (kappa eps : R) :
  1 <= kappa -> 0 < eps ->
  exists P : (paper_main_symmetric_dimension n).-tuple T -> 'M[R]_(S n),
    (forall a b : 'I_(S n), measurable_fun [set: _] ((fun x => P x a b) : _ -> T)) /\
    forall x : (paper_main_symmetric_dimension n).-tuple T,
      [/\ paper_main_head_cone_sphere kappa (P x),
        paper_main_symmetric (P x),
        paper_main_frobenius (P x) = 1,
        paper_main_cone_opnorm_le (P x) (kappa / Num.sqrt (S n)%:R) &
        paper_main_head_support (paper_main_public_symmetric_gaussian n (tval x))
            (paper_main_head_cone_sphere kappa) -
          eps * paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x)) <=
          paper_main_pairing (paper_main_public_symmetric_gaussian n (tval x)) (P x) /\
        paper_main_pairing (paper_main_public_symmetric_gaussian n (tval x)) (P x) <=
          paper_main_head_support (paper_main_public_symmetric_gaussian n (tval x))
            (paper_main_head_cone_sphere kappa)].
Proof.
move=> Hk He.
have [B [s [Hs [HB Hcov]]]] := paper_main_cone_net_family n kappa eps Hk He.
exists (fun x => paper_main_cone_selector B s (paper_main_public_symmetric_gaussian n (tval x))).
split.
  move=> a b.
  exact: (paper_main_finite_argmax_measurable B
    (fun x : (paper_main_symmetric_dimension n).-tuple T =>
      paper_main_public_symmetric_gaussian n (tval x)) 0 (iota 1 s.-1)
    (paper_main_cone_selector_gaussian_entry_measurable n) a b).
by move=> x; exact: (paper_main_cone_selector_spec n kappa eps B s _ Hk Hs HB Hcov).
Qed.
