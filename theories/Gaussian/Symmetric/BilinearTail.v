(* Applying the actual Gaussian linear-form tail to bilinear forms of the
   isotropic symmetric Gaussian. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions
  Gordon.ProcessCovariance Gaussian.Symmetric.Coordinates
  Gaussian.Symmetric.PublicLaw Spectral.SymmetricBilinear Gaussian.Tail.Linear.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_public_symmetric_bilinear_linear n (u v : 'cV[R]_(S n)) xs :
  ((u^T *m paper_main_public_symmetric_gaussian n xs *m v)%R) ord0 ord0 =
  paper_main_gaussian_linear_form (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n u v) xs.
Proof.
have H := paper_main_symmetric_bilinear_unit_row n u v xs.
rewrite paper_main_public_symmetric_feature_conversion scalerA in H.
have Hs := lt0r_neq0 (pmsb_goe_scale_gt0 n).
by rewrite (mulVf Hs) scale1r in H.
Qed.

Definition paper_main_public_symmetric_bilinear_union {I : Type} n
    (u v : I -> 'cV[R]_(S n)) (ids : list I) b :=
  paper_main_gaussian_linear_union (paper_main_symmetric_dimension n)
    (fun i => paper_main_symmetric_bilinear_coefficients n (u i) (v i)) ids b.

Lemma paper_main_public_symmetric_bilinear_unionE I n
    (u v : I -> 'cV[R]_(S n)) ids b x :
  paper_main_public_symmetric_bilinear_union n u v ids b x <->
  exists i, List.In i ids /\
    b <= Rabs ((((u i)^T *m paper_main_public_symmetric_gaussian n (tval x) *m (v i))%R) ord0 ord0).
Proof.
rewrite /paper_main_public_symmetric_bilinear_union paper_main_gaussian_linear_unionE.
split.
- move=> [i [Hi Hb]]; exists i; split; first exact Hi.
  by rewrite paper_main_public_symmetric_bilinear_linear.
- move=> [i [Hi Hb]]; exists i; split; first exact Hi.
  by rewrite paper_main_public_symmetric_bilinear_linear in Hb.
Qed.

Theorem paper_main_public_symmetric_bilinear_union_bound I n
    (u v : I -> 'cV[R]_(S n)) ids b :
  (forall i, List.In i ids -> ((u i)^T *m u i)%R ord0 ord0 = 1 /\
    ((v i)^T *m v i)%R ord0 ord0 = 1) -> 0 < b ->
  measurable (paper_main_public_symmetric_bilinear_union n u v ids b) /\
  (gaussian_product_law (paper_main_symmetric_dimension n)
    (paper_main_public_symmetric_bilinear_union n u v ids b) <=
    ((INR (List.length ids)*(2*exp(-b^2/2)))%Rcoq)%:E)%E.
Proof.
move=> Hunit Hb.
have HC : forall i, List.In i ids ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n (u i) (v i))
    (paper_main_symmetric_bilinear_coefficients n (u i) (v i)) <= 1.
  move=> i Hi; have [Hu Hv] := Hunit i Hi; apply/RleP.
  exact: paper_main_symmetric_bilinear_coefficients_unit.
split.
- exact: paper_main_gaussian_linear_union_measurable.
- exact: paper_main_gaussian_linear_union_bound.
Qed.

Definition paper_main_public_symmetric_net_event n (v : nat -> nat -> R) s b :=
  paper_main_public_symmetric_bilinear_union n
    (fun ij : nat*nat => paper_main_symmetric_column n (v (fst ij)))
    (fun ij : nat*nat => paper_main_symmetric_column n (v (snd ij)))
    (List.list_prod (List.seq 0 s) (List.seq 0 s)) b.

Lemma paper_main_public_symmetric_net_eventE n v s b x :
  paper_main_public_symmetric_net_event n v s b x <->
  exists i j, Nat.lt i s /\ Nat.lt j s /\
    b <= Rabs (((((paper_main_symmetric_column n (v i))^T) *m
      paper_main_public_symmetric_gaussian n (tval x) *m
      paper_main_symmetric_column n (v j))%R) ord0 ord0).
Proof.
rewrite /paper_main_public_symmetric_net_event paper_main_public_symmetric_bilinear_unionE.
split.
- move=> [[i j] [Hij Hb]]; simpl in Hb.
  apply List.in_prod_iff in Hij; destruct Hij as [Hi Hj].
  apply List.in_seq in Hi; apply List.in_seq in Hj.
  exists i,j; repeat split; try lia; exact Hb.
- move=> [i [j [Hi [Hj Hb]]]]; exists (i,j); split; last exact Hb.
  apply List.in_prod; apply List.in_seq; lia.
Qed.

Theorem paper_main_public_symmetric_net_tail n v s b :
  (forall i, Nat.lt i s -> paper_main_gordon_dot (S n) (v i) (v i) = 1) ->
  0 < b ->
  measurable (paper_main_public_symmetric_net_event n v s b) /\
  (gaussian_product_law (paper_main_symmetric_dimension n)
    (paper_main_public_symmetric_net_event n v s b) <=
    ((INR s * INR s * (2*exp(-b^2/2)))%Rcoq)%:E)%E.
Proof.
move=> HV Hb.
have HU : forall ij, List.In ij (List.list_prod (List.seq 0 s) (List.seq 0 s)) ->
  (((paper_main_symmetric_column n (v (fst ij)))^T *m
    paper_main_symmetric_column n (v (fst ij)))%R) ord0 ord0 = 1 /\
  (((paper_main_symmetric_column n (v (snd ij)))^T *m
    paper_main_symmetric_column n (v (snd ij)))%R) ord0 ord0 = 1.
  move=> [i j] Hij; apply List.in_prod_iff in Hij; destruct Hij as [Hi Hj].
  apply List.in_seq in Hi; apply List.in_seq in Hj; simpl.
  rewrite !paper_main_symmetric_column_norm; split; apply HV; lia.
have [HM HP] := paper_main_public_symmetric_bilinear_union_bound (nat*nat)%type n
  (fun ij => paper_main_symmetric_column n (v (fst ij)))
  (fun ij => paper_main_symmetric_column n (v (snd ij))) _ b HU Hb.
split; first exact HM.
rewrite List.length_prod !List.length_seq mult_INR in HP; exact HP.
Qed.

Lemma paper_main_symmetric_net_exponential_rate d s :
  0 < d -> 0 < s -> ln s <= 20*ln 2*d ->
  s*s*(2*exp(-(10*sqrt d)^2/2)) <= 2*exp(-10*d).
Proof.
intros Hd Hs Hln.
pose proof (exp_ineq1_le (ln 2)) as Hlog.
rewrite (exp_ln 2 ltac:(lra)) in Hlog.
assert (HE : s*s*(2*exp(-(10*sqrt d)^2/2)) =
  2*exp(2*ln s-(10*sqrt d)^2/2)).
{ replace (2*ln s-(10*sqrt d)^2/2) with (ln s+ln s+(-(10*sqrt d)^2/2)) by lra.
  rewrite !exp_plus (exp_ln s Hs); ring. }
rewrite HE.
apply Rmult_le_compat_l; [lra|].
apply Soft.Extrema.exp_monotone.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd)); nra.
Qed.

Theorem paper_main_public_symmetric_net_tail_exponential n v s :
  Nat.lt 0 s ->
  (forall i, Nat.lt i s -> paper_main_gordon_dot (S n) (v i) (v i) = 1) ->
  ln (INR s) <= 20*ln 2*INR (S n) ->
  measurable (paper_main_public_symmetric_net_event n v s (10*sqrt (INR (S n)))) /\
  (gaussian_product_law (paper_main_symmetric_dimension n)
    (paper_main_public_symmetric_net_event n v s (10*sqrt (INR (S n)))) <=
    (2*exp(-10*INR (S n)))%:E)%E.
Proof.
move=> Hs HV Hln.
have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
have Hb : 0 < 10*sqrt (INR (S n)) by have := sqrt_lt_R0 _ Hd; lra.
have [HM HP] := paper_main_public_symmetric_net_tail n v s _ HV Hb.
split; first exact HM.
eapply le_trans; first exact HP.
rewrite lee_fin; apply/RleP.
exact: (paper_main_symmetric_net_exponential_rate _ _ Hd (lt_0_INR s Hs) Hln).
Qed.
