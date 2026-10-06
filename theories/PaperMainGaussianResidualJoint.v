(* Residual tails when the matrix is chosen from independent Gaussian
   coordinates. Let z be D Gaussian coordinates and x an N-point data sample
   of R^d, under the joint law gaussian_product_law (D + N d), split
   by paper_main_split_coordinates D (N d). Let P(z) : 'M[R]_d have
   measurable entries and let H be a measurable bad event for z. The joint
   residual event
     exists i < N, r <= |<W_i(x), P(z)>|,   W_i = paper_main_head_feature x i,
   is measurable: each <W_i(x), P(z)> is a finite sum of products of
   measurable functions of x and of z. If, outside H, P(z) is symmetric with
   paper_main_pairing (P z) (P z) = 1 and
   paper_main_cone_opnorm_le (P z) (kappa / sqrt d), then for d = S n and
   r > 0 the section of the joint event at every good z is the residual event
   of PaperMainGaussianResidualRows, and paper_main_head_exception_bound
   gives
     P[exists i < N, r <= |<W_i(x), P(z)>|]
       <= N 2 exp (- d r^2 / (4 + 4 kappa r)) + P_z(H).
   The bound is uniform in P, so no union over matrices is used, and no
   measurable choice of a maximizer is assumed. Without bad set the second
   term vanishes; for a constant P the joint event has the probability of the
   residual event of the data sample. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability exp.
From EllipsoidFitting Require Import SoftDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHeadFeature
  PaperMainConeConditionOperator PaperMainMeasurabilityCoordinates
  PaperMainSampling PaperMainHeadLaw PaperMainHeadLawBounds PaperMainGaussianUnion
  PaperMainGaussianResidual PaperMainGaussianResidualRows.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* Measurability on any measurable space. *)

Lemma paper_main_gaussian_residual_abs_ge_measurable {dX : measure_display}
    {X : measurableType dX} (f : X -> R) (r : R) :
  measurable_fun [set: X] (f : X -> T) -> measurable [set x | Rle r (Rabs (f x))].
Proof.
move=> mf.
have -> : [set x | Rle r (Rabs (f x))] = [set x | r <= `|f x|].
  by apply/seteqP; split=> x /=; rewrite RabsE => H; apply/RleP.
rewrite -(preimage_itvcy (fun x => `|f x|)).
have Mn := measurableT_comp (@normr_measurable _ _) mf.
by rewrite -[(fun x => _) @^-1` _]setTI; exact: Mn measurableT _ (measurable_itv _).
Qed.

(* The entries of the head features are measurable functions of the sample. *)

Lemma paper_main_gaussian_residual_feature_entry_measurable N d (i : nat) (a b : 'I_d) :
  measurable_fun [set: paper_main_sample N d]
    ((fun x => paper_main_head_feature x i a b) : paper_main_sample N d -> T).
Proof.
have -> : (fun x : paper_main_sample N d => paper_main_head_feature x i a b) =
    (fun x => (Num.sqrt d%:R)^-1 *
      (paper_main_point x i a 0 * paper_main_point x i b 0 - (a == b)%:R)).
  apply/funext => x; rewrite /paper_main_head_feature !mxE big_ord1 !mxE.
  by [].
apply: pm_measurable_scale; apply: pm_measurable_sub; last exact: pm_measurable_cst.
by apply: pm_measurable_mul; exact: pm_point_entry_measurable.
Qed.

(* The joint residual set and event. *)

Definition paper_main_gaussian_residual_joint_set D N d (P : D.-tuple T -> 'M[R]_d)
    (r : R) : set (D.-tuple T * paper_main_sample N d) :=
  [set zx | exists i, (i < N)%coq_nat /\
    Rle r (Rabs (paper_main_pairing (paper_main_head_feature zx.2 i) (P zx.1)))].

Definition paper_main_gaussian_residual_joint_event D N d (P : D.-tuple T -> 'M[R]_d)
    (r : R) : set ((Nat.add D (N * d)%N).-tuple T) :=
  paper_main_split_coordinates D (N * d)%N @^-1` paper_main_gaussian_residual_joint_set D N d P r.

Lemma paper_main_gaussian_residual_joint_pairing_measurable D N d
    (P : D.-tuple T -> 'M[R]_d) (i : nat) :
  (forall a b : 'I_d, measurable_fun [set: D.-tuple T] ((fun z => P z a b) : _ -> T)) ->
  measurable_fun [set: D.-tuple T * paper_main_sample N d]
    ((fun zx => paper_main_pairing (paper_main_head_feature zx.2 i) (P zx.1)) : _ -> T).
Proof.
move=> mP; rewrite /paper_main_pairing.
apply: measurable_sum => a; apply: measurable_sum => b.
apply: measurable_funM.
- exact: (measurableT_comp (paper_main_gaussian_residual_feature_entry_measurable N d i a b)
    measurable_snd).
- exact: (measurableT_comp (mP a b) measurable_fst).
Qed.

Theorem paper_main_gaussian_residual_joint_set_measurable D N d
    (P : D.-tuple T -> 'M[R]_d) (r : R) :
  (forall a b : 'I_d, measurable_fun [set: D.-tuple T] ((fun z => P z a b) : _ -> T)) ->
  measurable (paper_main_gaussian_residual_joint_set D N d P r).
Proof.
move=> mP.
have -> : paper_main_gaussian_residual_joint_set D N d P r =
    paper_main_finite_event_union (List.seq 0 N) (fun i =>
      [set zx : D.-tuple T * paper_main_sample N d |
        Rle r (Rabs (paper_main_pairing (paper_main_head_feature zx.2 i) (P zx.1)))]).
  apply/seteqP; split=> zx /=.
  - move=> [i [Hi Hr]]; apply/paper_main_finite_event_union_member.
    by exists i; split; [apply/List.in_seq; lia | exact: Hr].
  - move/paper_main_finite_event_union_member => [i [Hi Hr]].
    by exists i; split; [move/List.in_seq: Hi; lia | exact: Hr].
elim: (List.seq 0 N) => [|i s IH] /=; first exact: measurable0.
apply: measurableU => //.
apply: paper_main_gaussian_residual_abs_ge_measurable.
exact: paper_main_gaussian_residual_joint_pairing_measurable.
Qed.

Theorem paper_main_gaussian_residual_joint_measurable D N d
    (P : D.-tuple T -> 'M[R]_d) (r : R) :
  (forall a b : 'I_d, measurable_fun [set: D.-tuple T] ((fun z => P z a b) : _ -> T)) ->
  measurable (paper_main_gaussian_residual_joint_event D N d P r).
Proof.
move=> mP.
have H := paper_main_split_coordinates_measurable D (N * d)%N measurableT _
  (paper_main_gaussian_residual_joint_set_measurable D N d P r mP).
by rewrite setTI in H.
Qed.

Lemma paper_main_gaussian_residual_joint_section D N d (P : D.-tuple T -> 'M[R]_d)
    (r : R) (z : D.-tuple T) :
  xsection (paper_main_gaussian_residual_joint_set D N d P r) z =
  paper_main_gaussian_residual_event N d (P z) r.
Proof.
apply/seteqP; split=> x.
- by move/xsectionP.
- by move=> Hx; apply/xsectionP.
Qed.

(* The joint tail. *)

Theorem paper_main_gaussian_residual_joint_tail D N n
    (P : D.-tuple T -> 'M[R]_(S n)) (H : set (D.-tuple T)) (kappa r : R) :
  (forall a b : 'I_(S n), measurable_fun [set: D.-tuple T] ((fun z => P z a b) : _ -> T)) ->
  measurable H ->
  (forall z, ~ H z ->
    [/\ paper_main_symmetric (P z), paper_main_pairing (P z) (P z) = 1 &
      paper_main_cone_opnorm_le (P z) (kappa / Num.sqrt (S n)%:R)]) ->
  0 <= kappa -> 0 < r ->
  measurable (paper_main_gaussian_residual_joint_event D N (S n) P r) /\
  (gaussian_product_law (Nat.add D (N * S n)%N)
    (paper_main_gaussian_residual_joint_event D N (S n) P r) <=
    (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
      (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E + gaussian_product_law D H)%E.
Proof.
move=> mP mH HP Hk Hr.
split; first exact: paper_main_gaussian_residual_joint_measurable.
apply: paper_main_head_exception_bound.
- exact: paper_main_gaussian_residual_joint_set_measurable.
- exact: mH.
- rewrite lee_fin; apply: mulr_ge0; first exact/RleP/pos_INR.
  apply/RleP; apply: Rmult_le_pos; first lra.
  by apply: Rlt_le; exact: exp_pos.
- move=> z Hz.
  have [HPs HP1 HPb] := HP z Hz.
  rewrite paper_main_gaussian_residual_joint_section.
  exact: (proj2 (paper_main_gaussian_residual_rows_tail N n (P z) kappa r HPs HP1 Hk HPb Hr)).
Qed.

Corollary paper_main_gaussian_residual_joint_tail_all D N n
    (P : D.-tuple T -> 'M[R]_(S n)) (kappa r : R) :
  (forall a b : 'I_(S n), measurable_fun [set: D.-tuple T] ((fun z => P z a b) : _ -> T)) ->
  (forall z, [/\ paper_main_symmetric (P z), paper_main_pairing (P z) (P z) = 1 &
      paper_main_cone_opnorm_le (P z) (kappa / Num.sqrt (S n)%:R)]) ->
  0 <= kappa -> 0 < r ->
  measurable (paper_main_gaussian_residual_joint_event D N (S n) P r) /\
  (gaussian_product_law (Nat.add D (N * S n)%N)
    (paper_main_gaussian_residual_joint_event D N (S n) P r) <=
    (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
      (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E)%E.
Proof.
move=> mP HP Hk Hr.
have [mE HE] := paper_main_gaussian_residual_joint_tail D N n P set0 kappa r mP measurable0
  (fun z _ => HP z) Hk Hr.
by split=> //; rewrite measure0 adde0 in HE.
Qed.

(* A constant matrix: the joint event is the residual event of the sample. *)
