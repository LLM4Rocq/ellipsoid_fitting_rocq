(* The exact law of a projected standard Gaussian array.
   An N-by-M array X is the row-major list of its entries (entry (i, j) at
   position i * M + j, as in Gordon.Escape). For a loading
   U : nat -> nat -> R whose first s rows are orthonormal in R^N,
     gaussian_covariance_entry N U a a' = [a = a']   (a, a' < s),
   the projected array U X (s by M) is the covariance image of X under the
   loading P_U (k, l) = U (k / M, l / M) [k mod M = l mod M]
   (paper_main_projected_loading), and P_U has orthonormal rows in R^(N M)
   (paper_main_projected_loading_orthonormal). The map
   paper_main_projected_map : (N M)-tuples -> (s M)-tuples is measurable, and
   it sends gaussian_product_law (N * M) to gaussian_product_law (s * M)
   (paper_main_projected_law): read on row vectors through Gaussian.LawBridge,
   it is x |-> x *m A for a matrix A with orthonormal columns, and
   gauss_orthogonal_law of the library gives the law of x *m A. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability numfun.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceDefinitions
  Gaussian.CovarianceLinearImages Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinatePolynomialContinuity Gaussian.FiniteSums
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gaussian.ProductLawBasics Gordon.ProcessCovariance
  Analysis.CoordinateTopology Gaussian.LawBridge Gaussian.CovarianceBounds.
From GaussianAnalysis Require Import measurable_matrix gauss gauss_law.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* The loading of the projected array. *)

Definition paper_main_projected_loading (M : nat) (U : nat -> nat -> R) (k l : nat) : R :=
  U (k / M)%nat (l / M)%nat * (if Nat.eqb (k mod M) (l mod M) then 1 else 0).

Definition paper_main_projected_orthonormal (s N : nat) (U : nat -> nat -> R) : Prop :=
  forall a a', (a < s)%coq_nat -> (a' < s)%coq_nat ->
    gaussian_covariance_entry N U a a' = if Nat.eqb a a' then 1 else 0.

Lemma paper_main_projected_row (N M : nat) (U : nat -> nat -> R) (a j : nat)
    (xs : list R) :
  (j < M)%coq_nat ->
  gaussian_covariance_row (N * M) (paper_main_projected_loading M U) (a * M + j) xs =
  finite_sum (fun i => U a i * List.nth (i * M + j) xs 0) (List.seq 0 N).
Proof.
move=> Hj.
rewrite /gaussian_covariance_row paper_main_gordon_sum_rectangle.
apply: finite_sum_ext => i _.
rewrite -(finite_sum_delta M j (U a i * List.nth (i * M + j) xs 0) Hj).
apply: finite_sum_ext => j' Hj'.
have Hj'M : (j' < M)%coq_nat by have := in_seq_lt _ _ Hj'; lia.
rewrite /paper_main_projected_loading.
rewrite !paper_main_gordon_row_major_div // !paper_main_gordon_row_major_mod //.
case: (Nat.eqb_spec j j') => [<-|Hne].
  by rewrite Nat.eqb_refl Rmult_1_r.
have -> : Nat.eqb j' j = false by apply/Nat.eqb_neq => H; apply: Hne.
ring.
Qed.

Lemma paper_main_projected_delta_dot (M j j' : nat) :
  (j < M)%coq_nat -> (j' < M)%coq_nat ->
  paper_main_gordon_dot M (fun t => if Nat.eqb j t then 1 else 0)
    (fun t => if Nat.eqb j' t then 1 else 0) = if Nat.eqb j j' then 1 else 0.
Proof.
move=> Hj Hj'; rewrite /paper_main_gordon_dot.
rewrite -(finite_sum_delta M j (if Nat.eqb j j' then 1 else 0) Hj).
apply: finite_sum_ext => t _.
case: (Nat.eqb_spec j t) => [<-|Hne].
  by rewrite Nat.eqb_refl Rmult_1_l Nat.eqb_sym.
have -> : Nat.eqb t j = false by apply/Nat.eqb_neq => H; apply: Hne.
by rewrite Rmult_0_l.
Qed.

(* The projected loading has orthonormal rows. *)

Theorem paper_main_projected_loading_orthonormal s N M (U : nat -> nat -> R) :
  paper_main_projected_orthonormal s N U ->
  forall k k', (k < s * M)%coq_nat -> (k' < s * M)%coq_nat ->
    gaussian_covariance_entry (N * M) (paper_main_projected_loading M U) k k' =
    if Nat.eqb k k' then 1 else 0.
Proof.
move=> HU k k' Hk Hk'.
have Hk2 : (k < Nat.mul s M)%coq_nat := Hk.
have Hk2' : (k' < Nat.mul s M)%coq_nat := Hk'.
have HM : (0 < M)%coq_nat by nia.
have Ha : (k / M < s)%coq_nat by apply: Nat.Div0.div_lt_upper_bound; lia.
have Ha' : (k' / M < s)%coq_nat by apply: Nat.Div0.div_lt_upper_bound; lia.
have Hj : (k mod M < M)%coq_nat by apply: Nat.mod_upper_bound; lia.
have Hj' : (k' mod M < M)%coq_nat by apply: Nat.mod_upper_bound; lia.
have T := paper_main_gordon_tensor_dot N M (U (k / M)%nat) (U (k' / M)%nat)
  (fun t => if Nat.eqb (k mod M) t then 1 else 0)
  (fun t => if Nat.eqb (k' mod M) t then 1 else 0).
transitivity (paper_main_gordon_dot N (U (k / M)%nat) (U (k' / M)%nat) *
  paper_main_gordon_dot M (fun t => if Nat.eqb (k mod M) t then 1 else 0)
    (fun t => if Nat.eqb (k' mod M) t then 1 else 0)).
  by rewrite -T.
rewrite paper_main_projected_delta_dot //.
have -> : paper_main_gordon_dot N (U (k / M)%nat) (U (k' / M)%nat) =
    gaussian_covariance_entry N U (k / M)%nat (k' / M)%nat by [].
rewrite HU //.
have Hk_eq := Nat.div_mod k M ltac:(lia).
have Hk'_eq := Nat.div_mod k' M ltac:(lia).
case: (Nat.eqb_spec (k / M) (k' / M)) => Hd;
  case: (Nat.eqb_spec (k mod M) (k' mod M)) => Hm;
  case: (Nat.eqb_spec k k') => Hkk; try ring; exfalso.
- by apply: Hkk; rewrite Hk_eq Hk'_eq Hd Hm.
- by apply: Hm; rewrite Hkk.
- by apply: Hd; rewrite Hkk.
- by apply: Hd; rewrite Hkk.
Qed.

(* The projected array as a map of tuples. *)

Definition paper_main_projected_image (s N M : nat) (U : nat -> nat -> R) (xs : list R) :
    list R :=
  gaussian_covariance_image (s * M) (N * M) (paper_main_projected_loading M U) xs.

Lemma paper_main_projected_image_size s N M U xs :
  size (paper_main_projected_image s N M U xs) == (s * M)%N.
Proof.
apply/eqP; rewrite /paper_main_projected_image /gaussian_covariance_image.
exact: length_map_seq.
Qed.

Definition paper_main_projected_map (s N M : nat) (U : nat -> nat -> R)
    (x : (N * M).-tuple T) : (s * M).-tuple T :=
  @Tuple (s * M) T (paper_main_projected_image s N M U (tval x))
    (paper_main_projected_image_size s N M U (tval x)).

Lemma paper_main_projected_map_val s N M U (x : (N * M).-tuple T) :
  tval (paper_main_projected_map s N M U x) = paper_main_projected_image s N M U (tval x).
Proof. by []. Qed.

Lemma paper_main_projected_row_continuous p (P : nat -> nat -> R) a :
  finite_joint_continuous p (gaussian_covariance_row p P a).
Proof.
rewrite /gaussian_covariance_row.
apply: (finite_joint_continuous_sum p (List.seq 0 p) (fun k xs => P a k * List.nth k xs 0)).
move=> k Hk; apply: finite_joint_continuous_scale.
by apply: finite_joint_continuous_nth; have := in_seq_lt _ _ Hk; lia.
Qed.

Lemma paper_main_projected_map_measurable s N M U :
  measurable_fun [set: (N * M).-tuple T] (paper_main_projected_map s N M U).
Proof.
apply/measurable_fun_tnthP => i.
have -> : (@tnth (s * M) T ^~ i \o paper_main_projected_map s N M U) =
    (fun x : (N * M).-tuple T =>
      gaussian_covariance_row (N * M) (paper_main_projected_loading M U) i (tval x)).
  apply: funext => x /=.
  rewrite (tnth_nth 0%R) /= /paper_main_projected_image /gaussian_covariance_image.
  rewrite -gpp_nthE.
  have Hi : (i < s * M)%coq_nat by apply/ssrnat.ltP; exact: ltn_ord.
  by rewrite (nth_map_seq _ (s * M) i Hi).
exact: (gpp_joint_measurable (N * M) _ (paper_main_projected_row_continuous _ _ _)).
Qed.

HB.instance Definition _ s N M U := isMeasurableFun.Build _ _ _ _
  (paper_main_projected_map s N M U) (paper_main_projected_map_measurable s N M U).

(* The exact law of the projected array: for every measurable event E of
   s-by-M arrays, P_(N M)(U X in E) = P_(s M)(E). *)

Section projected_law.
Local Notation RR := (R : realType).

Lemma paper_main_projected_tuple_of_row d (t : d.-tuple T) :
  tuple_of_row (row_of_tuple d t) = t.
Proof. by apply: val_inj; exact: list_of_row_of_tuple. Qed.

Lemma paper_main_projected_product_law d (E : set (d.-tuple T)) : measurable E ->
  gaussian_product_law d E = gauss d [set x : 'rV[RR]_d | E (tuple_of_row x)].
Proof.
move=> mE.
have mX : measurable [set x : 'rV[RR]_d | E (tuple_of_row x)].
  by have := measurable_tuple_of_row d measurableT E mE; rewrite setTI.
rewrite (gauss_gaussian_product_law _ _ mX).
by congr (gaussian_product_law d _); apply/seteqP; split => t /=;
  rewrite paper_main_projected_tuple_of_row.
Qed.

Theorem paper_main_projected_law s N M (U : nat -> nat -> R)
    (E : set ((s * M).-tuple T)) :
  paper_main_projected_orthonormal s N U -> measurable E ->
  gaussian_product_law (N * M) (paper_main_projected_map s N M U @^-1` E) =
  gaussian_product_law (s * M) E.
Proof.
move=> HU mE.
set P := paper_main_projected_loading M U.
set A := paper_main_covariance_mx (N * M) (s * M) P.
have mPE : measurable (paper_main_projected_map s N M U @^-1` E).
  by have := paper_main_projected_map_measurable s N M U measurableT E mE; rewrite setTI.
have mX : measurable [set y : 'rV[RR]_(s * M) | E (tuple_of_row y)].
  by have := measurable_tuple_of_row (s * M) measurableT E mE; rewrite setTI.
have A1 : (A^T *m A)%R = 1%:M%R.
  apply/matrixP => a b; rewrite paper_main_covariance_gram mxE.
  rewrite (paper_main_projected_loading_orthonormal s N M U HU);
    try by apply/ssrnat.ltP.
  case: (Nat.eqb_spec a b) => [ab|ab]; first by rewrite (val_inj ab) eqxx.
  by case: eqP => // ab'; case: ab; rewrite ab'.
rewrite !paper_main_projected_product_law// -(gauss_orthogonal_law A1 mX).
congr (gauss (N * M) _); apply/seteqP; split => x /=;
  suff -> : paper_main_projected_map s N M U (tuple_of_row x) =
    tuple_of_row (x *m A)%R by [].
all: apply: val_inj; rewrite /= /paper_main_projected_image.
all: by rewrite -[tval (tuple_of_row x)]/(list_of_row x) paper_main_covariance_image_row.
Qed.

End projected_law.
