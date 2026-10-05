(* Frobenius duality for the public symmetric matrices, in scalar form. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGordonBilinear.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_matrix_weighted_sum {d} N (u : nat -> R) (A : nat -> 'M[R]_d) : 'M[R]_d :=
  (\sum_(i < N) u i *: A i)%R.

Lemma paper_main_finite_sum_public N f :
  finite_sum f (List.seq 0 N) = (\sum_(i < N) f i)%R.
Proof.
elim: N f => [|N IH] f; first by rewrite big_ord0.
rewrite big_ord_recl /=.
rewrite finite_sum_seq_shift.
change (f 0%nat + finite_sum (fun i => f (S i)) (List.seq 0 N) = f 0%nat + (\sum_(i < N) f (S i))%R).
by rewrite IH.
Qed.

Lemma paper_main_frobenius_nonnegative d (T : 'M[R]_d) :
  0 <= paper_main_frobenius T.
Proof.
apply/RleP; apply sqrtr_ge0.
Qed.

Lemma paper_main_frobenius_squared d (T : 'M[R]_d) :
  (paper_main_frobenius T)^2 = paper_main_pairing T T.
Proof.
have H := sqr_sqrtr (paper_main_pairing_self_ge0 d T).
rewrite expr2 in H.
change (paper_main_frobenius T*paper_main_frobenius T = paper_main_pairing T T) in H.
nra.
Qed.

Lemma paper_main_matrix_weighted_sum_symmetric d N u (A : nat -> 'M[R]_d) :
  (forall i, Nat.lt i N -> paper_main_symmetric (A i)) ->
  paper_main_symmetric (paper_main_matrix_weighted_sum N u A).
Proof.
intros H i j.
rewrite /paper_main_matrix_weighted_sum !summxE.
apply: eq_bigr => k _; rewrite !mxE.
rewrite (H k); [exact: (elimT ssrnat.ltP (ltn_ord k))|reflexivity].
Qed.

Lemma paper_main_matrix_weighted_sum_pairing d N u (A : nat -> 'M[R]_d) T :
  paper_main_pairing (paper_main_matrix_weighted_sum N u A) T =
  finite_sum (fun i => u i*paper_main_pairing (A i) T) (List.seq 0 N).
Proof.
rewrite paper_main_pairingC /paper_main_matrix_weighted_sum paper_main_pairing_sum.
rewrite paper_main_finite_sum_public.
apply: eq_bigr => i _; by rewrite paper_main_pairingC.
Qed.

Theorem paper_main_symmetric_frobenius_duality d (A : 'M[R]_d) L :
  paper_main_symmetric A -> 0 <= L ->
  (forall T, paper_main_symmetric T -> Rabs(paper_main_pairing A T) <= L*paper_main_frobenius T) ->
  paper_main_frobenius A <= L.
Proof.
intros HA HL H.
have HH := H A HA.
have Hsq := paper_main_frobenius_squared d A.
have Hpos := paper_main_frobenius_nonnegative d A.
have Habs := Rle_abs (paper_main_pairing A A).
nra.
Qed.

Theorem paper_main_matrix_adjoint_bound d N (A : nat -> 'M[R]_d) L :
  (forall i, Nat.lt i N -> paper_main_symmetric (A i)) -> 0 <= L ->
  (forall u T, paper_main_symmetric T ->
    Rabs(finite_sum (fun i => u i*paper_main_pairing (A i) T) (List.seq 0 N)) <=
    L*euclidean_norm u (List.seq 0 N)*paper_main_frobenius T) ->
  forall u, paper_main_frobenius (paper_main_matrix_weighted_sum N u A) <=
    L*euclidean_norm u (List.seq 0 N).
Proof.
intros HA HL H u.
apply paper_main_symmetric_frobenius_duality.
- apply paper_main_matrix_weighted_sum_symmetric; exact HA.
- apply Rmult_le_pos; [exact HL|apply paper_main_gordon_euclidean_nonnegative].
- intros T HT; rewrite paper_main_matrix_weighted_sum_pairing; apply H; exact HT.
Qed.
