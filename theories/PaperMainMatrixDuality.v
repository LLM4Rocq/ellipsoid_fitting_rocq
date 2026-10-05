(* Frobenius duality for the public symmetric matrices, in scalar form. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGordonBilinear.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

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
