(* A measurable finite argmax for the Frobenius pairing. For a fixed family
   B : nat -> 'M[R]_d of public matrices, a nonempty list q0 :: Q of indices
   and a matrix M, paper_main_finite_argmax_index B M q0 Q compares
   <M, B j> with <M, B q0>, where j is the index selected from Q, and keeps
   q0 when <M, B j> <= <M, B q0>. So the selected index is the FIRST maximizer
   in the list q0 :: Q, and every tie is resolved towards the earlier index.
   The selected matrix paper_main_finite_argmax B M q0 Q = B (index) belongs
   to the family, maximizes <M, B q> over the list, and its pairing equals the
   finite maximum paper_main_finite_max B M q0 Q. If Z is a matrix-valued map
   on any measurable space with measurable entries, the entries of
   z |-> paper_main_finite_argmax B (Z z) q0 Q are measurable: every branch
   is a measurable comparison of two measurable real functions. Only finitely
   many candidates are compared; no measurable choice over an uncountable set
   is claimed. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

Fixpoint paper_main_finite_argmax_index {d : nat} (B : nat -> 'M[R]_d) (M : 'M[R]_d)
    (q0 : nat) (Q : seq nat) : nat :=
  match Q with
  | [::] => q0
  | q :: Q' =>
      let j := paper_main_finite_argmax_index B M q Q' in
      if paper_main_pairing M (B j) <= paper_main_pairing M (B q0) then q0 else j
  end.

Definition paper_main_finite_argmax {d : nat} (B : nat -> 'M[R]_d) (M : 'M[R]_d)
    (q0 : nat) (Q : seq nat) : 'M[R]_d :=
  B (paper_main_finite_argmax_index B M q0 Q).

(* The selected index is in the list and in the family. *)

Lemma paper_main_finite_argmax_index_mem {d : nat} (B : nat -> 'M[R]_d) M q0 Q :
  paper_main_finite_argmax_index B M q0 Q \in q0 :: Q.
Proof.
elim: Q q0 => [|q Q IH] q0 /=; first by rewrite mem_seq1.
case: ifP => _; first by rewrite in_cons eqxx.
by rewrite in_cons IH orbT.
Qed.

(* Maximality, the value, and the first-maximizer rule. *)

Theorem paper_main_finite_argmax_max {d : nat} (B : nat -> 'M[R]_d) M q0 Q :
  forall q, q \in q0 :: Q ->
    paper_main_pairing M (B q) <= paper_main_pairing M (paper_main_finite_argmax B M q0 Q).
Proof.
rewrite /paper_main_finite_argmax.
elim: Q q0 => [|q1 Q IH] q0 q /=; first by rewrite mem_seq1 => /eqP ->.
set j := paper_main_finite_argmax_index B M q1 Q.
rewrite in_cons => /orP [/eqP -> | Hq].
  by case: ifP => [_ | /negbT]; [exact: lexx | rewrite -ltNge => /ltW].
case: ifP => Hj; last exact: IH.
exact: le_trans (IH q1 q Hq) Hj.
Qed.

(* Measurability of the selected matrix. *)

Lemma paper_main_finite_pairing_measurable {dX : measure_display} {X : measurableType dX}
    {d : nat} (F G : X -> 'M[R]_d) :
  (forall a b : 'I_d, measurable_fun [set: X] ((fun x => F x a b) : X -> T)) ->
  (forall a b : 'I_d, measurable_fun [set: X] ((fun x => G x a b) : X -> T)) ->
  measurable_fun [set: X] ((fun x => paper_main_pairing (F x) (G x)) : X -> T).
Proof.
move=> mF mG; rewrite /paper_main_pairing.
apply: measurable_sum => a; apply: measurable_sum => b.
by apply: measurable_funM; [exact: mF | exact: mG].
Qed.

Theorem paper_main_finite_argmax_measurable {dX : measure_display} {X : measurableType dX}
    {d : nat} (B : nat -> 'M[R]_d) (Z : X -> 'M[R]_d) q0 Q :
  (forall a b : 'I_d, measurable_fun [set: X] ((fun x => Z x a b) : X -> T)) ->
  forall a b : 'I_d,
    measurable_fun [set: X] ((fun x => paper_main_finite_argmax B (Z x) q0 Q a b) : X -> T).
Proof.
move=> mZ; rewrite /paper_main_finite_argmax.
elim: Q q0 => [|q1 Q IH] q0 a b /=; first exact: measurable_cst.
set j := fun x => paper_main_finite_argmax_index B (Z x) q1 Q.
have -> : (fun x => B (if paper_main_pairing (Z x) (B (j x)) <=
      paper_main_pairing (Z x) (B q0) then q0 else j x) a b) =
    (fun x => if paper_main_pairing (Z x) (B (j x)) <= paper_main_pairing (Z x) (B q0)
      then B q0 a b else B (j x) a b).
  by apply: funext => x; case: ifP.
apply: measurable_fun_ifT.
- apply: measurable_fun_ler.
  + apply: paper_main_finite_pairing_measurable => // a' b'; exact: IH.
  + apply: paper_main_finite_pairing_measurable => // a' b'; exact: measurable_cst.
- exact: measurable_cst.
- exact: IH.
Qed.
