From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions
  SecondChaosDefinitions QuadraticDefinitions QuadraticGrowthProofs
  GaussianVectorDefinitions GaussianVectorStein.
Import QuadraticGrowthProofs.QuadraticGrowth.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Stein's identity in two coordinates for an entry of the quadratic
   gradient. quadratic_gaussian_entry_stein: for beta, gamma > 0, nonempty
   Y and S and a, b <= n, let g x be the entry (a, b) of quadratic_gradient
   at x. Then g, the entries (a, b) of its first derivative along
   chaos_basis n a and of its second derivative along chaos_basis n a and
   chaos_basis n b, and (x_a * x_b - [a = b]) * g x satisfy
   gaussian_vector_domain, and the Gaussian expectation of the second
   derivative equals that of (x_a * x_b - [a = b]) * g x. The proof applies
   gaussian_vector_second_stein of GaussianVectorStein, with the
   regularity given by quadratic_gradient_entry_polynomial_regular.

   gaussian_vector_domain and gaussian_vector_expectation ask for Lebesgue
   integrability against the Gaussian kernel at each level of the iterated
   expectation. With ssreflect loaded, the statement writes
   (a <= n)%coq_nat for Stdlib's order on nat. *)

Theorem quadratic_gaussian_entry_stein n beta gamma offset coeff Y S lambda C a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  List.Forall (gaussian_vector_domain n)
    [(fun x => matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b);
     (fun x => matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x
       (chaos_basis n a)) a b);
     (fun x => matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x
       (chaos_basis n a) (chaos_basis n b)) a b);
     (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
       matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)] /\
  gaussian_vector_expectation n
    (fun x => matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x
      (chaos_basis n a) (chaos_basis n b)) a b) =
  gaussian_vector_expectation n
    (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
      matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b).
Proof.
  intros Hb Hg HY HS Ha Hbb.
  destruct (quadratic_gradient_entry_polynomial_regular n beta gamma offset coeff Y S lambda C
    (chaos_basis n a) (chaos_basis n b) a b Hb Hg HY HS Ha Hbb)
    as [K0 [K1 [K2 [H0 [H1 [H2 Hregular]]]]]].
  apply (gaussian_vector_second_stein n a b
    (fun x => matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)
    (fun x u => matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x u) a b)
    (fun x u v => matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u v) a b)
    K0 O K1 (Datatypes.S O) K2 (Datatypes.S (Datatypes.S O))); try assumption;
    intro x; specialize (Hregular x); tauto.
Qed.
