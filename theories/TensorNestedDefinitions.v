From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions ThirdDefinitions MomentDefinitions
  MatrixDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions MatrixThirdDefinitions
  OperatorDefinitions TensorDefinitions TensorGibbsDefinitions TensorCombinationsDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/TensorNestedDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly. Its
   only Coquelicot content came through matrix n of MatrixDefinitions, the
   record trace_atom of TensorDefinitions, and the definitions of
   MatrixGibbsDefinitions, TensorGibbsDefinitions and
   TensorCombinationsDefinitions. Their ports keep the same names, arguments
   and fields, so the import of Coquelicot is dropped and nothing else
   changes. MathComp is not imported here, so the lists, the concatenation
   ++, and the arithmetic, including the powers gamma ^ 2 and beta ^ 2, the
   product - beta * gamma and the minus sign of - beta, are Stdlib's, as
   before. gibbs_weight comes from GibbsDefinitions, which is copied
   unchanged, so its exp is Stdlib's. *)

Definition nested_inner_weights n gamma offset coeff S (A : matrix n) y : nat -> R :=
  gibbs_weight gamma (matrix_affine_scores n offset coeff A y) S.

Definition nested_outer_weights n beta gamma offset coeff Y S (A : matrix n) : nat -> R :=
  gibbs_weight (- beta) (matrix_inner_values n gamma offset coeff S A) Y.

Definition nested_mean_matrix n gamma offset coeff S (A : matrix n) y : matrix n :=
  matrix_gibbs_mean n gamma (matrix_affine_scores n offset coeff A y) S (coeff y).

Definition nested_inner_center n gamma offset coeff S (A : matrix n) y s : matrix n :=
  matrix_centered n (nested_inner_weights n gamma offset coeff S A y) (coeff y) S s.

Definition nested_outer_center n beta gamma offset coeff Y S (A : matrix n) y : matrix n :=
  matrix_centered n (nested_outer_weights n beta gamma offset coeff Y S A)
    (nested_mean_matrix n gamma offset coeff S A) Y y.

Definition nested_inner_atom_rows n gamma offset coeff S (A : matrix n) y : list (trace_atom n) :=
  centered_trace_atoms n (nested_inner_weights n gamma offset coeff S A y) (coeff y) S.

Definition nested_covariance_atom_rows n beta gamma offset coeff Y S (A : matrix n) y :
    list (trace_atom n) :=
  mixed_trace_atoms n (nested_inner_weights n gamma offset coeff S A y)
    (nested_inner_center n gamma offset coeff S A y)
    (nested_inner_center n gamma offset coeff S A y)
    (fun _ => nested_outer_center n beta gamma offset coeff Y S A y) S.

Definition nested_inner_atoms n beta gamma offset coeff Y S (A : matrix n) : list (trace_atom n) :=
  tensor_weighted_join n (nested_outer_weights n beta gamma offset coeff Y S A)
    (nested_inner_atom_rows n gamma offset coeff S A) Y.

Definition nested_covariance_atoms n beta gamma offset coeff Y S (A : matrix n) : list (trace_atom n) :=
  tensor_weighted_join n (nested_outer_weights n beta gamma offset coeff Y S A)
    (nested_covariance_atom_rows n beta gamma offset coeff Y S A) Y.

Definition nested_outer_atoms n beta gamma offset coeff Y S (A : matrix n) : list (trace_atom n) :=
  centered_trace_atoms n (nested_outer_weights n beta gamma offset coeff Y S A)
    (nested_mean_matrix n gamma offset coeff S A) Y.

Definition nested_third_atoms n beta gamma offset coeff Y S (A : matrix n) : list (trace_atom n) :=
  tensor_scale_atoms (gamma ^ 2) (nested_inner_atoms n beta gamma offset coeff Y S A) ++
  tensor_scale_atoms (- beta * gamma)
    (nested_covariance_atoms n beta gamma offset coeff Y S A ++
     tensor_swap23_atoms n (nested_covariance_atoms n beta gamma offset coeff Y S A) ++
     tensor_rotate_atoms n (nested_covariance_atoms n beta gamma offset coeff Y S A)) ++
  tensor_scale_atoms (beta ^ 2) (nested_outer_atoms n beta gamma offset coeff Y S A).
