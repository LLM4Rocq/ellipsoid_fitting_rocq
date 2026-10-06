From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Uniqueness of the Frechet derivative of a real function on a normed
   module E. is_diff A f df says that f is differentiable at A with
   differential df, a continuous linear map. scalar_frechet_line: the
   function t |-> f (A + t U) of a real variable then has derivative df U at
   0. scalar_frechet_unique: two differentials of f at A agree on every
   vector. The real line is a normed module only as R^o, so the scalar
   functions have type E -> R^o; R^o is R by definition. *)

Lemma scalar_frechet_line {E : normedModType R}
    (f df : E -> R^o) (A U : E) :
  is_diff A f df ->
  is_derive (0 : R^o) (1 : R^o) (fun t : R^o => f (A + t *: U)%R) (df U).
Proof.
move=> HF.
have HL : is_diff (0 : R^o) (fun t : R^o => (A + t *: U)%R)
    (fun t : R^o => t *: U)%R.
  have -> : (fun t : R^o => (A + t *: U)%R) = (cst A + ( *:%R^~ U))%R.
    by apply/funext => t.
  apply: (is_diff_eq (is_diffD (is_diff_cst A (0 : R^o)) (is_diff_scalel 0 U))).
  by apply/funext => t /=; rewrite add0r.
have HA : (A + (0 : R^o) *: U)%R = A by rewrite scale0r addr0.
have HD : is_diff (A + (0 : R^o) *: U)%R f df by rewrite HA.
have HC := is_diff_comp HL HD.
apply: DeriveDef.
  exact/diff_derivable/ex_diff.
by rewrite deriveE ?diff_val //= scale1r.
Qed.

Theorem scalar_frechet_unique {E : normedModType R}
    (f df dg : E -> R^o) (A : E) :
  is_diff A f df -> is_diff A f dg ->
  forall U : E, df U = dg U.
Proof.
move=> HF HG U.
have Hf := @derive_val _ _ _ _ _ _ _ (scalar_frechet_line f df A U HF).
have Hg := @derive_val _ _ _ _ _ _ _ (scalar_frechet_line f dg A U HG).
by rewrite -Hf -Hg.
Qed.
