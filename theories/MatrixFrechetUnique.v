From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/MatrixFrechetUnique.v from Coquelicot to MathComp-Analysis.

   Coquelicot's hypothesis filterdiff f (locally A) df becomes MathComp's
   is_diff A f df. Both say that df is linear and continuous and that
   f y - f A - df (y - A) is a little-o of y - A as y tends to A. In
   Coquelicot the continuity of df is the bound M in is_linear, and the
   point x of is_filter_lim (locally A) x can only be A. MathComp's
   is_diff A f df also states df = 'd f A, the chosen differential, which
   is the same condition because that differential is unique. The meaning
   is the same.

   The type E ranges over normedModType R instead of NormedModule R_AbsRing.
   The real line is a normedModType only as R^o, so the scalar functions
   have type E -> R^o. R^o is R by definition, so a function with values in
   R can be passed where one with values in R^o is expected.

   Coquelicot's conclusion is_derive g 0 l, for g a function of a real
   variable, is filterdiff g (locally 0) (fun t => scal t l). It becomes
   MathComp's is_derive 0 1 g l: g is derivable at 0 along 1 with
   derivative l. For a function of a real variable these say the same
   thing. *)

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
