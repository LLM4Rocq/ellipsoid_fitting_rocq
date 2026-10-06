From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive realfun.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Gibbs.CurveDerivatives Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Gibbs.MatrixDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Frechet derivatives of soft maxima and of the inner values of the matrix
   Gibbs function. Let U be a real normed space and each score F i be
   differentiable at A with differential D i. If c <> 0 and I is nonempty,
   then M |-> soft_max c (fun i => F i M) I is differentiable at A, with
   differential H |-> gibbs_average c (fun i => F i A) I (fun i => D i H)
   (soft_max_frechet). For soft_min beta, the differential is the Gibbs
   average with parameter - beta (soft_min_frechet). The affine score
   offset y s + trace_pair (coeff y s) M has differential
   trace_pair (coeff y s) (matrix_affine_score_frechet), so the inner soft
   maxima matrix_inner_values have differential matrix_inner_derivative
   (matrix_inner_frechet).

   is_diff A f l is MathComp's Frechet differentiability: f is
   differentiable at A and its differential 'd f A is l. Maps into R are
   written with codomain R^o, the normed module view of R, because is_diff
   needs a normed module on the codomain; R^o is R by definition. The
   arithmetic, exp and ln are Stdlib's. *)

(* If Stdlib's derivable_pt_lim f x l holds, then f is Frechet
   differentiable at x as a map from R^o to R^o, with differential
   h |-> h * l. The first step, to MathComp's is_derive x 1 f l, repeats the
   proof of is_derive_of_Reals (Analysis.CalculusBridge): both say that
   (f (x + h) - f x) / h tends to l as h tends to 0 with h <> 0. The second
   step uses derivable1_diffP and diff1E of MathComp-Analysis. *)
Lemma matrix_gibbs_is_diff_of_Reals (f : R -> R) (x l : R) :
  derivable_pt_lim f x l ->
  is_diff (x : R^o) (f : R^o -> R^o) (fun h : R^o => h * l).
Proof.
move=> Hd.
have Hder : @is_derive R R^o R^o x 1 f l.
{ apply: DeriveDef; last apply: cvg_lim;
    [apply/cvg_ex; exists l | exact: norm_hausdorff |].
  all: apply/cvgrPdist_lt => e /RltP e0.
  all: have [d Hdl] := Hd e e0.
  all: rewrite near_withinE; exists (pos d); [by apply/RltP; exact: cond_pos d|].
  all: move=> h /= Hh hN0.
  all: have hN0' : h <> 0 by move/eqP: hN0.
  all: have Hh' : Rabs h < d by move: Hh; rewrite /ball /= sub0r normrN => /RltP.
  all: have H := Hdl h hN0' Hh'.
  all: apply/RltP; rewrite -RabsE -RminusE Rabs_minus_sym.
  all: rewrite [X in Rabs (X - _)](_ : _ = (f (x + h) - f x) / h); [|exact: H].
  all: rewrite /GRing.scale /= mulr1 RplusE RminusE RdivE.
  all: by rewrite [(h + x)%R]addrC mulrC. }
have [Ed Hv] := Hder.
have Dd : differentiable (f : R^o -> R^o) x by apply/derivable1_diffP.
apply: DiffDef; first exact Dd.
rewrite diff1E // derive1E Hv; apply: funext => h /=.
reflexivity.
Qed.

Lemma matrix_gibbs_sum_frechet {U : normedModType R}
    (F D : nat -> U -> R) (I : list nat) (A : U) :
  (forall i, In i I -> is_diff A (F i : U -> R^o) (D i)) ->
  is_diff A ((fun M => finite_sum (fun i => F i M) I) : U -> R^o)
    (fun H => finite_sum (fun i => D i H) I).
Proof.
  induction I as [|i I IH]; intros HF; simpl.
  - exact (is_diff_cst (0 : R^o) A).
  - have H1 : is_diff A (F i : U -> R^o) (D i) by apply HF; simpl; auto.
    have H2 := IH (fun j Hj => HF j (or_intror Hj)).
    exact (is_diffD H1 H2).
Qed.

Lemma matrix_gibbs_exp_frechet {U : normedModType R}
    (c : R) (f df : U -> R) (A : U) :
  is_diff A (f : U -> R^o) df ->
  is_diff A ((fun M => exp (c * f M)) : U -> R^o)
    (fun H => exp (c * f A) * (c * df H)).
Proof.
  intros HF.
  have Hc : is_diff A ((fun M => c * f M) : U -> R^o) (fun H => c * df H).
  { exact (is_diffZ c HF). }
  have He := matrix_gibbs_is_diff_of_Reals exp (c * f A) (exp (c * f A))
    (derivable_pt_lim_exp (c * f A)).
  have HC := is_diff_comp Hc He.
  apply: (is_diff_eq HC).
  apply: funext => H /=; apply Rmult_comm.
Qed.

(* Differentiating a finite soft maximum in an arbitrary real normed space
   gives the Gibbs average of its bounded linear score derivatives. *)
Theorem soft_max_frechet {U : normedModType R}
    (c : R) (F D : nat -> U -> R) (I : list nat) (A : U) :
  c <> 0 -> I <> [] ->
  (forall i, In i I -> is_diff A (F i : U -> R^o) (D i)) ->
  is_diff A ((fun M => soft_max c (fun i => F i M) I) : U -> R^o)
    (fun H => gibbs_average c (fun i => F i A) I (fun i => D i H)).
Proof.
  intros Hc HI HF.
  assert (HZ : 0 < partition c (fun i => F i A) I)
    by (apply partition_positive; exact HI).
  assert (HP : is_diff A
    ((fun M => partition c (fun i => F i M) I) : U -> R^o)
    (fun H => finite_sum (fun i => exp (c * F i A) * (c * D i H)) I)).
  { unfold partition; apply matrix_gibbs_sum_frechet.
    intros i Hi; apply matrix_gibbs_exp_frechet, HF; exact Hi. }
  assert (HL : is_diff (partition c (fun i => F i A) I : R^o)
    ((fun p : R => ln p / c) : R^o -> R^o)
    (fun h : R^o => h * ((/ partition c (fun i => F i A) I) / c))).
  { apply matrix_gibbs_is_diff_of_Reals, derivable_pt_lim_div_scal,
      derivable_pt_lim_ln; exact HZ. }
  have HC := is_diff_comp HP HL.
  unfold soft_max; apply: (is_diff_eq HC).
  (* The equation is stated in R^o, which is R by definition. *)
  apply: funext => H /=.
  match goal with |- ?a = ?b => change (@eq R a b) end.
  assert (HE : finite_sum (fun i => exp (c * F i A) * (c * D i H)) I =
    c * finite_sum (fun i => exp (c * F i A) * D i H) I).
  { rewrite <- gibbs_sum_scale; apply gibbs_sum_ext; intros; ring. }
  rewrite HE gibbs_average_ratio; field; split; lra.
Qed.

Theorem soft_min_frechet {U : normedModType R}
    (beta : R) (F D : nat -> U -> R) (I : list nat) (A : U) :
  beta <> 0 -> I <> [] ->
  (forall i, In i I -> is_diff A (F i : U -> R^o) (D i)) ->
  is_diff A ((fun M => soft_min beta (fun i => F i M) I) : U -> R^o)
    (fun H => gibbs_average (- beta) (fun i => F i A) I (fun i => D i H)).
Proof.
  intros Hb HI HF.
  have E : (fun M => soft_min beta (fun i => F i M) I) =
    (fun M => soft_max (- beta) (fun i => F i M) I).
  { apply: funext => M; apply soft_min_signed_identity; exact Hb. }
  rewrite E; apply soft_max_frechet; try assumption; lra.
Qed.

Theorem matrix_affine_score_frechet n offset coeff (A : matrix n) y s :
  is_diff A
    ((fun M => matrix_affine_scores n offset coeff M y s) : matrix n -> R^o)
    (fun H => trace_pair n (coeff y s) H).
Proof.
  unfold matrix_affine_scores.
  have HD := is_diffD (is_diff_cst (offset y s : R^o) A)
    (trace_pair_frechet n (coeff y s) A).
  apply: (is_diff_eq HD).
  apply: funext => H /=; apply Rplus_0_l.
Qed.

Theorem matrix_inner_frechet n gamma offset coeff S (A : matrix n) y :
  0 < gamma -> S <> [] ->
  is_diff A
    ((fun M => matrix_inner_values n gamma offset coeff S M y) : matrix n -> R^o)
    (fun H => matrix_inner_derivative n gamma offset coeff S A H y).
Proof.
  intros Hg HS; unfold matrix_inner_values, matrix_inner_derivative.
  apply (soft_max_frechet gamma
    (fun s M => matrix_affine_scores n offset coeff M y s)
    (fun s H => trace_pair n (coeff y s) H) S A).
  - lra.
  - exact HS.
  - intros; apply matrix_affine_score_frechet.
Qed.
