From Stdlib Require Import Reals Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace MatrixAssembly
  OperatorDefinitions HessianDefinitions CoefficientMaps SecondChaosDefinitions QuadraticDefinitions.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/QuadraticCalculus.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. The statements change form in four ways, the ways of
   the ports of MatrixCoordinates and MatrixAssembly, which this module
   imports.

   1. Normed spaces. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R. On vector n and matrix n the norms are the Euclidean
      and Frobenius norms of MatrixDefinitions, as in Coquelicot, and on
      hessian_array n the Euclidean norm of all its entries.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally x) l becomes
      is_diff x f l of MathComp-Analysis: f is differentiable at x and its
      differential 'd f x is l. Both say that l is linear and continuous and
      that f (x + h) = f x + l h + o(h) as h tends to 0.

   3. Real-valued maps. A map into R given to is_diff is written with
      codomain R^o, the normed module view of R, as in (F i : E -> R^o).
      R^o is R by definition, so the maps are the same.

   4. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statement of quadratic_coordinate_sum_frechet writes (i <= n)%coq_nat,
      which is Stdlib's le.

   So the hypotheses and the conclusions say the same thing as in the
   original. The arithmetic is Stdlib's, as before.

   The port adds one lemma, quadratic_mult_frechet, marked below. In the
   proofs, filterdiff_linear becomes matrix_linear_is_diff of
   MatrixCoordinates, filterdiff_const becomes is_diff_cst,
   filterdiff_plus_fct, filterdiff_minus_fct and filterdiff_scal_r_fct become
   is_diffD, is_diffB and is_diffZ, filterdiff_mult_fct becomes
   quadratic_mult_frechet, filterdiff_comp' becomes is_diff_comp, and
   filterdiff_ext_lin becomes is_diff_eq with an equation of functions. *)

(* Added by the port. The product rule, with the arguments and the
   derivative H |-> df H * g A + f A * dg H of Coquelicot's
   filterdiff_mult_fct, whose hypothesis that the product of the scalars
   commutes is dropped, since the scalars are the reals. MathComp-Analysis
   states the product rule (is_diffM) with its own operations on functions,
   so this lemma restates it with Stdlib's product and sum. *)
Lemma quadratic_mult_frechet {E : normedModType R}
    (f g : E -> R) (A : E) (df dg : E -> R) :
  is_diff A (f : E -> R^o) df -> is_diff A (g : E -> R^o) dg ->
  is_diff A ((fun M => f M * g M) : E -> R^o)
    (fun H => df H * g A + f A * dg H).
Proof.
  intros HF HG.
  have HM := is_diffM HF HG.
  apply: (is_diff_eq HM).
  apply: funext => H.
  change (f A * dg H + g A * df H = df H * g A + f A * dg H).
  ring.
Qed.

Theorem quadratic_vector_entry_frechet n i (x : vector n) :
  is_diff x ((fun z : vector n => vector_entry n z i) : vector n -> R^o)
    (fun u : vector n => vector_entry n u i).
Proof. apply matrix_linear_is_diff, tuple_entry_linear. Qed.

Lemma quadratic_coordinate_sum_frechet {E : normedModType R}
    n (F D : nat -> E -> R) (x : E) :
  (forall i, (i <= n)%coq_nat -> is_diff x (F i : E -> R^o) (D i)) ->
  is_diff x ((fun z => coordinate_sum n (fun i => F i z)) : E -> R^o)
    (fun u => coordinate_sum n (fun i => D i u)).
Proof.
  revert F D; induction n as [|n IH]; intros F D HF; simpl.
  - apply HF; lia.
  - have H0 : is_diff x (F O : E -> R^o) (D O) by apply HF; lia.
    have H1 : is_diff x
      ((fun z => coordinate_sum n (fun i => F (S i) z)) : E -> R^o)
      (fun u => coordinate_sum n (fun i => D (S i) u)).
    { apply (IH (fun i => F (S i)) (fun i => D (S i))); intros i Hi; apply HF; lia. }
    exact (is_diffD H0 H1).
Qed.

Lemma quadratic_coordinate_sum_add n f g :
  coordinate_sum n (fun i => f i + g i) = coordinate_sum n f + coordinate_sum n g.
Proof. revert f g; induction n; intros; simpl; [reflexivity|rewrite IHn; ring]. Qed.

Theorem quadratic_matrix_frechet n lambda C (x : vector n) :
  is_diff x (quadratic_matrix n lambda C) (quadratic_first n lambda x).
Proof.
  unfold quadratic_matrix, quadratic_first.
  apply matrix_build_frechet; intros i j Hi Hj.
  have HP := quadratic_mult_frechet
    (fun z : vector n => vector_entry n z i) (fun z : vector n => vector_entry n z j) x
    (fun u : vector n => vector_entry n u i) (fun u : vector n => vector_entry n u j)
    (quadratic_vector_entry_frechet n i x) (quadratic_vector_entry_frechet n j x).
  have HD : is_diff x
    ((fun z : vector n => matrix_entry n C i j + lambda *
      (vector_entry n z i * vector_entry n z j - (if Nat.eqb i j then 1 else 0)))
      : vector n -> R^o)
    (fun u : vector n => 0 + lambda *
      ((vector_entry n u i * vector_entry n x j + vector_entry n x i * vector_entry n u j) - 0)).
  { exact (is_diffD (is_diff_cst (matrix_entry n C i j : R^o) x)
      (is_diffZ lambda
        (is_diffB HP (is_diff_cst ((if Nat.eqb i j then 1 else 0) : R^o) x)))). }
  apply: (is_diff_eq HD).
  apply: funext => u.
  change (0 + lambda *
      ((vector_entry n u i * vector_entry n x j + vector_entry n x i * vector_entry n u j) - 0) =
    lambda * (vector_entry n u i * vector_entry n x j + vector_entry n x i * vector_entry n u j)).
  ring.
Qed.

Theorem quadratic_first_frechet n lambda (x u : vector n) :
  is_diff x (fun z => quadratic_first n lambda z u) (quadratic_second n lambda u).
Proof.
  unfold quadratic_first, quadratic_second.
  apply matrix_build_frechet; intros i j Hi Hj.
  have HP1 := quadratic_mult_frechet
    (fun _ : vector n => vector_entry n u i) (fun z : vector n => vector_entry n z j) x
    (fun _ : vector n => 0) (fun v : vector n => vector_entry n v j)
    (is_diff_cst (vector_entry n u i : R^o) x) (quadratic_vector_entry_frechet n j x).
  have HP2 := quadratic_mult_frechet
    (fun z : vector n => vector_entry n z i) (fun _ : vector n => vector_entry n u j) x
    (fun v : vector n => vector_entry n v i) (fun _ : vector n => 0)
    (quadratic_vector_entry_frechet n i x) (is_diff_cst (vector_entry n u j : R^o) x).
  have HD : is_diff x
    ((fun z : vector n => lambda *
      (vector_entry n u i * vector_entry n z j + vector_entry n z i * vector_entry n u j))
      : vector n -> R^o)
    (fun v : vector n => lambda *
      ((0 * vector_entry n x j + vector_entry n u i * vector_entry n v j) +
       (vector_entry n v i * vector_entry n u j + vector_entry n x i * 0))).
  { exact (is_diffZ lambda (is_diffD HP1 HP2)). }
  apply: (is_diff_eq HD).
  apply: funext => v.
  change (lambda * ((0 * vector_entry n x j + vector_entry n u i * vector_entry n v j) +
      (vector_entry n v i * vector_entry n u j + vector_entry n x i * 0)) =
    lambda * (vector_entry n u i * vector_entry n v j + vector_entry n v i * vector_entry n u j)).
  ring.
Qed.

Theorem quadratic_first_basis n lambda (x : vector n) a :
  quadratic_first n lambda x (chaos_basis n a) = matrix_scale n lambda (chaos_first n x a).
Proof.
  apply matrix_ext; intros i j Hi Hj; unfold quadratic_first, chaos_first.
  rewrite matrix_entry_scale matrix_entry_add.
  unfold vector_outer; rewrite !matrix_entry_build //.
Qed.

Theorem quadratic_second_basis n lambda a b :
  quadratic_second n lambda (chaos_basis n a) (chaos_basis n b) =
  matrix_scale n lambda (chaos_second n a b).
Proof.
  apply matrix_ext; intros i j Hi Hj; unfold quadratic_second, chaos_second.
  rewrite matrix_entry_scale matrix_entry_add.
  unfold vector_outer; rewrite !matrix_entry_build //.
Qed.

Theorem quadratic_trace_product_frechet {E : normedModType R}
    n (F dF G dG : E -> matrix n) (x : E) :
  is_diff x F dF -> is_diff x G dG ->
  is_diff x ((fun z => trace_pair n (F z) (G z)) : E -> R^o)
    (fun u => trace_pair n (dF u) (G x) + trace_pair n (F x) (dG u)).
Proof.
  intros HF HG; unfold trace_pair.
  have HS : is_diff x
    ((fun z => coordinate_sum n (fun i => coordinate_sum n (fun j =>
      matrix_entry n (F z) i j * matrix_entry n (G z) j i))) : E -> R^o)
    (fun u => coordinate_sum n (fun i => coordinate_sum n (fun j =>
      matrix_entry n (dF u) i j * matrix_entry n (G x) j i +
      matrix_entry n (F x) i j * matrix_entry n (dG u) j i))).
  { apply quadratic_coordinate_sum_frechet; intros i Hi.
    apply quadratic_coordinate_sum_frechet; intros j Hj.
    apply (quadratic_mult_frechet (fun z : E => matrix_entry n (F z) i j)
      (fun z : E => matrix_entry n (G z) j i) x
      (fun u : E => matrix_entry n (dF u) i j) (fun u : E => matrix_entry n (dG u) j i)).
    - exact (is_diff_comp HF (matrix_entry_frechet n (F x) i j)).
    - exact (is_diff_comp HG (matrix_entry_frechet n (G x) j i)). }
  apply: (is_diff_eq HS).
  apply: funext => u.
  change (coordinate_sum n (fun i => coordinate_sum n (fun j =>
      matrix_entry n (dF u) i j * matrix_entry n (G x) j i +
      matrix_entry n (F x) i j * matrix_entry n (dG u) j i)) =
    coordinate_sum n (fun i => coordinate_sum n (fun j =>
      matrix_entry n (dF u) i j * matrix_entry n (G x) j i)) +
    coordinate_sum n (fun i => coordinate_sum n (fun j =>
      matrix_entry n (F x) i j * matrix_entry n (dG u) j i))).
  transitivity (coordinate_sum n (fun i =>
    coordinate_sum n (fun j => matrix_entry n (dF u) i j * matrix_entry n (G x) j i) +
    coordinate_sum n (fun j => matrix_entry n (F x) i j * matrix_entry n (dG u) j i))).
  - apply coordinate_sum_ext; intros; apply quadratic_coordinate_sum_add.
  - apply quadratic_coordinate_sum_add.
Qed.

Theorem quadratic_hessian_product_frechet {E : normedModType R}
    n (F dF : E -> hessian_array n) (G dG : E -> matrix n) (x : E) :
  is_diff x F dF -> is_diff x G dG ->
  is_diff x (fun z => hessian_action n (F z) (G z))
    (fun u => matrix_add n (hessian_action n (dF u) (G x)) (hessian_action n (F x) (dG u))).
Proof.
  intros HF HG; unfold hessian_action.
  have HB : is_diff x
    (fun z => matrix_build n (fun i j => trace_pair n (hessian_entry n (F z) i j) (G z)))
    (fun u => matrix_build n (fun i j =>
      trace_pair n (hessian_entry n (dF u) i j) (G x) +
      trace_pair n (hessian_entry n (F x) i j) (dG u))).
  { apply matrix_build_frechet; intros i j Hi Hj.
    apply (quadratic_trace_product_frechet n
      (fun z => hessian_entry n (F z) i j) (fun u => hessian_entry n (dF u) i j) G dG x);
      [|exact HG].
    exact (is_diff_comp HF
      (matrix_linear_is_diff (fun H : hessian_array n => hessian_entry n H i j) (F x)
        (hessian_entry_linear n i j))). }
  apply: (is_diff_eq HB).
  apply: funext => u; apply matrix_ext; intros i j Hi Hj.
  rewrite matrix_entry_add !matrix_entry_build //.
Qed.
