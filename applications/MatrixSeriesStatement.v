From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals ereal exp.
From mathcomp Require Import measure lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import gauss.
From GaussianAnalysis.matrix Require Import opnorm.

(**md**************************************************************************)
(* # Gaussian matrix series: the statement                                    *)
(*                                                                            *)
(* Target T1 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of Lemma 4.2, 'A Gaussian matrix estimate', of    *)
(* 'Pointwise convergence of fourfold ergodic averages for mixing             *)
(* transformations' (family 154 of the OpenAI math collection, revision       *)
(* 1581d4cbd, sections/04-packing.tex), which is also a lemma of 'Pointwise   *)
(* multiple ergodic averages for mixing transformations' (the same family,    *)
(* sections/packing.tex). The collection has no Lean version of it. This file *)
(* holds the statement only.                                                  *)
(*                                                                            *)
(* Setting. R is any realType. g has law gauss r, the standard Gaussian       *)
(* measure on 'rV[R]_r (gaussian/gauss.v), and g 0 j is its coordinate j.     *)
(* Expectations are Lebesgue integrals against gauss r, of extended reals;    *)
(* the three integrands are nonnegative, so each bound also says that the     *)
(* integral is finite. opnorm is the operator norm of matrix/opnorm.v, \tr    *)
(* the trace of MathComp, and (2q - 1)!! = 1 * 3 * ... * (2q - 1) is written  *)
(* \prod_(i < q) i.*2.+1%:R, as in normal_moment_even.                        *)
(*                                                                            *)
(* matrix_series_statement, for every R:                                      *)
(*                                                                            *)
(* (a) the trace moments: for symmetric H_1, ..., H_r in 'M[R]_n, S = sum_j   *)
(* H_j^2 and H = sum_j g_j H_j, for every q >= 1, E tr H^(2q) <= (2q-1)!!     *)
(* opnorm(S)^(q-1) tr S;                                                      *)
(*                                                                            *)
(* (b) rectangular matrices: for B_1, ..., B_r in 'M[R]_(m, p) and every q >= *)
(* 1, E opnorm (sum_j g_j B_j) <= ((2q-1)!! sigma^(2(q-1)) tau)^(1/(2q)),     *)
(* with sigma^2 = max (opnorm (sum_j B_j B_j^T), opnorm (sum_j B_j^T B_j))    *)
(* and tau = 2 tr (sum_j B_j B_j^T), the root being powR;                     *)
(*                                                                            *)
(* (c) the manuscript's form: there is C > 0 such that for all m, p, r, B_1,  *)
(* ..., B_r and every real d >= 1 with sigma^2 <= sqrt d and tau <= 2 d, E    *)
(* opnorm (sum_j g_j B_j) <= C d^(1/4) sqrt (ln (2 + d)).                     *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - (b) and (c) are the bound of (a) for the symmetric dilations H_j = [[0,  *)
(*   B_j], [B_j^T, 0]] in 'M[R]_(m + p): H_j^2 is block diagonal with blocks  *)
(*   B_j B_j^T and B_j^T B_j, so opnorm S = sigma^2 and tr S = tau, and       *)
(*   opnorm (sum_j g_j H_j) = opnorm (sum_j g_j B_j). The statement is        *)
(*   written with B directly, without the dilation.                           *)
(*                                                                            *)
(* - The manuscript states (c) under its hypotheses opnorm S <= sqrt d and tr *)
(*   S <= 2 d, which are sigma^2 <= sqrt d and tau <= 2 d. Its constant is    *)
(*   universal; here C is a real of each realType R and does not depend on m, *)
(*   p, r, B or d. No ambient dimension appears in any bound.                 *)
(*                                                                            *)
(* - The manuscript proves the recursion of (a) for q >= 2 and starts from E  *)
(*   tr H^2 = tr S; (a) includes q = 1, where it is that equality.            *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition matrix_series_statement : Prop :=
  forall R : realType,
  [/\ forall (n r : nat) (H : 'I_r -> 'M[R]_n) (q : nat),
        (forall j, H j \is symmetricmx) -> (0 < q)%N ->
        (\int[gauss r]_g (\tr ((\sum_(j < r) g 0 j *: H j) ^+ q.*2))%:E <=
          ((\prod_(i < q) i.*2.+1%:R) *
           opnorm (\sum_(j < r) H j *m H j) ^+ q.-1 *
           \tr (\sum_(j < r) H j *m H j))%:E)%E,
      forall (m p r : nat) (B : 'I_r -> 'M[R]_(m, p)) (q : nat), (0 < q)%N ->
        (\int[gauss r]_g (opnorm (\sum_(j < r) g 0 j *: B j))%:E <=
          (((\prod_(i < q) i.*2.+1%:R) *
            Num.max (opnorm (\sum_(j < r) B j *m (B j)^T))
                    (opnorm (\sum_(j < r) (B j)^T *m B j)) ^+ q.-1 *
            (2 * \tr (\sum_(j < r) B j *m (B j)^T))) `^ (q.*2%:R)^-1)%:E)%E &
      exists C : R, 0 < C /\
      forall (m p r : nat) (B : 'I_r -> 'M[R]_(m, p)) (d : R), 1 <= d ->
        Num.max (opnorm (\sum_(j < r) B j *m (B j)^T))
                (opnorm (\sum_(j < r) (B j)^T *m B j)) <= Num.sqrt d ->
        2 * \tr (\sum_(j < r) B j *m (B j)^T) <= 2 * d ->
        (\int[gauss r]_g (opnorm (\sum_(j < r) g 0 j *: B j))%:E <=
          (C * Num.sqrt (Num.sqrt d) * Num.sqrt (ln (2 + d)))%:E)%E].
