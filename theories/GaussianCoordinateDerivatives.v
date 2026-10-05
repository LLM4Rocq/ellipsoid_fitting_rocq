From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinateDerivativeDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianCoordinateDerivatives.v from Coquelicot to
   MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the
   same order. Three kinds of change of text are made, and nothing else.

   1. finite_coordinate_derivative_last. Coquelicot's
        is_derive (fun u => F (xs++[u])) t (DF (xs++[t]))
      is written
        @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list),
      MathComp's derivative at the point t in the direction 1, on R with
      its own normed module structure R^o. Both are the ordinary
      derivative of a function R -> R, each being equivalent to Stdlib's
      derivable_pt_lim (Coquelicot's is_derive_Reals, and is_derive_Reals
      of AnalysisBridge), so the meaning is unchanged. This is the form of
      the vocabulary table of build/agent2/PORT-GUIDE.md. The direction 1
      is Stdlib's 1, as in the lemmas of AnalysisBridge; the definition
      finite_coordinate_derivative writes MathComp's 1%R, and the two are
      convertible, so exact and apply pass between both forms. The binders
      xs and t are annotated with list R and R, so that the statement does
      not mention R^o outside the derivative.

   2. finite_coordinate_derivative_swap_right. The hypothesis
      (S i < d)%nat is written (S i < d)%coq_nat. With ssreflect loaded,
      %nat would denote ssrnat's boolean ltn; %coq_nat is Peano's lt, the
      relation the original meant and the one the lemmas of
      GaussianCoordinatePermutations take.

   3. Concatenation. With ssreflect loaded, xs ++ [t] means MathComp's
      cat, while the original means Stdlib's app. The statements write
      (xs ++ [t])%list, which is app, as in the original and as in the
      ported GaussianLastDefinitions. The ports of TensorBounds and
      TensorResults follow the same convention. Likewise nth is written
      List.nth, because the bare name is MathComp's seq.nth, whose
      arguments are in another order. length and S are unchanged.

   replace_coordinate_last and finite_coordinate_derivative_times_other
   change only in these spellings.

   Proofs. The Stdlib tactic scripts are kept. Coquelicot's is_derive_ext
   and is_derive_scal are replaced by the lemmas of the same names in
   AnalysisBridge, which have the same shapes. The comma forms of rewrite
   and the "by" side conditions are spelled out, as ssreflect's rewrite
   accepts neither. *)

Lemma replace_coordinate_last xs t u :
  replace_coordinate (length xs) u (xs++[t])%list = (xs++[u])%list.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  simpl; rewrite IH; reflexivity.
Qed.

Lemma finite_coordinate_derivative_last d F DF :
  finite_coordinate_derivative (S d) d F DF ->
  forall xs : list R, length xs = d -> forall t : R,
  @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list).
Proof.
  intros HD xs Hxs t.
  pose proof (HD (xs++[t])%list ltac:(rewrite length_app; rewrite Hxs; simpl; lia)) as H.
  rewrite <- Hxs in H; rewrite nth_middle in H.
  change (@is_derive R R^o R^o t 1
    (fun u : R => F (replace_coordinate (length xs) u (xs++[t])%list)) (DF (xs++[t])%list)) in H.
  assert (He : (fun u => F (replace_coordinate (length xs) u (xs++[t])%list)) =
    (fun u => F (xs++[u])%list)).
  { apply functional_extensionality; intro u; rewrite replace_coordinate_last; reflexivity. }
  rewrite He in H; exact H.
Qed.

Lemma finite_coordinate_derivative_swap_right d i F DF :
  (S i < d)%coq_nat -> finite_coordinate_derivative d i F DF ->
  finite_coordinate_derivative d (S i)
    (fun xs => F (swap_adjacent i xs)) (fun xs => DF (swap_adjacent i xs)).
Proof.
  intros Hi HD xs Hxs.
  pose proof (HD (swap_adjacent i xs) ltac:(rewrite swap_adjacent_length; exact Hxs)) as H.
  rewrite (swap_adjacent_nth_left i xs ltac:(lia)) in H.
  apply is_derive_ext with (f := fun t => F (replace_coordinate i t (swap_adjacent i xs))).
  - intro t; rewrite (swap_adjacent_replace_right i t xs ltac:(lia)); reflexivity.
  - exact H.
Qed.

Lemma finite_coordinate_derivative_times_other d i j F DF :
  i <> j -> finite_coordinate_derivative d i F DF ->
  finite_coordinate_derivative d i
    (fun xs => List.nth j xs 0 * F xs) (fun xs => List.nth j xs 0 * DF xs).
Proof.
  intros Hij HD xs Hxs.
  apply is_derive_ext with (f := fun t => List.nth j xs 0 * F (replace_coordinate i t xs)).
  - intro t; rewrite (replace_coordinate_nth_other i j t xs Hij); reflexivity.
  - apply is_derive_scal; exact (HD xs Hxs).
Qed.
