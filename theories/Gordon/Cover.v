(* A finite-coordinate cover, obtained from compact real intervals. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From mathcomp Require Import finmap.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gordon_interval_cover delta :
  0 < delta -> exists centers : list R,
  forall x, -1 <= x <= 1 -> exists c, List.In c centers /\ Rabs (x-c) < delta.
Proof.
intros Hd.
have Hd' : (0 < delta)%R by apply/RltP.
have HC := @segment_compact _ (-1 : R)%R (1 : R)%R.
rewrite compact_cover in HC.
pose f := fun c : R => ball c delta.
have [D HD Hcover] := HC _ [set: R] f (fun c _ => @ball_open _ R^o c delta)
  ltac:(move=> x Hx; exists x; [exact I|apply ballxx; exact Hd']).
exists (enum_fset D); intros x [Hx0 Hx1].
have Hx : `[(-1)%R,1%R] x.
{ change ((-1 <= x <= 1)%R).
  apply/andP; split.
  - apply/RleP; rewrite <- RoppE; exact Hx0.
  - apply/RleP; exact Hx1. }
have [c Hc Hball] := Hcover x Hx.
exists c; split.
- have Hmem : c \in enum_fset D := Hc.
  move: Hmem; elim: (enum_fset D) => [|a cs IH] //=.
  rewrite in_cons => /orP[/eqP Hca|Hcs].
  + left; symmetry; exact Hca.
  + right; exact (IH Hcs).
- change (is_true (`|c - x| < delta)%R) in Hball.
  move: Hball; rewrite -RabsE -RminusE => /RltP H.
  rewrite Rabs_minus_sym; exact H.
Qed.
