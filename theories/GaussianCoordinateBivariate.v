From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianCoordinateBivariate.v from Coquelicot to
   MathComp-Analysis.

   Both lemmas of the original, finite_joint_continuous_two_iff and
   finite_joint_continuous_two_section, keep their names, their arguments
   and their statements word for word. Only the meaning of one name in them
   changes. continuity_2d_pt is no longer Coquelicot's epsilon-delta
   definition but the definition of the same name in
   AnalysisIntegralDefinitions: continuity at (x, y) of p |-> f p.1 p.2 for
   the product topology of R * R. The two say the same thing, because the
   open squares centred at (x, y) are the balls of MathComp's product
   distance on R * R and form a base of its neighbourhoods. The helper
   lemma coordinate_bivariate_continuity_2d_pt_Reals below states that
   equivalence in Coquelicot's epsilon-delta form, without posreal.

   finite_joint_continuous, Tn and close_n are those of the port of
   GaussianCoordinateDefinitions, which are copies of the originals, so the
   left-hand side of finite_joint_continuous_two_iff is unchanged.

   The proofs are the original ones, with the helper lemma inserted where
   Coquelicot's definition of continuity_2d_pt was unfolded. *)

(* The port's continuity_2d_pt in Coquelicot's epsilon-delta form. *)
Lemma coordinate_bivariate_continuity_2d_pt_Reals (f : R -> R -> R) x y :
  continuity_2d_pt f x y <->
  (forall eps, 0 < eps -> exists delta, 0 < delta /\
     forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta ->
       Rabs (f u v - f x y) < eps).
Proof.
rewrite /continuity_2d_pt /prop_for /continuous_at; split.
- move=> /cvg_ballP H eps eps0.
  have eps0' : (0 < eps)%R by apply/RltP.
  have := H eps eps0'.
  move=> /nbhs_ballP [d d0 Hd].
  exists d; split; first by apply/RltP.
  move=> u v Hu Hv.
  have := Hd (u, v).
  rewrite /ball /= => Hb.
  have Hfin : (`|f x y - f u v| < eps)%R.
    apply: Hb; rewrite /prod_ball /=; split; rewrite /ball /=; apply/RltP;
      rewrite -RabsE -RminusE Rabs_minus_sym; assumption.
  by move/RltP: Hfin; rewrite -RabsE -RminusE Rabs_minus_sym.
- move=> Hc.
  have key : forall eps : R, (0 < eps)%R ->
      nbhs (x, y) (fun p : R * R => ball (f x y) eps (f p.1 p.2)).
    move=> eps eps0.
    apply/nbhs_ballP.
    have eps0' : 0 < eps by apply/RltP.
    have [d [d0 Hd]] := Hc eps eps0'.
    have d0' : (0 < d)%R by apply/RltP.
    exists d => // -[u v].
    rewrite /ball /= /prod_ball /= => -[Hu Hv].
    apply/RltP; rewrite -RabsE -RminusE Rabs_minus_sym.
    apply: Hd.
    + by move/RltP: Hu; rewrite -RabsE -RminusE Rabs_minus_sym.
    + by move/RltP: Hv; rewrite -RabsE -RminusE Rabs_minus_sym.
  by apply/cvg_ballP => eps eps0; exact: key.
Qed.

Lemma finite_joint_continuous_two_iff F :
  finite_joint_continuous 2 F <->
  forall x y, continuity_2d_pt (fun u v => F [u; v]) x y.
Proof.
  split.
  - intros HF x y.
    apply (coordinate_bivariate_continuity_2d_pt_Reals (fun u v => F [u; v]) x y).
    intros eps eps0.
    destruct (HF (x, (y, tt)) (mkposreal eps eps0)) as [delta HD].
    exists delta; split; [apply cond_pos |].
    intros u v Hu Hv.
    apply (HD (u, (v, tt))); simpl; auto.
  - intros HF [x [y []]] eps.
    destruct (proj1 (coordinate_bivariate_continuity_2d_pt_Reals
                       (fun u v => F [u; v]) x y) (HF x y) eps (cond_pos eps))
      as [delta [d0 HD]].
    exists (mkposreal delta d0); intros [u [v []]] [Hu [Hv _]].
    exact (HD u v Hu Hv).
Qed.

Lemma finite_joint_continuous_two_section F :
  finite_joint_continuous 2 F ->
  forall x y, continuity_2d_pt (fun u v => F [u; v]) x y.
Proof. apply finite_joint_continuous_two_iff. Qed.
