(* Replicated Gibbs averages, for the comparison of translated losses.

   paper_main_loss_replica c f I k F is the average of F over k independent
   replicas s_1, ..., s_k, each with the Gibbs weights of
   gibbs_average c f I. For a product F = u(s_1) ... u(s_k)
   (paper_main_loss_product) it is the k-th power of the Gibbs average of u
   (paper_main_loss_replica_power), and every bound on |F| bounds it
   (paper_main_loss_replica_bound).
   paper_main_loss_row_poly beta f I n ell is the truncated series
   sum_(j = 1..n) (1 - Z)^j / j of -ln Z, where Z is the Gibbs average of
   exp(-beta ell) (paper_main_gibbs_row_factor). Each new term is a replica
   average (paper_main_loss_row_poly_step). paper_main_loss_row_poly_uniform:
   for losses 0 <= ell <= 1, the increment soft_min(f + ell) - soft_min(f)
   of the soft minimum is within eps of paper_main_loss_row_poly / beta for
   every large n, uniformly in f, I and ell. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GibbsDefinitions GibbsWeights GibbsMomentBounds
  PaperMainLossLogPolynomial PaperMainLossGibbs.
Open Scope R_scope.

Fixpoint paper_main_loss_replica c f I (k : nat) (F : list nat -> R) : R :=
  match k with O => F nil | S j => gibbs_average c f I
    (fun s => paper_main_loss_replica c f I j (fun xs => F (s :: xs))) end.
Fixpoint paper_main_loss_product (u : nat -> R) (xs : list nat) : R :=
  match xs with nil => 1 | s :: ys => u s * paper_main_loss_product u ys end.

Lemma paper_main_loss_replica_ext c f I k F G :
  (forall xs, F xs = G xs) ->
  paper_main_loss_replica c f I k F = paper_main_loss_replica c f I k G.
Proof.
revert F G; induction k; intros F G HE; simpl; [apply HE|].
apply gibbs_average_ext; intros s Hs; apply IHk; intro xs; apply HE.
Qed.

Lemma paper_main_loss_replica_scale c f I k a F :
  paper_main_loss_replica c f I k (fun xs => a*F xs) =
    a*paper_main_loss_replica c f I k F.
Proof.
revert F; induction k; intro F; simpl; [reflexivity|].
transitivity (gibbs_average c f I
  (fun s => a*paper_main_loss_replica c f I k (fun xs => F(s::xs)))).
- apply gibbs_average_ext; intros s Hs; apply IHk.
- apply gibbs_average_scale.
Qed.

Lemma paper_main_loss_replica_power c f I k u :
  paper_main_loss_replica c f I k (paper_main_loss_product u) =
    (gibbs_average c f I u)^k.
Proof.
induction k; simpl; [reflexivity|].
transitivity (gibbs_average c f I (fun s =>
  (gibbs_average c f I u)^k * u s)).
- apply gibbs_average_ext; intros s Hs.
  rewrite paper_main_loss_replica_scale, IHk; ring.
- rewrite gibbs_average_scale; ring.
Qed.

Lemma paper_main_loss_replica_bound c f I k F K :
  I <> nil ->
  (forall xs, length xs = k -> List.Forall (fun s => In s I) xs -> Rabs(F xs) <= K) ->
  Rabs(paper_main_loss_replica c f I k F) <= K.
Proof.
intros HI; revert F; induction k; intros F HF; simpl.
- apply HF; [reflexivity|constructor].
- apply gibbs_mean_uniform_bound; [exact HI|].
  intros s Hs; apply IHk; intros xs Hlen Hxs.
  apply HF; [simpl; now rewrite Hlen|constructor; assumption].
Qed.

Definition paper_main_loss_row_poly beta f I n ell :=
  paper_main_loss_log_poly n (1-paper_main_gibbs_row_factor beta f I ell).

Lemma paper_main_loss_row_poly_step beta f I n ell : I <> nil ->
  paper_main_loss_row_poly beta f I (S n) ell =
    paper_main_loss_row_poly beta f I n ell +
    paper_main_loss_replica (-beta) f I (S n)
      (paper_main_loss_product (fun s => 1-exp(-beta*ell s))) / INR(S n).
Proof.
intro HI; unfold paper_main_loss_row_poly; simpl paper_main_loss_log_poly.
rewrite paper_main_loss_replica_power.
assert (HE : gibbs_average (-beta) f I (fun s => 1-exp(-beta*ell s)) =
  1-paper_main_gibbs_row_factor beta f I ell).
{ unfold paper_main_gibbs_row_factor.
  transitivity (gibbs_average (-beta) f I (fun s => 1+(-1)*exp(-beta*ell s))).
  - apply gibbs_average_ext; intros s Hs; ring.
  - rewrite gibbs_average_add, gibbs_average_scale, (gibbs_average_const (-beta) f I 1 HI); ring. }
rewrite HE; reflexivity.
Qed.

Theorem paper_main_loss_row_poly_uniform beta eps : 0 < beta -> 0 < eps ->
  exists N, forall n, (N <= n)%nat -> forall f I ell,
    I <> nil -> (forall s, In s I -> 0 <= ell s <= 1) ->
    Rabs(soft_min beta (fun s => f s+ell s) I-soft_min beta f I -
      paper_main_loss_row_poly beta f I n ell/beta) < eps.
Proof.
intros Hb He.
assert (HA : 0 < exp(-beta) <= 1).
{ split; [apply exp_pos|rewrite <- exp_0; apply exp_monotone; lra]. }
destruct (paper_main_loss_log_factor_uniform (exp(-beta)) (beta*eps)
  HA ltac:(nra)) as [N HN].
exists N; intros n Hn f I ell HI Hell.
pose proof (paper_main_gibbs_row_bounds beta f I ell ltac:(lra) HI Hell) as Hbounds.
pose proof (HN n Hn (paper_main_gibbs_row_factor beta f I ell) Hbounds) as HH.
rewrite (paper_main_gibbs_row_increment beta f I ell Hb HI Hell).
unfold paper_main_loss_row_poly.
replace (-Rpower.ln(paper_main_gibbs_row_factor beta f I ell)/beta-
  paper_main_loss_log_poly n (1-paper_main_gibbs_row_factor beta f I ell)/beta)
  with ((-Rpower.ln(paper_main_gibbs_row_factor beta f I ell)-
  paper_main_loss_log_poly n (1-paper_main_gibbs_row_factor beta f I ell))*/beta) by (unfold Rdiv; ring).
rewrite Rabs_mult, (Rabs_pos_eq (/beta) ltac:(apply Rlt_le,Rinv_0_lt_compat; exact Hb)).
apply (Rmult_lt_reg_r beta); [exact Hb|].
replace (Rabs(-Rpower.ln(paper_main_gibbs_row_factor beta f I ell)-
  paper_main_loss_log_poly n (1-paper_main_gibbs_row_factor beta f I ell))*/beta*beta)
  with (Rabs(-Rpower.ln(paper_main_gibbs_row_factor beta f I ell)-
  paper_main_loss_log_poly n (1-paper_main_gibbs_row_factor beta f I ell))) by (field; lra).
nra.
Qed.
