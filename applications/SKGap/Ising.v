From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions interval reals topology normedtype.
From mathcomp Require Import sequences derive realfun exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianApplications Require Import SKGapDefinitions.

(**md**************************************************************************)
(* # The Ising law on the cube and its conditional expectations               *)
(*                                                                            *)
(* Part of target T4 of phase 12 (AGENTS.md, section Phase 12), the spectral  *)
(* gap of the heat-bath dynamics of the Sherrington-Kirkpatrick model for     *)
(* beta < 1/2. A Rocq formalization of the credited argument of 'Cutoff       *)
(* throughout the high-temperature Sherrington-Kirkpatrick phase' (family 227 *)
(* of the OpenAI math collection, revision 1581d4cbd, appendices/entropy.tex, *)
(* subsection 'A two-spin estimate and a uniform gap'). The objects are those *)
(* of the frozen applications/SKGapDefinitions.v.                             *)
(*                                                                            *)
(* - Spin flips: spin_set and its algebra, the involution spin_flip,          *)
(*   sum_pair2 (a sum over the cube is half the sum over the pairs x^(i,+),   *)
(*   x^(i,-)), and cube_const (a function invariant under every spin_set is   *)
(*   constant).                                                               *)
(* - sk_tanh and sk_cosh, with expR_spin: exp (b u) = cosh u (1 + b tanh u)   *)
(*   for a spin b, and, by monotonicity (MathComp-Analysis                    *)
(*   ger0_derive1_ndecry), |tanh u| <= |u| and |tanh u - u| <= |u|^3          *)
(*   (sk_tanh_norm_le, sk_tanh_sub_le).                                       *)
(* - For a matrix A and a field theta: the weights are positive and the       *)
(*   masses sum to one; ising_mean is linear and monotone; the conditional    *)
(*   expectation ising_cexp i given the spins outside i and the projection    *)
(*   ising_dproj i = I - E_i satisfy D_i f = (x_i - m_i) d_i f                *)
(*   (ising_dproj_eq), nu[(D_i f)^2] = nu[v_i (d_i f)^2] (ising_energy) and   *)
(*   nu[g D_i f] = nu[D_i g D_i f] (ising_dproj_adj). The Dirichlet form is   *)
(*   the sum of the energies, and it vanishes only on constants               *)
(*   (ising_dirichlet_eq0). ising_gen f = sum_i D_i f is minus the generator  *)
(*   of the heat-bath dynamics with rate one at every site.                   *)
(* - ising_weight_block: for A symmetric with zero diagonal and i != j, the   *)
(*   weights of the four configurations of the spins i and j with the other   *)
(*   spins fixed are K (1 + a x)(1 + b y)(1 + t x y), with K > 0, |a|, |b| <  *)
(*   1 and t = tanh A_ij: the pair law of the manuscript.                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Arguments spin {R} b.
Arguments spin_vec {R n} x.

Section spin_flip.
Variable n : nat.
Implicit Types (x : {ffun 'I_n -> bool}) (i j : 'I_n) (b c : bool).

Lemma spin_setE x i b j : spin_set x i b j = if j == i then b else x j.
Proof. by rewrite ffunE. Qed.

Lemma spin_set_id x i : spin_set x i (x i) = x.
Proof. by apply/ffunP => j; rewrite ffunE; case: eqP => // ->. Qed.

Lemma spin_set_val x i b : x i = b -> spin_set x i b = x.
Proof. by move=> <-; exact: spin_set_id. Qed.

Lemma spin_setK x i b c : spin_set (spin_set x i b) i c = spin_set x i c.
Proof. by apply/ffunP => j; rewrite !ffunE; case: eqP. Qed.

Lemma spin_set_same x i b : spin_set x i b i = b.
Proof. by rewrite ffunE eqxx. Qed.

Lemma spin_set_other x i j b : j != i -> spin_set x i b j = x j.
Proof. by rewrite ffunE => /negbTE ->. Qed.

Lemma spin_setC x i j b c : i != j ->
  spin_set (spin_set x i b) j c = spin_set (spin_set x j c) i b.
Proof.
move=> ij; apply/ffunP => k; rewrite !ffunE.
have [kj|kj] := eqVneq k j; have [ki|ki] := eqVneq k i => //.
by move: ij; rewrite -ki -kj eqxx.
Qed.

Definition spin_flip x i := spin_set x i (~~ x i).

Lemma spin_flipK x i : spin_flip (spin_flip x i) i = x.
Proof. by rewrite /spin_flip spin_set_same negbK spin_setK spin_set_id. Qed.

Lemma sum_flip (V : nmodType) i (G : {ffun 'I_n -> bool} -> V) :
  \sum_x G x = \sum_x G (spin_flip x i).
Proof. exact: (reindex_inj (inv_inj (spin_flipK ^~ i))). Qed.

Lemma sum_pair2 (R : ringType) i (G : {ffun 'I_n -> bool} -> R) :
  \sum_x (G (spin_set x i true) + G (spin_set x i false)) = 2 * \sum_x G x.
Proof.
rewrite mulr_natl mulr2n {2}(sum_flip i G) -big_split /=.
apply: eq_bigr => x _; rewrite /spin_flip.
by case Ex: (x i); rewrite (spin_set_val Ex) //= addrC.
Qed.

Lemma cube_const (T : Type) (f : {ffun 'I_n -> bool} -> T) :
  (forall x i b, f (spin_set x i b) = f x) -> forall x y, f x = f y.
Proof.
move=> h x y.
pose z k := [ffun j : 'I_n => if (j < k)%N then y j else x j].
have z0 : z 0 = x by apply/ffunP => j; rewrite ffunE.
have zn : z n = y by apply/ffunP => j; rewrite ffunE ltn_ord.
suff H : forall k, (k <= n)%N -> f x = f (z k) by rewrite -zn; exact: H.
elim => [|k IH] kn; first by rewrite z0.
rewrite (IH (ltnW kn)).
have -> : z k.+1 = spin_set (z k) (Ordinal kn) (y (Ordinal kn)).
  rewrite /z; apply/ffunP => j; rewrite !ffunE ltnS leq_eqVlt.
  have [->|jk] := eqVneq j (Ordinal kn); first by rewrite /= eqxx.
  have /negbTE -> : (j : nat) != k.
    by apply: contra jk => /eqP jk'; apply/eqP/val_inj.
  by [].
by rewrite h.
Qed.

End spin_flip.

Section spin_values.
Variable R : realType.

Lemma spin_sqr b : spin b ^+ 2 = 1 :> R.
Proof. by case: b; rewrite /spin ?sqrrN expr1n. Qed.

Lemma spin_norm b : `|spin b| = 1 :> R.
Proof. by case: b; rewrite /spin ?normrN normr1. Qed.

Lemma spin_mul b c : spin b * spin c = spin (b == c) :> R.
Proof. by case: b; case: c; rewrite /spin /= ?mulr1 ?mulrN1 ?opprK. Qed.

End spin_values.

Section sk_tanh.
Local Open Scope classical_set_scope.
Variable R : realType.
Implicit Types u : R.

Definition sk_cosh u : R := (expR u + expR (- u)) / 2.

Definition sk_tanh u : R := (expR u - expR (- u)) / (expR u + expR (- u)).

Lemma sk_cosh_den u : 0 < expR u + expR (- u).
Proof. by rewrite addr_gt0 ?expR_gt0. Qed.

Lemma sk_cosh_gt0 u : 0 < sk_cosh u.
Proof. by apply: divr_gt0; [exact: sk_cosh_den | lra]. Qed.

Lemma sk_tanh_lt1 u : `|sk_tanh u| < 1.
Proof.
have e1 := expR_gt0 u; have e2 := expR_gt0 (- u); have d := sk_cosh_den u.
rewrite /sk_tanh normf_div (gtr0_norm d) ltr_pdivrMr // mul1r ltr_norml.
by apply/andP; split; lra.
Qed.

Lemma sk_tanh0 : sk_tanh 0 = 0.
Proof. by rewrite /sk_tanh oppr0 subrr mul0r. Qed.

Lemma sk_tanhN u : sk_tanh (- u) = - sk_tanh u.
Proof.
have d1 : expR u + expR (- u) != 0 by rewrite gt_eqF ?sk_cosh_den.
have d2 : expR (- u) + expR u != 0 by rewrite addrC.
by rewrite /sk_tanh opprK; field.
Qed.

Lemma expR_spin u b : expR (spin b * u) = sk_cosh u * (1 + spin b * sk_tanh u).
Proof.
have d := sk_cosh_den u; have d0 : expR u + expR (- u) != 0 by rewrite gt_eqF.
by case: b; rewrite /spin /sk_cosh /sk_tanh ?mul1r ?mulN1r; field.
Qed.

Lemma is_derive_expRN' (z : R) :
  is_derive z 1 (fun z : R => expR (- z)) (- expR (- z)).
Proof.
have dneg : is_derive z 1 (fun z : R => - z) (-1).
  by apply: is_deriveN; exact: is_derive_id.
have := @is_derive1_comp R expR (fun z : R => - z) z _ _ (is_derive_expR (- z)) dneg.
by rewrite mulrN1.
Qed.

(* sinh z <= z cosh z for z >= 0, by monotonicity. *)
Lemma sinh_le_mul_cosh u : 0 <= u ->
  expR u - expR (- u) <= u * (expR u + expR (- u)).
Proof.
move=> u0.
pose h (z : R) := z * (expR z + expR (- z)) - (expR z - expR (- z)).
have dh (z : R) : is_derive z 1 h (z * (expR z - expR (- z))).
  have dC := is_deriveD (is_derive_expR z) (is_derive_expRN' z).
  have dS := is_deriveB (is_derive_expR z) (is_derive_expRN' z).
  have := is_deriveB (is_deriveM (is_derive_id z (1 : R)) dC) dS.
  rewrite /GRing.scale /= => H; apply: (is_derive_eq H).
  by rewrite !fctE opprK; ring.
have dv (x : R) : derivable h x 1 by case: (dh x).
have hc : continuous h.
  by move=> x; apply: differentiable_continuous; apply/derivable1_diffP; exact: dv.
have hd x : x \in `]0, +oo[%R -> 0 <= h^`() x.
  rewrite in_itv /= andbT => x0.
  rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dh x)).
  apply: mulr_ge0; first exact: ltW.
  by rewrite subr_ge0 ler_expR; lra.
have h0 : h 0 = 0 by rewrite /h oppr0 expR0; ring.
have := @ger0_derive1_ndecry R h 0 (fun x _ => dv x) hd (continuous_subspaceT hc) 0 u
  (lexx 0) u0.
by rewrite h0 /h subr_ge0.
Qed.

Lemma sk_tanh_ge0 u : 0 <= u -> 0 <= sk_tanh u.
Proof.
move=> u0; apply: divr_ge0; last exact/ltW/sk_cosh_den.
by rewrite subr_ge0 ler_expR; lra.
Qed.

Lemma sk_tanh_le u : 0 <= u -> sk_tanh u <= u.
Proof.
move=> u0; have C0 := sk_cosh_den u.
rewrite /sk_tanh ler_pdivrMr //.
exact: sinh_le_mul_cosh.
Qed.

(* (u - u^3) cosh u <= sinh u for u >= 0, by monotonicity. *)
Lemma cubic_le_sinh u : 0 <= u ->
  (u - u ^+ 3) * (expR u + expR (- u)) <= expR u - expR (- u).
Proof.
move=> u0.
have e3 (z : R) : z ^+ 3 = z * (z * z) by rewrite !exprS expr0 mulr1.
pose g (z : R) := (expR z - expR (- z)) - (z - z * (z * z)) * (expR z + expR (- z)).
have dz3 (z : R) : is_derive z (1 : R) (fun z : R => z - z * (z * z)) (1 - 3 * (z * z)).
  have dzz := is_deriveM (is_derive_id z (1 : R)) (is_derive_id z (1 : R)).
  have := is_deriveB (is_derive_id z (1 : R)) (is_deriveM (is_derive_id z (1 : R)) dzz).
  rewrite /GRing.scale /= => H; apply: (is_derive_eq H).
  by rewrite ?fctE; ring.
have dg (z : R) : is_derive z 1 g
    (3 * (z * z) * (expR z + expR (- z)) - (z - z * (z * z)) * (expR z - expR (- z))).
  have dC := is_deriveD (is_derive_expR z) (is_derive_expRN' z).
  have dS := is_deriveB (is_derive_expR z) (is_derive_expRN' z).
  have := is_deriveB dS (is_deriveM (dz3 z) dC).
  rewrite /GRing.scale /= => H; apply: (is_derive_eq H).
  by rewrite !fctE !opprK; ring.
have dv (x : R) : derivable g x 1 by case: (dg x).
have gc : continuous g.
  by move=> x; apply: differentiable_continuous; apply/derivable1_diffP; exact: dv.
have hd x : x \in `]0, +oo[%R -> 0 <= g^`() x.
  rewrite in_itv /= andbT => x0.
  rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dg x)) subr_ge0.
  have hs := sinh_le_mul_cosh (ltW x0).
  have hS : 0 <= expR x - expR (- x) by rewrite subr_ge0 ler_expR; lra.
  have hC := ltW (sk_cosh_den x).
  have [x1|x1] := leP x 1.
    have hx : 0 <= x - x * (x * x) by have := sqr_ge0 x; nra.
    have h2 := ler_wpM2l hx hs.
    apply: le_trans h2 _.
    have -> : (x - x * (x * x)) * (x * (expR x + expR (- x))) =
        ((x - x * (x * x)) * x) * (expR x + expR (- x)) by ring.
    apply: ler_wpM2r => //.
    by have := sqr_ge0 x; nra.
  have hx : x - x * (x * x) <= 0 by have := sqr_ge0 x; nra.
  apply: (le_trans (y := 0)); first exact: mulr_le0_ge0 hx hS.
  apply: mulr_ge0 hC; apply: mulr_ge0; first lra.
  exact: mulr_ge0 (ltW x0) (ltW x0).
have g0 : g 0 = 0 by rewrite /g oppr0 expR0; ring.
have := @ger0_derive1_ndecry R g 0 (fun x _ => dv x) hd (continuous_subspaceT gc) 0 u
  (lexx 0) u0.
by rewrite g0 /g subr_ge0 e3.
Qed.

Lemma sk_tanh_cubic u : 0 <= u -> u - u ^+ 3 <= sk_tanh u.
Proof.
move=> u0; have C0 := sk_cosh_den u.
rewrite /sk_tanh ler_pdivlMr //.
exact: cubic_le_sinh.
Qed.

Lemma sk_tanh_norm_le u : `|sk_tanh u| <= `|u|.
Proof.
have [u0|u0] := leP 0 u.
  by rewrite (ger0_norm u0) (ger0_norm (sk_tanh_ge0 u0)) sk_tanh_le.
have nu0 : 0 <= - u by rewrite oppr_ge0 ltW.
have := sk_tanh_le nu0; have := sk_tanh_ge0 nu0; rewrite sk_tanhN => h1 h2.
have h3 : sk_tanh u <= 0 by lra.
by rewrite (ltr0_norm u0) (ler0_norm h3).
Qed.

Lemma sk_tanh_sub_le u : `|sk_tanh u - u| <= `|u| ^+ 3.
Proof.
have key v : 0 <= v -> `|sk_tanh v - v| <= v ^+ 3.
  move=> v0; have h1 := sk_tanh_le v0; have h2 := sk_tanh_cubic v0.
  have hn : sk_tanh v - v <= 0 by rewrite subr_le0.
  by rewrite (ler0_norm hn); lra.
have [u0|u0] := leP 0 u; first by rewrite (ger0_norm u0); exact: key.
have nu0 : 0 <= - u by rewrite oppr_ge0 ltW.
have := key _ nu0; rewrite sk_tanhN -opprD normrN (ltr0_norm u0).
done.
Qed.

End sk_tanh.

Section ising.
Variables (R : realType) (n : nat) (A : 'M[R]_n) (theta : 'cV[R]_n).
Local Notation cube := {ffun 'I_n -> bool}.
Local Notation w := (ising_weight A theta).
Local Notation nu := (ising_mass A theta).
Local Notation E := (ising_mean A theta).
Implicit Types (x : cube) (i j : 'I_n) (f g : cube -> R).

Lemma ising_weight_gt0 x : 0 < w x.
Proof. exact: expR_gt0. Qed.

Lemma ising_Z_gt0 : 0 < \sum_x w x.
Proof.
pose x0 : cube := [ffun => true].
apply: (lt_le_trans (ising_weight_gt0 x0)).
rewrite (bigD1 x0) //= lerDl sumr_ge0 // => y _.
exact/ltW/ising_weight_gt0.
Qed.

Lemma ising_mass_gt0 x : 0 < nu x.
Proof. by rewrite /ising_mass divr_gt0 ?ising_weight_gt0 ?ising_Z_gt0. Qed.

Lemma ising_mass_sum : \sum_x nu x = 1.
Proof. by rewrite /ising_mass -mulr_suml mulfV // lt0r_neq0 // ising_Z_gt0. Qed.

Lemma ising_meanE f : E f = (\sum_x w x * f x) / \sum_x w x.
Proof.
rewrite /ising_mean /ising_mass mulr_suml; apply: eq_bigr => x _.
by rewrite mulrAC.
Qed.

Lemma ising_mean_ext f g : f =1 g -> E f = E g.
Proof. by move=> fg; rewrite /ising_mean; apply: eq_bigr => x _; rewrite fg. Qed.

Lemma ising_meanD f g : E (fun x => f x + g x) = E f + E g.
Proof. by rewrite /ising_mean -big_split; apply: eq_bigr => x _; rewrite mulrDr. Qed.

Lemma ising_meanZ c f : E (fun x => c * f x) = c * E f.
Proof. by rewrite /ising_mean mulr_sumr; apply: eq_bigr => x _; rewrite mulrCA. Qed.

Lemma ising_meanN f : E (fun x => - f x) = - E f.
Proof.
rewrite -mulN1r -ising_meanZ /ising_mean; apply: eq_bigr => x _.
by rewrite mulN1r.
Qed.

Lemma ising_meanB f g : E (fun x => f x - g x) = E f - E g.
Proof. by rewrite ising_meanD ising_meanN. Qed.

Lemma ising_mean_cst c : E (fun _ => c) = c.
Proof. by rewrite /ising_mean -mulr_suml ising_mass_sum mul1r. Qed.

Lemma ising_mean_le f g : (forall x, f x <= g x) -> E f <= E g.
Proof.
move=> fg; rewrite /ising_mean ler_sum // => x _.
by rewrite ler_wpM2l // ltW // ising_mass_gt0.
Qed.

Lemma ising_mean_ge0 f : (forall x, 0 <= f x) -> 0 <= E f.
Proof.
move=> f0; rewrite -(ising_mean_cst 0); exact: ising_mean_le.
Qed.

Lemma ising_mean_sum (I : finType) (F : I -> cube -> R) :
  E (fun x => \sum_k F k x) = \sum_k E (F k).
Proof.
rewrite /ising_mean; under eq_bigr do rewrite mulr_sumr.
exact: exchange_big.
Qed.

Lemma ising_mean_eq0 f : (forall x, 0 <= f x) -> E f = 0 -> forall x, f x = 0.
Proof.
move=> f0 Ef x.
have h : forall y, true -> 0 <= nu y * f y.
  by move=> y _; rewrite mulr_ge0 // ltW // ising_mass_gt0.
have /eqP := psumr_eq0P h Ef (i := x) isT.
by rewrite mulf_eq0 (gt_eqF (ising_mass_gt0 x)) /= => /eqP.
Qed.

Lemma ising_mean_pair i f :
  E f = (\sum_x (w (spin_set x i true) * f (spin_set x i true) +
                 w (spin_set x i false) * f (spin_set x i false))) /
        2 / \sum_x w x.
Proof.
rewrite ising_meanE (sum_pair2 i (fun x => w x * f x)).
have Z0 : \sum_x w x != 0 := lt0r_neq0 ising_Z_gt0.
by field.
Qed.

Lemma ising_mean_pair_eq i f g :
  (forall x, w (spin_set x i true) * f (spin_set x i true) +
               w (spin_set x i false) * f (spin_set x i false) =
             w (spin_set x i true) * g (spin_set x i true) +
               w (spin_set x i false) * g (spin_set x i false)) ->
  E f = E g.
Proof.
move=> h; rewrite (ising_mean_pair i f) (ising_mean_pair i g).
by congr (_ / _ / _); apply: eq_bigr => x _; exact: h.
Qed.

(* The conditional expectation given the spins outside i, and the
   projection D_i = I - E_i. *)
Definition ising_cexp i f x : R :=
  (w (spin_set x i true) * f (spin_set x i true) +
   w (spin_set x i false) * f (spin_set x i false)) /
  (w (spin_set x i true) + w (spin_set x i false)).

Definition ising_dproj i f x : R := f x - ising_cexp i f x.

Definition ising_gen f x : R := \sum_i ising_dproj i f x.

Lemma ising_pair_den i x : 0 < w (spin_set x i true) + w (spin_set x i false).
Proof. by rewrite addr_gt0 ?ising_weight_gt0. Qed.

Lemma ising_cexp_set i f x b : ising_cexp i f (spin_set x i b) = ising_cexp i f x.
Proof. by rewrite /ising_cexp !spin_setK. Qed.

Lemma ising_cond_mean_set i x b :
  ising_cond_mean A theta i (spin_set x i b) = ising_cond_mean A theta i x.
Proof. by rewrite /ising_cond_mean !spin_setK. Qed.

Lemma ising_cond_var_set i x b :
  ising_cond_var A theta i (spin_set x i b) = ising_cond_var A theta i x.
Proof. by rewrite /ising_cond_var ising_cond_mean_set. Qed.

Lemma half_diff_set i f x b : half_diff i f (spin_set x i b) = half_diff i f x.
Proof. by rewrite /half_diff !spin_setK. Qed.

Lemma ising_cond_mean_lt1 i x : `|ising_cond_mean A theta i x| < 1.
Proof.
have hp := ising_weight_gt0 (spin_set x i true).
have hm := ising_weight_gt0 (spin_set x i false).
have d := ising_pair_den i x.
rewrite /ising_cond_mean normf_div (gtr0_norm d) ltr_pdivrMr // mul1r ltr_norml.
by apply/andP; split; lra.
Qed.

Lemma ising_cond_var_ge0 i x : 0 <= ising_cond_var A theta i x.
Proof.
have h1 := ltW (ising_cond_mean_lt1 i x).
rewrite /ising_cond_var subr_ge0 -real_normK ?num_real // expr2.
exact: mulr_ile1.
Qed.

Lemma ising_cond_var_le1 i x : ising_cond_var A theta i x <= 1.
Proof. by rewrite /ising_cond_var lerBlDr lerDl sqr_ge0. Qed.

Lemma ising_pair_val i (F : cube -> R) x : F x = F (spin_set x i (x i)).
Proof. by rewrite spin_set_id. Qed.

Lemma ising_dproj_eq i f x :
  ising_dproj i f x = (spin (x i) - ising_cond_mean A theta i x) * half_diff i f x.
Proof.
rewrite /ising_dproj /ising_cexp /ising_cond_mean /half_diff.
have d := ising_pair_den i x; have d0 := lt0r_neq0 d.
move: d0; rewrite [f x](ising_pair_val i).
by case: (x i) => d0; rewrite /spin; field.
Qed.

Lemma ising_energy i f :
  E (fun x => ising_dproj i f x ^+ 2) =
  E (fun x => ising_cond_var A theta i x * half_diff i f x ^+ 2).
Proof.
apply: (ising_mean_pair_eq (i := i)) => x /=.
rewrite /ising_dproj !ising_cexp_set !ising_cond_var_set !half_diff_set.
rewrite /ising_cexp /ising_cond_var /ising_cond_mean /half_diff ?spin_setK.
have d := ising_pair_den i x; have d0 := lt0r_neq0 d.
by field.
Qed.

Lemma ising_dproj_adj i f g :
  E (fun x => g x * ising_dproj i f x) =
  E (fun x => ising_dproj i g x * ising_dproj i f x).
Proof.
apply: (ising_mean_pair_eq (i := i)) => x /=.
rewrite /ising_dproj !ising_cexp_set /ising_cexp ?spin_setK.
have d := ising_pair_den i x; have d0 := lt0r_neq0 d.
by field.
Qed.

Lemma ising_dirichletE f :
  ising_dirichlet A theta f = \sum_i E (fun x => ising_dproj i f x ^+ 2).
Proof. by rewrite /ising_dirichlet; apply: eq_bigr => i _; rewrite ising_energy. Qed.

Lemma ising_dirichlet_ge0 f : 0 <= ising_dirichlet A theta f.
Proof.
rewrite ising_dirichletE sumr_ge0 // => i _.
by apply: ising_mean_ge0 => x; exact: sqr_ge0.
Qed.

Lemma ising_dproj_eq0 i f :
  (forall x, ising_dproj i f x = 0) -> forall x b, f (spin_set x i b) = f x.
Proof.
move=> h.
have hp x : f (spin_set x i true) = f (spin_set x i false).
  have := h (spin_set x i true); rewrite ising_dproj_eq spin_set_same.
  rewrite ising_cond_mean_set half_diff_set /half_diff.
  have := ising_cond_mean_lt1 i x; rewrite ltr_norml => /andP[_ m1].
  move=> /eqP; rewrite /spin /= mulf_eq0 subr_eq0 (gt_eqF m1) /=.
  by rewrite mulf_eq0 invr_eq0 pnatr_eq0 orbF subr_eq0; move/eqP.
move=> x b; rewrite [in RHS](ising_pair_val i).
by case: b; case: (x i); rewrite // hp.
Qed.

Lemma ising_dirichlet_eq0 f : ising_dirichlet A theta f = 0 -> forall x y, f x = f y.
Proof.
move=> h0.
have hpos : forall i : 'I_n, true -> 0 <= E (fun x => ising_dproj i f x ^+ 2).
  by move=> i _; apply: ising_mean_ge0 => x; exact: sqr_ge0.
have hE := psumr_eq0P hpos (etrans (esym (ising_dirichletE f)) h0).
apply: cube_const => x i b; apply: (ising_dproj_eq0 _ x b) => y.
have := ising_mean_eq0 (fun z => sqr_ge0 (ising_dproj i f z)) (hE i isT) y.
by move/eqP; rewrite sqrf_eq0 => /eqP.
Qed.

End ising.

Section ising_block.
Variables (R : realType) (n : nat) (A : 'M[R]_n) (theta : 'cV[R]_n).
Hypothesis Asym : A \is symmetricmx.
Hypothesis Adiag : forall k, A k k = 0.
Local Notation cube := {ffun 'I_n -> bool}.
Local Notation w := (ising_weight A theta).
Implicit Types (x : cube) (i j : 'I_n).

Lemma mxdot_deltal (M : 'cV[R]_n) k : mxdot (delta_mx k 0) M = M k 0.
Proof. by rewrite mxdotC mxdot_delta. Qed.

Lemma spin_vec_set2 x i j c d : i != j ->
  spin_vec (spin_set (spin_set x i c) j d) =
  (spin_vec x - spin (x i) *: delta_mx i 0 - spin (x j) *: delta_mx j 0) +
  spin c *: delta_mx i 0 + spin d *: delta_mx j 0 :> 'cV[R]_n.
Proof.
move=> ij; apply/matrixP => k l; rewrite (ord1 l) !mxE !ffunE.
have [->|kj] := eqVneq k j.
  have [ji|ji] := eqVneq j i; first by move: ij; rewrite ji eqxx.
  by rewrite /=; ring.
have [->|ki] := eqVneq k i; first by rewrite /=; ring.
by rewrite /=; ring.
Qed.

Lemma quad_expand i j (u : 'cV[R]_n) (al be : R) :
  mxdot (u + al *: delta_mx i 0 + be *: delta_mx j 0)
    (A *m (u + al *: delta_mx i 0 + be *: delta_mx j 0)) =
  mxdot u (A *m u) + 2 * al * (A *m u) i 0 + 2 * be * (A *m u) j 0 +
  2 * al * be * A i j.
Proof.
have hl k : mxdot u (A *m delta_mx k 0) = (A *m u) k 0.
  by rewrite -(mxdot_mulmx_sym _ _ Asym) mxdot_delta.
have hd k l : mxdot (delta_mx k 0 : 'cV[R]_n) (A *m delta_mx l 0) = A k l.
  by rewrite mxdot_deltal -colE mxE.
have hji : A j i = A i j by move/symmetricmxP: Asym => /(congr1 (fun M : 'M[R]_n => M i j)); rewrite mxE.
rewrite !mulmxDr -!scalemxAr !mxdotDl !mxdotDr !mxdotZl !mxdotZr.
rewrite !hl !hd !mxdot_deltal hji !Adiag.
ring.
Qed.

Lemma lin_expand i j (u : 'cV[R]_n) (al be : R) :
  mxdot theta (u + al *: delta_mx i 0 + be *: delta_mx j 0) =
  mxdot theta u + al * theta i 0 + be * theta j 0.
Proof. by rewrite !mxdotDr !mxdotZr !mxdot_delta. Qed.

Lemma ising_weight_block x i j : i != j ->
  exists K a b, [/\ 0 < K, `|a| < 1, `|b| < 1 &
    forall c d, w (spin_set (spin_set x i c) j d) =
      K * ((1 + a * spin c) * (1 + b * spin d) *
           (1 + sk_tanh (A i j) * spin c * spin d))].
Proof.
move=> ij.
pose u := spin_vec x - spin (x i) *: (delta_mx i 0 : 'cV[R]_n) -
  spin (x j) *: (delta_mx j 0 : 'cV[R]_n).
pose hi := (A *m u) i 0 + theta i 0.
pose hj := (A *m u) j 0 + theta j 0.
pose c0 := mxdot u (A *m u) / 2 + mxdot theta u.
exists (expR c0 * sk_cosh hi * sk_cosh hj * sk_cosh (A i j)), (sk_tanh hi), (sk_tanh hj).
split; [| exact: sk_tanh_lt1 | exact: sk_tanh_lt1 |].
  apply: mulr_gt0; last exact: sk_cosh_gt0.
  apply: mulr_gt0; last exact: sk_cosh_gt0.
  by apply: mulr_gt0; [exact: expR_gt0 | exact: sk_cosh_gt0].
move=> c d.
have ex : mxdot (spin_vec (spin_set (spin_set x i c) j d))
      (A *m spin_vec (spin_set (spin_set x i c) j d)) / 2 +
    mxdot theta (spin_vec (spin_set (spin_set x i c) j d)) =
    c0 + spin c * hi + spin d * hj + spin (c == d) * A i j.
  rewrite (spin_vec_set2 x c d ij) -/u quad_expand lin_expand /c0 /hi /hj.
  by rewrite -spin_mul; field.
rewrite /ising_weight ex !expRD !expR_spin -spin_mul.
ring.
Qed.

End ising_block.
