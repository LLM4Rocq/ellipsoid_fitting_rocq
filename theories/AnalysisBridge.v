(* AnalysisBridge: lemmas that connect Stdlib's real analysis
   (derivable_pt_lim, continuity_pt, Rabs, Rpower.ln, ...) with
   MathComp-Analysis (is_derive, continuous, limits along filters), so that
   statements written with Stdlib's operations can be proved with
   MathComp-Analysis.

   The carrier is Stdlib's R, made a realType by Rstruct and a topological
   and pseudometric space by Rstruct_topology. R is not a normedModType, its
   copy R^o is, so every statement about derivatives below writes
   @is_derive R R^o R^o x 1 f l, @derivable R R^o R^o f x 1 and
   @derive R R^o R^o f x 1 (MathComp's 'D_1 f x). Continuity at a point is
   MathComp's {for x, continuous f}; continuous f is continuity everywhere.

   Conventions.
   - Statements use Stdlib's operations (+, *, /, exp, Rpower.ln, sqrt,
     pow) so that field, ring, lra and nra apply to them; only the proofs
     touch MathComp's ring operations. Under this header a bare ln is
     MathComp's exp.ln, so Stdlib's logarithm is always written Rpower.ln.
   - The lemmas on derivatives are named after the operation they treat
     (is_derive_plus, is_derive_exp, is_derive_inv, is_derive_comp, ...) and
     use MathComp's argument order is_derive x 1 f l. Names that would clash
     with a MathComp lemma get an R (is_derive_id_R, continuous_Rln, ...).
   - The lemmas suffixed _Reals convert between the two libraries. The
     lemmas cvg_Reals_* and nbhs_Reals unfold MathComp's limits and
     neighbourhoods into epsilon-delta statements.
   - The tactic auto_derive proves goals is_derive, derivable,
     derivable_pt_lim and derivable_pt; see the comment above its
     definition.

   This module re-exports the libraries below, so that a proof module can
   begin with From EllipsoidFitting Require Import AnalysisBridge. followed
   by its own Open Scope lines. It contains lemmas, instances and tactics
   only, and no axiom. Stdlib defines Rpower.ln through ln_exists, whose
   proof depends on the axiom classic of Stdlib.Logic.Classical_Prop, so the
   statements that mention Rpower.ln (is_derive_ln, is_derive_ln_comp,
   continuous_Rln) depend on it too. *)

From Stdlib Require Export Reals Lra.
From HB Require Export structures.
From mathcomp Require Export all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Export boolp classical_sets functions reals.
From mathcomp Require Export Rstruct.
From mathcomp Require Export topology normedtype derive realfun sequences exp.
From mathcomp Require Export Rstruct_topology.
From mathcomp Require Export ereal measure lebesgue_measure lebesgue_integral ftc.
Export GRing.Theory Num.Theory.
Local Open Scope R_scope.


(* ---- Stdlib's derivative and MathComp's is_derive ---- *)

Lemma is_derive_of_Reals {f : R -> R} {x l : R} :
  derivable_pt_lim f x l -> @is_derive R R^o R^o x 1 f l.
Proof.
move=> Hd.
apply: DeriveDef; last apply: cvg_lim;
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
all: by rewrite [(h + x)%R]addrC mulrC.
Qed.

Lemma Reals_of_is_derive {f : R -> R} {x l : R} :
  @is_derive R R^o R^o x 1 f l -> derivable_pt_lim f x l.
Proof.
move=> [Hd Hv] eps eps0.
rewrite /derivable in Hd; rewrite /derive in Hv; rewrite Hv in Hd.
move/cvgrPdist_lt: Hd => /(_ eps (introT RltP eps0)).
rewrite near_withinE => /nbhs_ballP [d d0 Hdl].
have d0' : 0 < d by apply/RltP; exact: d0.
exists (mkposreal d d0') => h hN0 /= Hh.
have Hb : ball (0%R : R) d h.
  by rewrite /ball /= sub0r normrN; apply/RltP; rewrite -RabsE.
have hN0' : h != 0%R by apply/eqP.
have := Hdl h Hb hN0'.
move=> /RltP; rewrite -RabsE -RminusE Rabs_minus_sym.
rewrite [X in Rabs (X - _)](_ : _ = (f (x + h) - f x) / h) //.
by rewrite /GRing.scale /= mulr1 RplusE RminusE RdivE [(h + x)%R]addrC mulrC.
Qed.

Lemma is_derive_Reals (f : R -> R) (x l : R) :
  @is_derive R R^o R^o x 1 f l <-> derivable_pt_lim f x l.
Proof. by split; [exact: Reals_of_is_derive | exact: is_derive_of_Reals]. Qed.

Lemma derivable_of_is_derive (f : R -> R) (x l : R) :
  @is_derive R R^o R^o x 1 f l -> @derivable R R^o R^o f x 1.
Proof. by move=> [H _]. Qed.

Lemma ex_derive_Reals_0 (f : R -> R) (x : R) :
  @derivable R R^o R^o f x 1 -> derivable_pt f x.
Proof.
move=> Hd; exists (@derive R R^o R^o f x 1).
by apply: Reals_of_is_derive; exact: derivableP.
Qed.

Lemma is_derive_ext (f g : R -> R) (x l : R) :
  (forall t, f t = g t) ->
  @is_derive R R^o R^o x 1 f l -> @is_derive R R^o R^o x 1 g l.
Proof. by move=> Hfg; rewrite (funext Hfg). Qed.

Lemma is_derive_continuous (f : R -> R) (x l : R) :
  @is_derive R R^o R^o x 1 f l -> {for x, continuous f}.
Proof.
by move=> [Hd _]; exact: (differentiable_continuous (iffLR (derivable1_diffP _ _) Hd)).
Qed.

Lemma ex_derive_continuous (f : R -> R) (x : R) :
  @derivable R R^o R^o f x 1 -> {for x, continuous f}.
Proof.
by move=> Hd; exact: (differentiable_continuous (iffLR (derivable1_diffP _ _) Hd)).
Qed.

Lemma is_derive_continuity_pt (f : R -> R) (x l : R) :
  @is_derive R R^o R^o x 1 f l -> continuity_pt f x.
Proof.
by move=> H; apply: derivable_continuous_pt; exists l; exact: Reals_of_is_derive.
Qed.

(* ---- elementary functions ---- *)

Global Instance is_derive_exp (x : R) : @is_derive R R^o R^o x 1 exp (exp x).
Proof. by apply: is_derive_of_Reals; exact: derivable_pt_lim_exp. Qed.

Global Instance is_derive_ln (x : R) :
  0 < x -> @is_derive R R^o R^o x 1 Rpower.ln (/ x).
Proof. by move=> x0; apply: is_derive_of_Reals; exact: derivable_pt_lim_ln. Qed.

Global Instance is_derive_Rsqrt (x : R) :
  0 < x -> @is_derive R R^o R^o x 1 sqrt (/ (2 * sqrt x)).
Proof. by move=> x0; apply: is_derive_of_Reals; exact: derivable_pt_lim_sqrt. Qed.

Global Instance is_derive_Rinv (x : R) :
  x <> 0 -> @is_derive R R^o R^o x 1 Rinv (- 1 / x ^ 2).
Proof.
move=> x0; apply: is_derive_of_Reals.
have H := derivable_pt_lim_div (fct_cte 1) Ranalysis1.id x 0 1
  (derivable_pt_lim_const 1 x) (derivable_pt_lim_id x) x0.
have -> : - 1 / x ^ 2 = (0 * Ranalysis1.id x - 1 * fct_cte 1 x) / (Ranalysis1.id x)².
  by rewrite /fct_cte /Ranalysis1.id /Rsqr; field; auto.
apply: (derivable_pt_lim_ext _ _ _ _ _ H) => t.
by rewrite /div_fct /fct_cte /Ranalysis1.id /Rdiv Rmult_1_l.
Qed.

Global Instance is_derive_Rpow (n : nat) (x : R) :
  @is_derive R R^o R^o x 1 (fun y => y ^ n) (INR n * x ^ Nat.pred n).
Proof. by apply: is_derive_of_Reals; exact: derivable_pt_lim_pow. Qed.

Global Instance is_derive_Rsqr (x : R) : @is_derive R R^o R^o x 1 Rsqr (2 * x).
Proof. by apply: is_derive_of_Reals; exact: derivable_pt_lim_Rsqr. Qed.

(* ---- combinators, stated with Stdlib's operations ---- *)

Lemma is_derive_const (c x : R) : @is_derive R R^o R^o x 1 (fun _ => c) 0.
Proof. by apply: is_derive_of_Reals; exact: derivable_pt_lim_const. Qed.

Lemma is_derive_id_R (x : R) : @is_derive R R^o R^o x 1 (fun y => y) 1.
Proof. by apply: is_derive_of_Reals; exact: derivable_pt_lim_id. Qed.

Lemma is_derive_plus (f g : R -> R) (x df dg : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => f y + g y) (df + dg).
Proof.
move=> /Reals_of_is_derive Hf /Reals_of_is_derive Hg; apply: is_derive_of_Reals.
exact: (derivable_pt_lim_plus f g x df dg Hf Hg).
Qed.

Lemma is_derive_minus (f g : R -> R) (x df dg : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => f y - g y) (df - dg).
Proof.
move=> /Reals_of_is_derive Hf /Reals_of_is_derive Hg; apply: is_derive_of_Reals.
exact: (derivable_pt_lim_minus f g x df dg Hf Hg).
Qed.

Lemma is_derive_mult (f g : R -> R) (x df dg : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => f y * g y) (df * g x + f x * dg).
Proof.
move=> /Reals_of_is_derive Hf /Reals_of_is_derive Hg; apply: is_derive_of_Reals.
exact: (derivable_pt_lim_mult f g x df dg Hf Hg).
Qed.

Lemma is_derive_opp (f : R -> R) (x df : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 (fun y => - f y) (- df).
Proof.
move=> /Reals_of_is_derive Hf; apply: is_derive_of_Reals.
exact: (derivable_pt_lim_opp f x df Hf).
Qed.

Lemma is_derive_scal (k : R) (f : R -> R) (x df : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 (fun y => k * f y) (k * df).
Proof.
move=> /Reals_of_is_derive Hf; apply: is_derive_of_Reals.
exact: (derivable_pt_lim_scal f k x df Hf).
Qed.

Lemma is_derive_scal_l (k : R) (f : R -> R) (x df : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 (fun y => f y * k) (df * k).
Proof.
move=> /Reals_of_is_derive Hf.
have -> : df * k = df * fct_cte k x + f x * 0 by rewrite /fct_cte; ring.
exact: (is_derive_of_Reals
  (derivable_pt_lim_mult f (fct_cte k) x df 0 Hf (derivable_pt_lim_const k x))).
Qed.

Lemma is_derive_div (f g : R -> R) (x df dg : R) :
  @is_derive R R^o R^o x 1 f df -> @is_derive R R^o R^o x 1 g dg -> g x <> 0 ->
  @is_derive R R^o R^o x 1 (fun y => f y / g y) ((df * g x - dg * f x) / g x ^ 2).
Proof.
move=> /Reals_of_is_derive Hf /Reals_of_is_derive Hg gx0.
have -> : (df * g x - dg * f x) / g x ^ 2 = (df * g x - dg * f x) / (g x)².
  by rewrite /Rsqr; field; auto.
exact: (is_derive_of_Reals (derivable_pt_lim_div f g x df dg Hf Hg gx0)).
Qed.

(* Stdlib's chain rule with the composite written as a lambda. *)
Lemma derivable_pt_lim_comp_R (f g : R -> R) (x df dg : R) :
  derivable_pt_lim g x dg -> derivable_pt_lim f (g x) df ->
  derivable_pt_lim (fun y => f (g y)) x (df * dg).
Proof.
by move=> Hg Hf; have := derivable_pt_lim_comp g f x dg df Hg Hf; rewrite /Ranalysis1.comp.
Qed.

Lemma is_derive_inv (g : R -> R) (x dg : R) :
  @is_derive R R^o R^o x 1 g dg -> g x <> 0 ->
  @is_derive R R^o R^o x 1 (fun y => / g y) (- dg / g x ^ 2).
Proof.
move=> /Reals_of_is_derive Hg gx0.
have -> : - dg / g x ^ 2 = - 1 / g x ^ 2 * dg by field; auto.
exact (is_derive_of_Reals (derivable_pt_lim_comp_R Rinv g x (- 1 / g x ^ 2) dg Hg
  (Reals_of_is_derive (is_derive_Rinv (g x) gx0)))).
Qed.

Lemma is_derive_comp (f g : R -> R) (x df dg : R) :
  @is_derive R R^o R^o (g x) 1 f df -> @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => f (g y)) (dg * df).
Proof.
move=> /Reals_of_is_derive Hf /Reals_of_is_derive Hg.
have -> : dg * df = df * dg by ring.
exact (is_derive_of_Reals (derivable_pt_lim_comp_R f g x df dg Hg Hf)).
Qed.

Lemma is_derive_exp_comp (g : R -> R) (x dg : R) :
  @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => exp (g y)) (exp (g x) * dg).
Proof.
move=> /Reals_of_is_derive Hg; apply: is_derive_of_Reals.
exact (derivable_pt_lim_comp_R exp g x (exp (g x)) dg Hg (derivable_pt_lim_exp (g x))).
Qed.

Lemma is_derive_ln_comp (g : R -> R) (x dg : R) :
  0 < g x -> @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => Rpower.ln (g y)) (/ g x * dg).
Proof.
move=> gx0 /Reals_of_is_derive Hg; apply: is_derive_of_Reals.
exact (derivable_pt_lim_comp_R Rpower.ln g x (/ g x) dg Hg (derivable_pt_lim_ln (g x) gx0)).
Qed.

Lemma is_derive_sqrt (g : R -> R) (x dg : R) :
  @is_derive R R^o R^o x 1 g dg -> 0 < g x ->
  @is_derive R R^o R^o x 1 (fun y => sqrt (g y)) (dg / (2 * sqrt (g x))).
Proof.
move=> /Reals_of_is_derive Hg gx0.
have -> : dg / (2 * sqrt (g x)) = / (2 * sqrt (g x)) * dg by rewrite /Rdiv Rmult_comm.
apply: is_derive_of_Reals.
exact (derivable_pt_lim_comp_R sqrt g x (/ (2 * sqrt (g x))) dg Hg (derivable_pt_lim_sqrt (g x) gx0)).
Qed.

Lemma is_derive_pow (g : R -> R) (n : nat) (x dg : R) :
  @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => g y ^ n) (INR n * dg * g x ^ Nat.pred n).
Proof.
move=> /Reals_of_is_derive Hg.
have -> : INR n * dg * g x ^ Nat.pred n = INR n * g x ^ Nat.pred n * dg by ring.
apply: is_derive_of_Reals.
exact (derivable_pt_lim_comp_R (fun y => y ^ n) g x (INR n * g x ^ Nat.pred n) dg Hg (derivable_pt_lim_pow (g x) n)).
Qed.

Lemma is_derive_Rsqr_comp (g : R -> R) (x dg : R) :
  @is_derive R R^o R^o x 1 g dg ->
  @is_derive R R^o R^o x 1 (fun y => Rsqr (g y)) (2 * g x * dg).
Proof.
move=> /Reals_of_is_derive Hg; apply: is_derive_of_Reals.
exact (derivable_pt_lim_comp_R Rsqr g x (2 * g x) dg Hg (derivable_pt_lim_Rsqr (g x))).
Qed.

(* ---- continuity of the elementary functions ---- *)

Lemma continuous_Rexp : continuous exp.
Proof. by move=> x; exact: is_derive_continuous (is_derive_exp x). Qed.

Lemma continuous_Rln (x : R) : 0 < x -> {for x, continuous Rpower.ln}.
Proof. by move=> x0; exact: is_derive_continuous (is_derive_ln x x0). Qed.

Lemma continuous_Rsqrt (x : R) : 0 <= x -> {for x, continuous sqrt}.
Proof. by move=> x0; apply/continuity_ptE; exact: continuity_pt_sqrt. Qed.

Lemma continuous_Rpow (n : nat) : continuous (fun y : R => y ^ n).
Proof. by move=> x; exact: is_derive_continuous (is_derive_Rpow n x). Qed.

(* ---- the tactic auto_derive ----

   On a goal @is_derive R R^o R^o x 1 (fun y => e y) l the tactic applies
   is_derive_eq, derives e by the combinators above (sum, difference,
   product, quotient, opposite, inverse, exp, Rpower.ln, sqrt, pow, Rsqr,
   constants, the identity, and hypotheses is_derive x 1 f df found by
   eassumption), and leaves the side conditions (0 < g x, g x <> 0), then the
   equation computed derivative = l, stated at type R. A typical script is
   auto_derive; try lra. followed by field; lra. for that equation.
   On derivable f x 1 it proves the goal outright when the chain closes; on
   derivable_pt_lim f x l and derivable_pt f x it first converts to the
   MathComp form. A function under a definition (gaussian_kernel) must be
   unfolded first.
   Two more features:
   - A hypothesis is used through eapply, so a universally quantified
     hypothesis (forall t, Rabs (t - a) <= rho -> is_derive t 1 f (df t))
     closes a leaf, leaving its premise as a side goal, and so does a
     Stdlib hypothesis derivable_pt_lim f x df.
   - A composite fun y => h (g y) whose head h is not one of the known
     functions is split by the chain rule is_derive_comp, so that a
     hypothesis about h at the point g x can close the inner goal. A bare
     fun y => h y is left to the leaves. *)

Ltac auto_derive_leaf :=
  first [ eassumption
        | match goal with H : _ |- _ => eapply H end
        | eapply is_derive_of_Reals; eassumption
        | eapply is_derive_id_R
        | eapply is_derive_const
        | eapply is_derive_exp
        | eapply is_derive_ln
        | eapply is_derive_Rsqrt
        | eapply is_derive_Rinv
        | eapply is_derive_Rsqr ].

(* Unification returns eta-reduced functions, such as Rminus 1 for
   fun v => 1 - v; the rules below need a lambda. *)
Ltac auto_derive_eta :=
  lazymatch goal with
  | |- is_derive _ _ (fun _ => _) _ => idtac
  | |- @is_derive ?K ?V ?W ?x ?v ?f ?l => change (@is_derive K V W x v (fun y => f y) l)
  end.

(* The rule is chosen on the head symbol of the body, so that unification
   cannot unfold Rminus, Rdiv, Rsqr or pow into a sum or a product first. *)
Ltac auto_derive_rule :=
  auto_derive_eta;
  lazymatch goal with
  | |- is_derive _ _ (fun y => Rsqr _) _ => eapply is_derive_Rsqr_comp
  | |- is_derive _ _ (fun y => Rdiv _ _) _ => eapply is_derive_div
  | |- is_derive _ _ (fun y => Rminus _ _) _ => eapply is_derive_minus
  | |- is_derive _ _ (fun y => Rplus _ _) _ => eapply is_derive_plus
  | |- is_derive _ _ (fun y => Rmult _ _) _ => eapply is_derive_mult
  | |- is_derive _ _ (fun y => Ropp _) _ => eapply is_derive_opp
  | |- is_derive _ _ (fun y => Rinv _) _ => eapply is_derive_inv
  | |- is_derive _ _ (fun y => exp _) _ => eapply is_derive_exp_comp
  | |- is_derive _ _ (fun y => Rpower.ln _) _ => eapply is_derive_ln_comp
  | |- is_derive _ _ (fun y => sqrt _) _ => eapply is_derive_sqrt
  | |- is_derive _ _ (fun y => pow _ _) _ => eapply is_derive_pow
  | |- is_derive _ _ (fun y => _ y) _ => fail
  | |- is_derive _ _ (fun y => ?h _) _ => eapply is_derive_comp
  end.

Ltac auto_derive_chain := repeat first [ auto_derive_leaf | auto_derive_rule ].

Ltac auto_derive_eq_R :=
  lazymatch goal with
  | |- @eq _ ?a ?b => change (@eq R a b)
  end.

Ltac auto_derive :=
  lazymatch goal with
  | |- is_derive _ _ _ _ =>
      eapply is_derive_eq; [ auto_derive_chain | auto_derive_eq_R ]; cbv beta
  | |- derivable _ _ _ => eapply derivable_of_is_derive; auto_derive_chain; cbv beta
  | |- derivable_pt_lim _ _ _ => apply Reals_of_is_derive; auto_derive
  | |- derivable_pt _ _ => apply ex_derive_Reals_0; auto_derive
  end.


(* ---- continuity ---- *)

Lemma continuity_pt_filterlim (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_ptE. Qed.

Lemma continuity_continuous (f : R -> R) : continuity f <-> continuous f.
Proof. by split=> H x; apply/continuity_ptE; exact: H. Qed.

Lemma continuous_Rabs : continuous Rabs.
Proof. by apply/continuity_continuous; exact: Rcontinuity_abs. Qed.

(* ---- neighbourhoods and limits, in epsilon-delta form ---- *)

Lemma nbhs_Reals (x : R) (P : R -> Prop) :
  nbhs x P <-> (exists delta, 0 < delta /\ forall y, Rabs (y - x) < delta -> P y).
Proof.
split.
- move=> /nbhs_ballP [d d0 Hd]; exists d; split; first by apply/RltP; exact: d0.
  move=> y Hy; apply: Hd; rewrite /ball /=; apply/RltP.
  by rewrite -RabsE -RminusE Rabs_minus_sym.
- move=> [d [d0 Hd]]; have d0' : (0 < d)%R by apply/RltP.
  apply/nbhs_ballP; exists d => // y; rewrite /ball /= => /RltP.
  by rewrite -RabsE -RminusE Rabs_minus_sym; exact: Hd.
Qed.

Lemma cvg_Reals_nbhs (f : R -> R) (x l : R) :
  (f y @[y --> x] --> l)%classic <->
  (forall eps, 0 < eps -> exists delta, 0 < delta /\
     forall y, Rabs (y - x) < delta -> Rabs (f y - l) < eps).
Proof.
split.
- move=> H eps eps0.
  have Hl : nbhs l (fun z => Rabs (z - l) < eps) by apply/nbhs_Reals; exists eps.
  have /nbhs_Reals [d [d0 Hd]] : nbhs x (fun y => Rabs (f y - l) < eps) := H _ Hl.
  by exists d; split=> // y /Hd.
- move=> H A /nbhs_Reals [eps [eps0 HA]].
  have [d [d0 Hd]] := H eps eps0.
  suff : nbhs x (fun y => A (f y)) by [].
  by apply/nbhs_Reals; exists d; split=> // y /Hd /HA.
Qed.

Lemma cvg_Reals_pinfty (f : R -> R) (l : R) :
  (f x @[x --> +oo%R] --> l)%classic <->
  (forall eps, 0 < eps -> exists M, forall x, M < x -> Rabs (f x - l) < eps).
Proof.
split.
- move=> H eps eps0.
  have Hl : nbhs l (fun z => Rabs (z - l) < eps) by apply/nbhs_Reals; exists eps.
  have [M [_ HM]] : exists M : R, M \is Num.real /\
      forall x, (M < x)%R -> Rabs (f x - l) < eps := H _ Hl.
  by exists M => x /RltP /HM.
- move=> H A /nbhs_Reals [eps [eps0 HA]].
  have [M HM] := H eps eps0.
  suff : exists M : R, M \is Num.real /\ forall x, (M < x)%R -> A (f x) by [].
  by exists M; split; [exact: num_real | move=> x /RltP /HM /HA].
Qed.

Lemma is_lim_exp_m : (exp x @[x --> -oo%R] --> 0)%classic.
Proof.
have -> : exp = expR by apply/funext => x; exact: RexpE.
by apply/cvgNy_compNP; exact: cvgr_expR.
Qed.

Lemma continuous_Reals (f : R -> R) (x : R) :
  {for x, continuous f} <->
  (forall eps, 0 < eps -> exists delta, 0 < delta /\
     forall y, Rabs (y - x) < delta -> Rabs (f y - f x) < eps).
Proof. exact: cvg_Reals_nbhs. Qed.

(* ---- algebra on R^o ---- *)

(* ---- continuity combinators at real-valued functions ---- *)

Section ContinuityCombinators.
Variable T : topologicalType.
Implicit Types (f g : T -> R) (x : T).

Lemma continuous_const (c : R) x : {for x, continuous (fun _ : T => c)}.
Proof. exact: cvg_cst. Qed.

Lemma continuous_plus f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun y => f y + g y)}.
Proof. by move=> Hf Hg; exact (continuousD (V := R^o) Hf Hg). Qed.

Lemma continuous_minus f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun y => f y - g y)}.
Proof. by move=> Hf Hg; exact (continuousB (V := R^o) Hf Hg). Qed.

Lemma continuous_mult f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun y => f y * g y)}.
Proof. by move=> Hf Hg; exact (continuousM (K := R) Hf Hg). Qed.

Lemma continuous_opp f x :
  {for x, continuous f} -> {for x, continuous (fun y => - f y)}.
Proof. by move=> Hf; exact (continuousN (V := R^o) Hf). Qed.

End ContinuityCombinators.

Lemma continuous_id (x : R) : {for x, continuous (fun y : R => y)}.
Proof. exact: cvg_id. Qed.


(* ---- division and absolute value ---- *)

Lemma Rdiv_le_0_compat (r1 r2 : R) : 0 <= r1 -> 0 < r2 -> 0 <= r1 / r2.
Proof.
move=> H1 H2; rewrite /Rdiv; apply: Rmult_le_pos => //.
by apply: Rlt_le; exact: Rinv_0_lt_compat.
Qed.

Lemma Rabs_lt_between (x y : R) : Rabs x < y <-> - y < x < y.
Proof.
split; first by move=> /Rabs_def2 [H1 H2]; split.
by move=> [H1 H2]; apply: Rabs_def1.
Qed.

Lemma Rabs_le_between (x y : R) : Rabs x <= y <-> - y <= x <= y.
Proof.
split; last exact: Rabs_le.
move=> H; split.
- by have := Rle_abs (- x); rewrite Rabs_Ropp; lra.
- by have := Rle_abs x; lra.
Qed.

Lemma Rabs_div (a b : R) : b <> 0 -> Rabs (a / b) = Rabs a / Rabs b.
Proof. by move=> b0; rewrite /Rdiv Rabs_mult Rabs_inv. Qed.

(* ---- mean value theorems ---- *)

Lemma MVT_Reals (f df : R -> R) (a b : R) : a < b ->
  (forall x, a < x < b -> @is_derive R R^o R^o x 1 f (df x)) ->
  (forall x, a <= x <= b -> continuity_pt f x) ->
  exists c, a < c < b /\ f b - f a = df c * (b - a).
Proof.
move=> ab Hd Hc.
have ab' : (a < b)%R by apply/RltP.
have [c cab Heq] : exists2 c, c \in `]a, b[%R & (f b - f a = df c * (b - a))%R.
  apply: MVT => //.
  - move=> x; rewrite in_itv /= => /andP [/RltP ax /RltP xb].
    by have := Hd x (conj ax xb).
  - apply: continuous_in_subspaceT => x /[1!inE].
    rewrite /= in_itv /= => /andP [/RleP ax /RleP xb].
    by apply/continuity_ptE; exact: Hc.
move: cab; rewrite in_itv /= => /andP [/RltP ac /RltP cb].
by exists c; split.
Qed.

Lemma MVT_gen (f : R -> R) (a b : R) (df : R -> R) :
  (forall x, Rmin a b < x < Rmax a b -> @is_derive R R^o R^o x 1 f (df x)) ->
  (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f x) ->
  exists c, Rmin a b <= c <= Rmax a b /\ f b - f a = df c * (b - a).
Proof.
have key : forall a b, a <= b ->
    (forall x, a < x < b -> @is_derive R R^o R^o x 1 f (df x)) ->
    (forall x, a <= x <= b -> continuity_pt f x) ->
    exists c, a <= c <= b /\ f b - f a = df c * (b - a).
  move=> a' b' ab Hd Hc.
  have [c cab Heq] : exists2 c, c \in `[a', b']%R & (f b' - f a' = df c * (b' - a'))%R.
    apply: MVT_segment; first exact/RleP.
    - move=> x; rewrite in_itv /= => /andP [/RltP ax /RltP xb].
      by have := Hd x (conj ax xb).
    - apply: continuous_in_subspaceT => x /[1!inE].
      rewrite /= in_itv /= => /andP [/RleP ax /RleP xb].
      by apply/continuity_ptE; exact: Hc.
  move: cab; rewrite in_itv /= => /andP [/RleP ac /RleP cb].
  by exists c; split.
case: (Rle_or_lt a b) => ab Hd Hc.
- rewrite (Rmin_left _ _ ab) (Rmax_right _ _ ab) in Hd Hc *.
  exact: key.
- have ba : b <= a by lra.
  rewrite (Rmin_right _ _ ba) (Rmax_left _ _ ba) in Hd Hc *.
  have [c [cab Heq]] := key b a ba Hd Hc.
  exists c; split=> //.
  have -> : f b - f a = - (f a - f b) by ring.
  by rewrite Heq; ring.
Qed.

(* The mean value theorem on a ball around a, with an intermediate point c
   no farther from a than b is. *)
Lemma MVT_cor4 (f df : R -> R) (a eps : R) :
  (forall c, Rabs (c - a) <= eps -> @is_derive R R^o R^o c 1 f (df c)) ->
  forall b, Rabs (b - a) <= eps ->
  exists c, f b - f a = df c * (b - a) /\ Rabs (c - a) <= Rabs (b - a).
Proof.
move=> Hd b Hb.
have Hin : forall x, Rmin a b <= x <= Rmax a b -> Rabs (x - a) <= Rabs (b - a).
  move=> x [Hx1 Hx2]; case: (Rle_or_lt a b) => ab.
  - rewrite (Rmin_left _ _ ab) (Rmax_right _ _ ab) in Hx1 Hx2.
    have -> : Rabs (b - a) = b - a by rewrite Rabs_pos_eq; lra.
    by apply: Rabs_le; lra.
  - have ba : b <= a by lra.
    rewrite (Rmin_right _ _ ba) (Rmax_left _ _ ba) in Hx1 Hx2.
    have -> : Rabs (b - a) = - (b - a) by rewrite Rabs_left1; lra.
    by apply: Rabs_le; lra.
have Hd' : forall x, Rmin a b < x < Rmax a b -> @is_derive R R^o R^o x 1 f (df x).
  by move=> x Hx; apply: Hd; apply: Rle_trans _ Hb; apply: Hin; lra.
have Hc' : forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f x.
  move=> x Hx; have Hxa : Rabs (x - a) <= eps by apply: Rle_trans _ Hb; exact: Hin.
  exact: (is_derive_continuity_pt _ _ _ (Hd x Hxa)).
have [c [Hc Heq]] := MVT_gen f a b df Hd' Hc'.
by exists c; split=> //; exact: Hin.
Qed.
