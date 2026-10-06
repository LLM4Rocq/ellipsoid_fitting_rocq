(* AnalysisBridge2: AnalysisBridge with a stronger tactic auto_derive.
   This module re-exports AnalysisBridge and adds no lemma, no definition,
   no notation and no axiom. It redefines the tactics auto_derive_leaf,
   auto_derive_rule, auto_derive_chain and auto_derive, which shadow those
   of AnalysisBridge in a module that imports AnalysisBridge2. The new
   auto_derive handles two more cases.
   - A hypothesis is used through eapply, so a universally quantified
     hypothesis (forall t, Rabs (t - a) <= rho -> is_derive t 1 f (df t))
     closes a leaf, leaving its premise as a side goal, and so does a
     Stdlib hypothesis derivable_pt_lim f x df.
   - A composite fun y => h (g y) whose head h is not one of the known
     functions is split by the chain rule is_derive_comp, so that a
     hypothesis about h at the point g x can close the inner goal. A bare
     fun y => h y is left to the leaves. *)

From EllipsoidFitting Require Export AnalysisBridge.
Local Open Scope R_scope.

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

Ltac auto_derive :=
  lazymatch goal with
  | |- is_derive _ _ _ _ =>
      eapply is_derive_eq; [ auto_derive_chain | auto_derive_eq_R ]; cbv beta
  | |- derivable _ _ _ => eapply derivable_of_is_derive; auto_derive_chain; cbv beta
  | |- derivable_pt_lim _ _ _ => apply Reals_of_is_derive; auto_derive
  | |- derivable_pt _ _ => apply ex_derive_Reals_0; auto_derive
  end.
