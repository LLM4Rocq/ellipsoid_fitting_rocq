From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Hierarchy Builder reports redundant canonical projections when it builds
   the instances below. They are harmless. *)
Local Set Warnings "-redundant-canonical-projection".

(* Transport of a normed module structure from V to a type T along a
   bijection encode : T -> V, decode : V -> T.

   Port notes (Coquelicot to MathComp-Analysis).
   - V is a normedModType over Stdlib's R, the analogue of
     NormedModule R_AbsRing.
   - The structures live on the type copy transport_type, a new name. It is
     T, but it also records V, encode, decode and the two inverse laws, so
     that Hierarchy Builder can key the instances on it. The instances are
     declared in the section and are generalized over its six parameters when
     the section closes, as the Coquelicot canonical structures were.
   - Coquelicot needed five mixins. Here there are four factory instances:
     transport_AbelianMonoid_mixin (additive monoid, nmodType),
     transport_AbelianGroup_mixin (opposite, zmodType),
     transport_ModuleSpace_mixin (scaling, lmodType R) and
     transport_NormedModule_mixin (norm, through the factory
     Lmodule_isNormed). The last one also builds the uniform and
     pseudometric structure from the norm, so the Coquelicot
     transport_UniformSpace_mixin has no separate factory. The name is kept
     for the class of that pseudometric structure, and the content of the
     Coquelicot mixin, that the ball of T is the ball of V through encode, is
     the lemma transport_ball.
   - The norm of x is the norm of encode x, as in Coquelicot. The ball of T is
     the ball of V through encode, as in Coquelicot, because the ball of a
     MathComp normed module is the ball of its norm.
   - Coquelicot's is_linear is algebraic linearity together with a bound
     norm (l x) <= M * norm x for some M > 0. MathComp's linear is algebraic
     only. The two linearity theorems state both parts, as a conjunction.
     The bound is stated with Stdlib's order on R. *)

Definition transport_type (V : normedModType R) (T : Type)
  (encode : T -> V) (decode : V -> T)
  (decode_encode : forall x, decode (encode x) = x)
  (encode_decode : forall x, encode (decode x) = x) : Type := T.

Section Transport.
Context (V : normedModType R) (T : Type).
Context (encode : T -> V) (decode : V -> T).
Context (decode_encode : forall x, decode (encode x) = x).
Context (encode_decode : forall x, encode (decode x) = x).

Local Notation TT := (transport_type V T encode decode decode_encode encode_decode).

Lemma transport_encode_injective x y : encode x = encode y -> x = y.
Proof. intros H; rewrite <- (decode_encode x), <- (decode_encode y), H; reflexivity. Qed.

Definition transport_plus (x y : T) : T := decode (encode x + encode y)%R.
Definition transport_zero : T := decode 0%R.
Definition transport_opp (x : T) : T := decode (- encode x)%R.
Definition transport_scal (c : R) (x : T) : T := decode (c *: encode x)%R.

(* Equality and choice come from V through the injection encode. *)
HB.instance Definition _ := Choice.copy TT (can_type decode_encode).

Lemma transport_plus_comm (x y : TT) : transport_plus x y = transport_plus y x.
Proof. by rewrite /transport_plus addrC. Qed.

Lemma transport_plus_assoc (x y z : TT) :
  transport_plus x (transport_plus y z) = transport_plus (transport_plus x y) z.
Proof. by rewrite /transport_plus !encode_decode addrA. Qed.

Lemma transport_plus_zero_l (x : TT) : transport_plus transport_zero x = x.
Proof. by rewrite /transport_plus /transport_zero encode_decode add0r. Qed.

HB.instance Definition transport_AbelianMonoid_mixin :=
  GRing.isNmodule.Build TT transport_plus_assoc transport_plus_comm
    transport_plus_zero_l.

Definition transport_AbelianMonoid : nmodType := GRing.Nmodule.clone TT _.

Lemma transport_plus_opp_l (x : TT) :
  transport_plus (transport_opp x) x = transport_zero.
Proof.
by rewrite /transport_plus /transport_opp /transport_zero encode_decode addNr.
Qed.

HB.instance Definition transport_AbelianGroup_mixin :=
  GRing.Nmodule_isZmodule.Build TT transport_plus_opp_l.

Definition transport_AbelianGroup : zmodType := GRing.Zmodule.clone TT _.

Lemma transport_scal_assoc (a b : R) (x : TT) :
  transport_scal a (transport_scal b x) = transport_scal (a * b)%R x.
Proof. by rewrite /transport_scal encode_decode scalerA. Qed.

Lemma transport_scal_one (x : TT) : transport_scal 1%R x = x.
Proof. by rewrite /transport_scal scale1r decode_encode. Qed.

Lemma transport_scal_distr_l (a : R) (x y : TT) :
  transport_scal a (x + y)%R =
  ((transport_scal a x : TT) + (transport_scal a y : TT))%R.
Proof.
change (decode (a *: encode (transport_plus x y)) =
  transport_plus (decode (a *: encode x)) (decode (a *: encode y)))%R.
by rewrite /transport_plus !encode_decode scalerDr.
Qed.

Lemma transport_scal_distr_r (x : TT) (a b : R) :
  transport_scal (a + b)%R x =
  ((transport_scal a x : TT) + (transport_scal b x : TT))%R.
Proof.
change (decode ((a + b) *: encode x) =
  transport_plus (decode (a *: encode x)) (decode (b *: encode x)))%R.
by rewrite /transport_plus !encode_decode scalerDl.
Qed.

HB.instance Definition transport_ModuleSpace_mixin :=
  GRing.Zmodule_isLmodule.Build R TT transport_scal_assoc transport_scal_one
    transport_scal_distr_l transport_scal_distr_r.

Definition transport_ModuleSpace : lmodType R := GRing.Lmodule.clone R TT _.

Definition transport_norm (x : TT) : R := (`| encode x |)%R.

Lemma transport_norm_triangle (x y : TT) :
  (transport_norm (x + y) <= transport_norm x + transport_norm y)%R.
Proof.
change (`| encode (transport_plus x y) | <= `| encode x | + `| encode y |)%R.
by rewrite /transport_plus encode_decode ler_normD.
Qed.

Lemma transport_norm_scal (c : R) (x : TT) :
  transport_norm (c *: x)%R = (`| c | * transport_norm x)%R.
Proof.
change (`| encode (transport_scal c x) | = `| c | * `| encode x |)%R.
by rewrite /transport_scal encode_decode normrZ.
Qed.

Lemma transport_norm_eq_zero (x : TT) : transport_norm x = 0%R -> x = 0%R.
Proof.
move=> /normr0_eq0 H; apply: transport_encode_injective.
by rewrite H; change (0%R = encode (decode 0%R)); rewrite encode_decode.
Qed.

(* This factory builds the normed Zmodule, the uniform and pseudometric
   structure of the norm, and the normed module. It replaces the Coquelicot
   mixins transport_UniformSpace_mixin and transport_NormedModule_mixin. *)
HB.instance Definition transport_NormedModule_mixin :=
  Lmodule_isNormed.Build R TT transport_norm_triangle transport_norm_scal
    transport_norm_eq_zero.

Definition transport_UniformSpace : pseudoMetricType R :=
  PseudoMetric.clone R TT _.

(* The class of transport_UniformSpace: the pseudometric structure of T,
   built by transport_NormedModule_mixin. It keeps the name of the Coquelicot
   mixin, whose ball transport_ball describes. *)
Definition transport_UniformSpace_mixin :=
  PseudoMetric.class transport_UniformSpace.

(* Coquelicot's NormedModuleAux is a module space with a uniform space and no
   compatibility law. PreUniformLmodule is the MathComp structure of the same
   shape; its uniform space is the one of transport_UniformSpace. *)
Definition transport_NormedModuleAux : PreUniformLmodule.type R :=
  PreUniformLmodule.clone R TT _.

Definition transport_NormedModule : normedModType R :=
  NormedModule.clone R TT _.

(* The content of the Coquelicot transport_UniformSpace_mixin: the ball of T
   is the ball of V through encode. *)
Lemma transport_ball (x : TT) (e : R) (y : TT) :
  ball x e y <-> ball (encode x) e (encode y).
Proof.
rewrite -!ball_normE /ball_.
change (`| encode (transport_plus x (transport_opp y)) | < e <->
  `| encode x - encode y | < e)%R.
by rewrite /transport_plus /transport_opp !encode_decode.
Qed.

Theorem transport_encode_linear :
  linear (encode : TT -> V) /\
  exists M : R, 0 < M /\ forall x : TT, (`| encode x |)%R <= M * (`| x |)%R.
Proof.
split.
- move=> a u v.
  change (encode (transport_plus (transport_scal a u) v) = a *: encode u + encode v)%R.
  by rewrite /transport_plus /transport_scal !encode_decode.
- exists 1; split; [lra|]; intros x.
  change ((`| encode x |)%R <= 1 * (`| encode x |)%R); lra.
Qed.

Theorem transport_decode_linear :
  linear (decode : V -> TT) /\
  exists M : R, 0 < M /\ forall x : V, (`| (decode x : TT) |)%R <= M * (`| x |)%R.
Proof.
split.
- move=> a u v.
  change (decode (a *: u + v) =
    transport_plus (transport_scal a (decode u)) (decode v))%R.
  by rewrite /transport_plus /transport_scal !encode_decode.
- exists 1; split; [lra|]; intros x.
  change ((`| encode (decode x) |)%R <= 1 * (`| x |)%R).
  rewrite encode_decode; lra.
Qed.

(* Continuity of encode and decode, the form in which MathComp-Analysis
   consumes a bounded linear map (for instance diff_lin). *)
Lemma transport_encode_continuous : continuous (encode : TT -> V).
Proof.
move=> x U /nbhs_ballP [e e0 HU]; apply/nbhs_ballP; exists e => // y Hy.
by apply: HU; apply/transport_ball.
Qed.

Lemma transport_decode_continuous : continuous (decode : V -> TT).
Proof.
move=> x U /nbhs_ballP [e e0 HU]; apply/nbhs_ballP; exists e => // y Hy.
by apply: HU; apply/transport_ball; rewrite !encode_decode.
Qed.

End Transport.
