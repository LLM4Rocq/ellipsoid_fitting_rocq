(* Stdlib's real functions and order at Stdlib's R, as equalities of
   functions with their MathComp counterparts, so that rewrite can use them
   under binders. The pointwise versions are RleP, RltP, RabsE, RsqrtE,
   RpowE, INRE, RmaxE, RminE, RinvE and RdistE of Rstruct, and RexpE and
   RlnE of Rstruct_topology. The operations + - * / and the constants 0 and
   1 need no lemma: at Stdlib's R, MathComp's are Stdlib's up to unfolding.

   To state a library result at Stdlib's R, rewrite with these lemmas, from
   right to left, the Stdlib forms of the paper into the MathComp forms of
   the library.

   finite_sum_seqE reads the paper's finite_sum over List.seq 0 n
   (Soft.Definitions) as MathComp's \sum_(i < n). *)
From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum boolp reals.
From mathcomp Require Import Rstruct Rstruct_topology sequences exp.
From EllipsoidFitting Require Import Soft.Definitions.
Import GRing.Theory Num.Theory.

Lemma RleF : Rle = (fun x y : R => (x <= y)%R).
Proof. by apply/funext => x; apply/funext => y; apply/propext; split => /RleP. Qed.

Lemma RltF : Rlt = (fun x y : R => (x < y)%R).
Proof. by apply/funext => x; apply/funext => y; apply/propext; split => /RltP. Qed.

Lemma RabsF : Rabs = (fun x : R => `|x|%R).
Proof. by apply/funext => x; rewrite RabsE. Qed.

Lemma sqrtF : sqrt = (fun x : R => Num.sqrt x).
Proof. by apply/funext => x; rewrite RsqrtE. Qed.

Lemma powF : pow = (fun (x : R) (n : nat) => (x ^+ n)%R).
Proof. by apply/funext => x; apply/funext => n; rewrite RpowE. Qed.

Lemma INRF : INR = (fun n : nat => (n%:R : R)%R).
Proof. by apply/funext => n; rewrite INRE. Qed.

Lemma RmaxF : Rmax = (fun x y : R => Num.max x y).
Proof. by apply/funext => x; apply/funext => y; rewrite RmaxE. Qed.

Lemma RminF : Rmin = (fun x y : R => Num.min x y).
Proof. by apply/funext => x; apply/funext => y; rewrite RminE. Qed.

Lemma RinvF : Rinv = (fun x : R => x^-1%R).
Proof. by apply/funext => x; rewrite RinvE. Qed.

Lemma RdistF : Rdist = (fun x y : R => `|x - y|%R).
Proof. by apply/funext => x; apply/funext => y; rewrite RdistE. Qed.

Lemma expF : Rtrigo_def.exp = (fun x : R => expR x).
Proof. by apply/funext => x; rewrite RexpE. Qed.

Lemma lnF : Rpower.ln = (fun x : R => @exp.ln (R : realType) x).
Proof. by apply/funext => x; rewrite RlnE. Qed.

Lemma finite_sum_seq_addE k n (f : nat -> R) :
  finite_sum f (List.seq k n) = (\sum_(i < n) f (k + i)%N)%R.
Proof.
elim: n k => [|n IH] k; first by rewrite big_ord0.
rewrite big_ord_recl /= addn0 IH.
by congr (_ + _)%R; apply: eq_bigr => i _; rewrite addSnnS.
Qed.

Lemma finite_sum_seqE n (f : nat -> R) :
  finite_sum f (List.seq 0 n) = (\sum_(i < n) f i)%R.
Proof. by rewrite finite_sum_seq_addE. Qed.
