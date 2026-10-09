(* The endpoint behavior of the condition-number curve at fourth moment
   three: the statement condition_endpoints_statement of
   ConditionEndpoints, proved. Item R4 of phase 9.

   condition_endpoints (Condition/Endpoints) proves the four parts: the
   expansion (11) of alpha_C near C = 1, the leading term of (13) as
   C -> oo, and the note's (34) and (35) for C_star near alpha = 0 and
   alpha = 1/4. *)

From EllipsoidUniversality Require Import ConditionEndpoints.
From EllipsoidUniversality.Condition Require Import Endpoints.

Theorem condition_endpoints_theorem : condition_endpoints_statement.
Proof. exact condition_endpoints. Qed.
