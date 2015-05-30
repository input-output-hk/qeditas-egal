(* Title "Relations, Functions and Choice" *)
(* Author "Chad E. Brown" *)

(* Salt "4w4Ara2THhpx6TpZ" *)

Section RelnFunsPoly2.
Variable A B:SType.

Definition functionalreln : (A->B->prop)->prop := fun R => forall x:A, forall y y':B, R x y -> R x y' -> y = y'.

Definition injectivereln : (A->B->prop)->prop := fun R => forall y:B, forall x x':A, R x y -> R x' y -> x = x'.

Definition totalreln : (A->B->prop)->prop := fun R => forall x:A, exists y:B, R x y.

Definition surjectivereln : (A->B->prop)->prop := fun R => forall y:B, exists x:A, R x y.

(* Treasure "18ZCw2ufwLWvyEJoVbuAmhvVomQHeJngjV" *)
Theorem function_functional : forall f:A->B, functionalreln (fun (x:A) (y:B) => f x = y).
Admitted.

(* Treasure "18LHx2gfuA4YrKNKCgPU4Ddq7pg9K4QMBQ" *)
Theorem function_total : forall f:A->B, totalreln (fun (x:A) (y:B) => f x = y).
Admitted.

Definition injective : (A->B)->prop := fun f => forall x x':A, f x = f x' -> x = x'.

Definition surjective : (A->B)->prop := fun f => forall y:B, exists x:A, f x = y.

(* Treasure "1EMRHjeccFLDXqUZ4yYjJE62aNsXjdrMUc" *)
Theorem injective_fun_reln : forall f:A->B, injective f -> injectivereln (fun (x:A) (y:B) => f x = y).
Admitted.

(* Treasure "1EkNBzqQEYLSAT9jFLg2AauaJTY7pBwHpD" *)
Theorem surjective_fun_reln : forall f:A->B, surjective f -> surjectivereln (fun (x:A) (y:B) => f x = y).
Admitted.

End RelnFunsPoly2.

(** We include an epsilon operator (Eps) as a form of the axiom of choice. **)

Section Choice.
Variable A:SType.
Parameter Eps : (A->prop)->A.
Axiom EpsR : forall P:A->prop, forall x:A, P x -> P (Eps P).
End Choice.

Binder some , := Eps.

Section ChoiceThms.
Variable A:SType.

(* Treasure "1ELxniE3VKAjKLyN7me1ZtpBAczsumxnBd" *)
Theorem EpsR2 : forall P:A->prop, (exists x:A, P x) -> P (some x:A, P x).
Admitted.

(* Treasure "1Gx6ukMgQ3nZucoSWF7jopfCL1N22T87Nq" *)
Theorem InhEx : exists x:A, True.
Admitted.

(* Treasure "1FGZXkkDewZGGxSKsLLmRce6ikJT4qZg4X" *)
Theorem Inh : forall (P:prop), (forall x:A, P) -> P.
Admitted.

End ChoiceThms.

Section ChoiceExercises1.
Variable A:SType.

(* Treasure "1EfDMdmLzsSGwK55WornEYQ1MfABCGAhie" *)
Theorem EpsComplR : exists e:(A->prop)->A, forall P:A->prop, (exists x:A, ~P x) -> ~P (e P).
Admitted.

End ChoiceExercises1.

Section ChoiceExercises2.
Variable A B:SType.

(* Treasure "19rPCde7ShMMxKDErHidtMFFqFGngCBwHX" *)
Theorem Skolem : forall R:A->B->prop, totalreln A B R -> exists f:A->B, forall x:A, R x (f x).
Admitted.

(* Treasure "1LCjwPbLzDoMcsHXfZ8xTaXiLLz9JDaA94" *)
Theorem Eps2R : exists (e1:(A->B->prop)->A) (e2:(A->B->prop)->B), forall R:A->B->prop, (exists (x:A) (y:B), R x y) -> R (e1 R) (e2 R).
Admitted.

(* Treasure "1MschmJoDdkBEW952KhpXCQYbz8UezcQFb" *)
Theorem surj_inverse_ex : forall f:A->B, surjective A B f -> exists g:B->A, forall y:B, f (g y) = y.
Admitted.

(* Treasure "1DC2osiWsNrPYFrjwfNq5BgWCtPWo7tFcG" *)
Theorem inj_inverse_ex : forall f:A->B, injective A B f -> exists g:B->A, forall x:A, g (f x) = x.
Admitted.

End ChoiceExercises2.

Section ChoiceExercises3.
Variable A:SType.

(* Treasure "13r5zTBqvZNdafSSteD8K1sEFTA3i6aoES" *)
Theorem SurjectiveCantor : ~exists g:A->A->prop, surjective A (A->prop) g.
Admitted.

(* Treasure "13o2pLwKuJX4HNq2xW1CjppVpGocCriX97" *)
Theorem InjectiveCantor : forall h:(A->prop)->A, ~injective (A->prop) A h.
Admitted.

End ChoiceExercises3.
