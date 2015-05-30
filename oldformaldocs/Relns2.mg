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
let f x y y'.
assume H1:f x = y.
assume H2:f x = y'.
prove y = y'.
rewrite <- H1. exact H2.
Qed.

(* Treasure "18LHx2gfuA4YrKNKCgPU4Ddq7pg9K4QMBQ" *)
Theorem function_total : forall f:A->B, totalreln (fun (x:A) (y:B) => f x = y).
let f x.
prove exists y:B, f x = y.
witness (f x).
apply (eqI B).
Qed.

Definition injective : (A->B)->prop := fun f => forall x x':A, f x = f x' -> x = x'.

Definition surjective : (A->B)->prop := fun f => forall y:B, exists x:A, f x = y.

(* Treasure "1EMRHjeccFLDXqUZ4yYjJE62aNsXjdrMUc" *)
Theorem injective_fun_reln : forall f:A->B, injective f -> injectivereln (fun (x:A) (y:B) => f x = y).
let f.
assume H1: injective f.
let y x x'.
assume H2: f x = y.
assume H3: f x' = y.
prove x = x'.
apply (H1 x x').
prove f x = f x'.
rewrite H3. exact H2.
Qed.

(* Treasure "1EkNBzqQEYLSAT9jFLg2AauaJTY7pBwHpD" *)
Theorem surjective_fun_reln : forall f:A->B, surjective f -> surjectivereln (fun (x:A) (y:B) => f x = y).
let f. assume H1:surjective f.
let y.
prove exists x:A, f x = y.
exact (H1 y).
Qed.

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
exact (fun P u => u (P (some x:A, P x)) (fun x v => EpsR A P x v)).
Qed.

(* Treasure "1Gx6ukMgQ3nZucoSWF7jopfCL1N22T87Nq" *)
Theorem InhEx : exists x:A, True.
exact (exI A (fun _ => True) (some x:A, True) TrueI).
Qed.

(* Treasure "1FGZXkkDewZGGxSKsLLmRce6ikJT4qZg4X" *)
Theorem Inh : forall (P:prop), (forall x:A, P) -> P.
exact (fun P u => u (some x:A, True)).
Qed.

End ChoiceThms.

Section ChoiceExercises1.
Variable A:SType.

(* Treasure "1EfDMdmLzsSGwK55WornEYQ1MfABCGAhie" *)
Theorem EpsComplR : exists e:(A->prop)->A, forall P:A->prop, (exists x:A, ~P x) -> ~P (e P).
witness (fun P:A->prop => some x:A, ~P x).
exact (fun P u => EpsR2 A (fun x => ~P x) u).
Qed.

End ChoiceExercises1.

Section ChoiceExercises2.
Variable A B:SType.

(* Treasure "19rPCde7ShMMxKDErHidtMFFqFGngCBwHX" *)
Theorem Skolem : forall R:A->B->prop, totalreln A B R -> exists f:A->B, forall x:A, R x (f x).
let R.
assume u: forall x:A, exists y:B, R x y.
witness (fun x:A => some y:B, R x y).
let x.
exact (EpsR2 B (R x) (u x)).
Qed.

(* Treasure "1LCjwPbLzDoMcsHXfZ8xTaXiLLz9JDaA94" *)
Theorem Eps2R : exists (e1:(A->B->prop)->A) (e2:(A->B->prop)->B), forall R:A->B->prop, (exists (x:A) (y:B), R x y) -> R (e1 R) (e2 R).
set e1 := fun R:A->B->prop => some x:A, exists y:B, R x y.
set e2 := fun R:A->B->prop => some y:B, R (e1 R) y.
witness e1. witness e2.
let R:A->B->prop.
assume u: exists (x:A) (y:B), R x y.
claim L1: exists y:B, R (e1 R) y.
{ exact (EpsR2 A (fun x => exists y:B, R x y) u). }
exact (EpsR2 B (fun y => R (e1 R) y) L1).
Qed.

(* Treasure "1MschmJoDdkBEW952KhpXCQYbz8UezcQFb" *)
Theorem surj_inverse_ex : forall f:A->B, surjective A B f -> exists g:B->A, forall y:B, f (g y) = y.
let f.
assume H1: surjective A B f.
witness (fun y:B => some x:A, f x = y).
prove forall y:B, f (some x:A, f x = y) = y.
let y.
exact (EpsR2 A (fun x => f x = y) (H1 y)).
Qed.

(* Treasure "1DC2osiWsNrPYFrjwfNq5BgWCtPWo7tFcG" *)
Theorem inj_inverse_ex : forall f:A->B, injective A B f -> exists g:B->A, forall x:A, g (f x) = x.
let f.
assume H1: injective A B f.
witness (fun y:B => some x:A, f x = y).
prove forall x:A, (some z:A, f z = f x) = x.
let x.
apply H1.
prove f (some z:A, f z = f x) = f x.
claim L1: exists z:A, f z = f x.
{
  witness x.
  exact (eqI B (f x)).
}
exact (EpsR2 A (fun z => f z = f x) L1).
Qed.

End ChoiceExercises2.

Section ChoiceExercises3.
Variable A:SType.

(* Treasure "13r5zTBqvZNdafSSteD8K1sEFTA3i6aoES" *)
Theorem SurjectiveCantor : ~exists g:A->A->prop, surjective A (A->prop) g.
assume H: exists g:A->A->prop, surjective A (A->prop) g.
apply H.
let g.
assume H1: forall f:A->prop, exists x:A, g x = f.
apply (H1 (fun x:A => ~g x x)).
let x.
assume H2: g x = fun x:A => ~g x x.
claim L1: g x x <-> ~g x x.
{
  rewrite H2 at 1.
  prove ~g x x <-> ~g x x.
  exact (iff_refl (~g x x)).
}
exact (iff_circuit (g x x) L1).
Qed.

(* Treasure "13o2pLwKuJX4HNq2xW1CjppVpGocCriX97" *)
Theorem InjectiveCantor : forall h:(A->prop)->A, ~injective (A->prop) A h.
let h.
assume H1: injective (A->prop) A h.
apply (inj_inverse_ex (A->prop) A h H1).
let g.
assume H2: forall p:A->prop, g (h p) = p.
claim L1: surjective A (A->prop) g.
{
  let p. witness (h p). exact (H2 p).
}
apply SurjectiveCantor.
witness g.
exact L1.
Qed.

End ChoiceExercises3.
