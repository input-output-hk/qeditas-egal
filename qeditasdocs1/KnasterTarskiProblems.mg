(* Title "Knaster-Tarski Fixed Points" *)
(* Author "Chad E. Brown" *)

(* Salt "rV9oQDrt79Whisxz" *)

(*** Chad E Brown ***)
(*** Aug 2010 - June 2011 - September 2011 (-nois version) - March 2013 ***)

(*** Definitions of logical constants. ***)

Section Poly1_fpdef.
Variable A:SType.

Variable F:((A->prop)->A->prop).
Hypothesis Fmon:forall p q:A->prop, p c= q -> F p c= F q.

Definition lfp : A->prop :=
fun z => forall p:A -> prop, F p c= p -> p z.

Definition gfp : A->prop :=
fun z => exists p:A -> prop, p c= F p /\ p z.

Section lfp.

Let Y := lfp.

Theorem lfp_t : 
(F Y = Y) /\ forall X:A -> prop, F X = X -> Y c= X.
claim L1 : F Y c= Y.
{
  prove forall z:A, F Y z -> forall p:A->prop, F p c= p -> p z.
  let z.
  assume H1: F Y z.
  let p.
  assume H2: F p c= p.
  apply H2.
  prove F p z.
  apply (Fmon Y p).
  - prove Y c= p. let u. assume H3: Y u. exact (H3 p H2).
  - prove F Y z. exact H1.
}
apply andI.
- prove (F Y = Y). apply (pred_ext A).
  + prove F Y c= Y. exact L1.
  + prove Y c= F Y. let z. assume H1: Y z.
    apply (H1 (F Y)).
    prove F (F Y) c= F Y.
    exact (Fmon (F Y) Y L1).
- prove forall X : A -> prop, F X = X -> Y c= X.
  let X. assume H1: F X = X. let z. assume H2: Y z.
  claim L2 : F X c= X.
  {
    rewrite H1. exact (fun z H2 => H2).
  }
  prove X z.
  exact (H2 X L2).
Qed.  

End lfp.

Section gfp.

Let Y := gfp.

Theorem gfp_t :
(F Y = Y) /\ forall X:A -> prop, F X = X -> X c= Y.
Admitted.

End gfp.

Theorem lfpe_t : exists Y:A->prop, (F Y = Y) /\ forall X:A -> prop, F X = X -> Y c= X.
Admitted.

Theorem gfpe_t : exists Y:A->prop, (F Y = Y) /\ forall X:A -> prop, F X = X -> X c= Y.
Admitted.

Theorem fpe_t : exists Y:A->prop, (F Y = Y).
Admitted.

End Poly1_fpdef.

Section Poly2_fpdef.
Variable A B:SType.

Variable F : (A->B->prop) -> (A->B->prop).
Hypothesis Fmon:forall R S:A->B->prop, R c= S -> F R c= F S.

Definition lfp2 : A->B->prop :=
  fun z1 z2 => forall p:A->B->prop, F p c= p -> p z1 z2.

Definition gfp2 : A->B->prop :=
  fun z1 z2 => exists p:A->B->prop, p c= F p /\ p z1 z2.

Section lfp2.

Let Y := lfp2.

Theorem lfp2_t : 
(F Y = Y) /\ forall X:A->B->prop, F X = X -> Y c= X.
Admitted.

End lfp2.

Section gfp2.

Let Y := gfp2.

Theorem gfp2_t : (F Y = Y) /\ forall X:A->B->prop, F X = X -> X c= Y.
Admitted.

End gfp2.

Theorem lfp2e_t :
exists Y:A->B->prop, (F Y = Y) /\ forall X:A->B->prop, F X = X -> Y c= X.
Admitted.

Theorem gfp2e_t :
exists Y:A->B->prop, (F Y = Y) /\ forall X:A->B->prop, F X = X -> X c= Y.
Admitted.

Theorem fp2 :
exists Y:A->B->prop, (F Y = Y).
Admitted.

End Poly2_fpdef.

Section Poly1_trans_clos.

Variable A:SType.

Variable R:A->A->prop.

(*** Transitive Closure ***)
Definition trans_clos : A->A->prop :=
 lfp2 A A (fun (Q:A->A->prop) (x z:A) => R x z \/ exists y:A, Q x y /\ Q y z).

Let F : (A->A->prop)->A->A->prop := (fun Q:A->A->prop => fun (x z:A) => R x z \/ exists y:A, Q x y /\ Q y z).

Theorem trans_clos_monotone :
 forall Q1 Q2:A->A->prop, Q1 c= Q2 -> F Q1 c= F Q2.
Admitted.

Theorem trans_clos_sub : R c= trans_clos.
Admitted.

Theorem trans_clos_trans : transitive A trans_clos.
Admitted.

Theorem trans_clos_ind : forall Q:A->A->prop,
 R c= Q
 ->
 transitive A Q
 ->
 forall x z:A, trans_clos x z -> Q x z.
Admitted.

Theorem trans_clos_ind_r : forall P:A->prop,
 (forall x y:A, P x -> R x y -> P y)
 ->
 forall x y:A, trans_clos x y -> (forall y:A, R x y -> P y) -> P y.
Admitted.

Theorem trans_clos_ind_l : forall P:A->prop,
 (forall x y:A, P y -> R x y -> P x)
 ->
 forall x y:A, trans_clos x y -> (forall x:A, R x y -> P x) ->  P x.
Admitted.

Theorem trans_clos_inv_r : forall x y:A,
  trans_clos x y -> R x y \/ exists w:A, trans_clos x w /\ R w y.
Admitted.

Theorem trans_clos_inv_l : forall x y:A,
  trans_clos x y -> R x y \/ exists z:A, R x z /\ trans_clos z y.
Admitted.

End Poly1_trans_clos.
