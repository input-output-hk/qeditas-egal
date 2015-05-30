(* Title "Natural Numbers as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2nPDtwmgvfam3ctmf" *)

Definition ordsucc : set->set := fun x:set => x :\/: {x}.

Lemma ordsuccI1 : forall x:set, x c= ordsucc x.
Admitted.

Lemma ordsuccI2 : forall x:set, x :e ordsucc x.
Admitted.

Lemma ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
Admitted.

Notation Nat Empty ordsucc.

Lemma neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
Admitted.

Lemma neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
Admitted.

Lemma ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
Admitted.

Lemma ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.
Admitted.

Lemma In_0_1 : 0 :e 1.
Admitted.

Lemma In_1_2 : 1 :e 2.
Admitted.

Lemma In_0_2 : 0 :e 2.
Admitted.

Lemma neq_0_1 : 0 <> 1.
Admitted.

Lemma neq_1_0 : 1 <> 0.
Admitted.

Lemma neq_0_2 : 0 <> 2.
Admitted.

Lemma neq_2_0 : 2 <> 0.
Admitted.

Lemma neq_1_2 : 1 <> 2.
Admitted.

Lemma neq_2_1 : 2 <> 1.
Admitted.

Lemma nIn_0_0 : 0 /:e 0.
Admitted.

Lemma nIn_1_0 : 1 /:e 0.
Admitted.

Lemma nIn_2_0 : 2 /:e 0.
Admitted.

Lemma nIn_1_1 : 1 /:e 1.
Admitted.

Lemma nIn_2_1 : 2 /:e 1.
Admitted.

Lemma nIn_2_2 : 2 /:e 2.
Admitted.

Lemma Subq_0_0 : 0 c= 0.
Admitted.

Lemma Subq_0_1 : 0 c= 1.
Admitted.

Lemma Subq_0_2 : 0 c= 2.
Admitted.

Lemma nSubq_1_0 : 1 /c= 0.
Admitted.

Lemma Subq_1_1 : 1 c= 1.
Admitted.

Lemma Subq_1_2 : 1 c= 2.
Admitted.

Lemma nSubq_2_0 : 2 /c= 0.
Admitted.

Lemma nSubq_2_1 : 2 /c= 1.
Admitted.

Lemma Subq_2_2 : 2 c= 2.
Admitted.

Lemma Subq_1_Sing0 : 1 c= {0}.
Admitted.

Lemma Subq_Sing0_1 : {0} c= 1.
Admitted.

Lemma eq_1_Sing0 : 1 = {0}.
Admitted.

Lemma Subq_2_UPair01 : 2 c= {0,1}.
Admitted.

Lemma Subq_UPair01_2 : {0,1} c= 2.
Admitted.

Lemma eq_2_UPair01 : 2 = {0,1}.
Admitted.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

Lemma nat_0 : nat_p 0.
Admitted.

Lemma nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
Admitted.

Lemma nat_1 : nat_p 1.
Admitted.

Lemma nat_2 : nat_p 2.
Admitted.

Lemma nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
Admitted.

Lemma nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
Admitted.

Lemma nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
Admitted.

Lemma nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
Admitted.

Lemma nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
Admitted.

Lemma nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
Admitted.

Lemma nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
Admitted.

Lemma nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.
Admitted.

Lemma Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.
Admitted.
