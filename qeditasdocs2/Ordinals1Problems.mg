(* Title "Introduction to Ordinals" *)
(* Author "Chad E. Brown" *)

(* Salt "tgrf8cu2HQz7s5oc" *)

(* Unicode alpha "3b1" *)
(* Unicode beta "3b2" *)
(* Unicode gamma "3b3" *)
(* Unicode delta "3b4" *)

Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Theorem ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.
Admitted.

Theorem ordinal_In_TransSet : forall alpha:set, ordinal alpha -> forall beta :e alpha, TransSet beta.
Admitted.

Theorem ordinal_Empty : ordinal Empty.
Admitted.

Theorem ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.
Admitted.

Theorem ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.
Admitted.

Theorem TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).
Admitted.

Theorem ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).
Admitted.

Theorem nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
Admitted.

Theorem omega_TransSet : TransSet omega.
Admitted.

Theorem omega_ordinal : ordinal omega.
Admitted.

Theorem TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.
Admitted.

Theorem ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.
Admitted.

Theorem ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
Admitted.

Theorem ordinal_trichotomy : forall alpha beta:set,
 ordinal alpha -> ordinal beta -> exactly1of3 (alpha :e beta) (alpha = beta) (beta :e alpha).
Admitted.

Theorem ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.
Admitted.

Theorem ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.
Admitted.
