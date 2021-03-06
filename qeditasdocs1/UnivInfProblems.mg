(* Title "Universes and Infinity" *)
(* Author "Chad E. Brown" *)

(* Salt "3GET5N85aHveg5ZgU" *)

Definition TransSet : set->prop := fun U:set => forall X:set, X :e U -> X c= U.

Definition Union_closed : set->prop := fun U:set => forall X:set, X :e U -> Union X :e U.
Definition Power_closed : set->prop := fun U:set => forall X:set, X :e U -> Power X :e U.
Definition Repl_closed : set->prop := fun U:set => forall X:set, X :e U -> forall F:set->set,
   (forall x:set, x :e X -> F x :e U) -> {F x|x :e X} :e U.
Definition ZF_closed : set->prop := fun U:set =>
   Union_closed U
/\ Power_closed U
/\ Repl_closed U.

Theorem ZF_closed_I : forall U,
 Union_closed U ->
 Power_closed U ->
 Repl_closed U ->
 ZF_closed U.
Admitted.

Theorem ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.
Admitted.

Theorem ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.
Admitted.

Theorem ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.
Admitted.

Theorem ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.
Admitted.

Theorem ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.
Admitted.

Theorem ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.
Admitted.

Theorem ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.
Admitted.

Theorem ZF_ordsucc_closed : forall U, ZF_closed U ->
  forall x :e U, ordsucc x :e U.
Admitted.

Parameter UnivOf : set->set.

Axiom UnivOf_In : forall N:set, N :e UnivOf N.

Axiom UnivOf_TransSet : forall N:set, TransSet (UnivOf N).

Axiom UnivOf_ZF_closed : forall N:set, ZF_closed (UnivOf N).

Axiom UnivOf_Min : forall N U:set, N :e U
  -> TransSet U
  -> ZF_closed U
  -> UnivOf N c= U.

Definition InfiniteSet : set->prop := fun X:set =>
exists f:set->set, (forall x :e X, f x :e X) /\ (exists z :e X, forall x :e X, f x <> z) /\ (forall x y :e X, f x = f y -> x = y).

Definition FiniteSet : set->prop := fun X:set => ~InfiniteSet X.

Theorem UnivOfEmptyInfinite : InfiniteSet (UnivOf Empty).
Admitted.

Theorem nat_p_UnivOf_Empty : forall n:set, nat_p n -> n :e UnivOf Empty.
Admitted.

(* Unicode omega "3c9" *)
Definition omega : set := {n :e UnivOf Empty|nat_p n}.

Theorem omega_nat_p : forall n :e omega, nat_p n.
Admitted.

Theorem nat_p_omega : forall n:set, nat_p n -> n :e omega.
Admitted.

Definition ZF_Model : set->prop := fun U:set => ZF_closed U /\ TransSet U /\ omega :e U.

Theorem ZF_Model_UnivOf_omega : ZF_Model (UnivOf omega).
Admitted.
