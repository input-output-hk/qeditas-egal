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

(* Treasure "1DsJZkAjGZGjggQWve8pFsN28wVg3j5mDu" *)
Theorem ZF_closed_I : forall U,
 Union_closed U ->
 Power_closed U ->
 Repl_closed U ->
 ZF_closed U.
Admitted.

(* Treasure "1PyQmhMNwCZNZwjX84YXABmgABM4bFvSiM" *)
Theorem ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.
Admitted.

(* Treasure "12zcSHLyVnDdy3n3LLcZvzZeNY1ZXBrCfo" *)
Theorem ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.
Admitted.

(* Treasure "1Mp9aDNdXyAskcNuQM5xpmaM2DEnWxWsG5" *)
Theorem ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.
Admitted.

(* Treasure "18eW7WFW3SASnf18fYKpoiEiQwtQFrccwN" *)
Theorem ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.
Admitted.

(* Treasure "18YRAAuJQF8idQh4s24tdgEwbVevTj6htU" *)
Theorem ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.
Admitted.

(* Treasure "1FGwGgAxu6ZYw7Bzd89uXDAAyuddAArDat" *)
Theorem ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.
Admitted.

(* Treasure "19Cwn4VLwH6xKGjicNXrJgcnqLKpNzdgK1" *)
Theorem ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.
Admitted.

(* Treasure "1Aeuo28gzUEmXogq3X1vWU3ZrF9F7AJu9j" *)
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

(* Treasure "1JUy3T5RBcd7EqyeH1bVk6AS3YZ5hMWHL2" *)
Theorem UnivOfEmptyInfinite : InfiniteSet (UnivOf Empty).
Admitted.

(* Treasure "1DVxAvJT2LnPiY11njJ7744cpGVkgHBKRZ" *)
Theorem nat_p_UnivOf_Empty : forall n:set, nat_p n -> n :e UnivOf Empty.
Admitted.

(* Unicode omega "3c9" *)
Definition omega : set := {n :e UnivOf Empty|nat_p n}.

(* Treasure "1McazTdmkVE9tJzASWquhSyy2vWskdUS2B" *)
Theorem omega_nat_p : forall n :e omega, nat_p n.
Admitted.

(* Treasure "192B8XjoorT55zN5HuNfcq8SoQsnS23TqT" *)
Theorem nat_p_omega : forall n:set, nat_p n -> n :e omega.
Admitted.

Definition ZF_Model : set->prop := fun U:set => ZF_closed U /\ TransSet U /\ omega :e U.

(* Treasure "1LAwVndmsJw3uCjTka4xwRcMhwM3Fg3Bby" *)
Theorem ZF_Model_UnivOf_omega : ZF_Model (UnivOf omega).
Admitted.
