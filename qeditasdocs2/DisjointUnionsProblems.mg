(* Title "Disjoint Unions" *)
(* Author "Chad E. Brown" *)

(* Salt "3HmtMxzQo7ZHzs1du" *)

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec (fun X f => {0} :\/: {f x|x :e X}).

Theorem Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
Admitted.

Theorem Inj1I1 : forall X:set, 0 :e Inj1 X.
Admitted.

Theorem Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
Admitted.

Theorem Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
Admitted.

Theorem Inj1NE1 : forall x:set, Inj1 x <> 0.
Admitted.

Theorem Inj1NE2 : forall x:set, Inj1 x /:e {0}.
Admitted.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

Theorem Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
Admitted.

Theorem Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.
Admitted.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec (fun X f => {f x|x :e X :\: {0}}).

Theorem Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
Admitted.

Theorem Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
Admitted.

Theorem Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
Admitted.

Theorem Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
Admitted.

Theorem Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
Admitted.

Theorem Inj0_0 : Inj0 0 = 0.
Admitted.

Theorem Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.
Admitted.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.

(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

Theorem Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
Admitted.

Theorem Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
Admitted.

Theorem setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).
Admitted.

Theorem Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
Admitted.

Theorem Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
Admitted.

Theorem nat_setsum1_ordsucc : forall n:set, nat_p n -> 1 :+: n = ordsucc n.
Admitted.

Theorem setsum_0_0 : 0 :+: 0 = 0.
Admitted.

Theorem setsum_1_0_1 : 1 :+: 0 = 1.
Admitted.

Theorem setsum_1_1_2 : 1 :+: 1 = 2.
Admitted.

Theorem setsum_mon : forall X Y W Z, X c= W -> Y c= Z -> X :+: Y c= W :+: Z.
Admitted.
