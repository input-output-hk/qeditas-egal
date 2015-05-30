(* Title "Ordered Pairs as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "3KhxsZskpyxtXKgXx" *)

Definition pair : set -> set -> set := fun X Y => X :+: Y.

Theorem pair_0_0 : pair 0 0 = 0.
Admitted.

Theorem pair_1_0_1 : pair 1 0 = 1.
Admitted.

Theorem pair_1_1_2 : pair 1 1 = 2.
Admitted.

Theorem nat_pair1_ordsucc : forall n:set, nat_p n -> pair 1 n = ordsucc n.
Admitted.

Definition proj0 : set -> set := fun Z => {Unj z|z :e Z, exists x:set, Inj0 x = z}.

Definition proj1 : set -> set := fun Z => {Unj z|z :e Z, exists y:set, Inj1 y = z}.

Theorem Inj0_pair_0_eq : Inj0 = pair 0.
Admitted.

Theorem Inj1_pair_1_eq : Inj1 = pair 1.
Admitted.

Theorem pairI0 : forall X Y x, x :e X -> pair 0 x :e pair X Y.
Admitted.

Theorem pairI1 : forall X Y y, y :e Y -> pair 1 y :e pair X Y.
Admitted.

Theorem pairE : forall X Y z, z :e pair X Y -> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
Admitted.

Theorem pairE0 : forall X Y x, pair 0 x :e pair X Y -> x :e X.
Admitted.

Theorem pairE1 : forall X Y y, pair 1 y :e pair X Y -> y :e Y.
Admitted.

Theorem pairEq : forall X Y z, z :e pair X Y <-> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
Admitted.

Theorem pairSubq : forall X Y W Z, X c= W -> Y c= Z -> pair X Y c= pair W Z.
Admitted.

Theorem proj0I : forall w u:set, pair 0 u :e w -> u :e proj0 w.
Admitted.

Theorem proj0E : forall w u:set, u :e proj0 w -> pair 0 u :e w.
Admitted.

Theorem proj1I : forall w u:set, pair 1 u :e w -> u :e proj1 w.
Admitted.

Theorem proj1E : forall w u:set, u :e proj1 w -> pair 1 u :e w.
Admitted.

Theorem proj0_pair_eq : forall X Y:set, proj0 (pair X Y) = X.
Admitted.

Theorem proj1_pair_eq : forall X Y:set, proj1 (pair X Y) = Y.
Admitted.

Theorem pair_inj : forall x y w z:set, pair x y = pair w z -> x = w /\ y = z.
Admitted.

Theorem pair_eta_Subq_proj : forall w, pair (proj0 w) (proj1 w) c= w.
Admitted.
