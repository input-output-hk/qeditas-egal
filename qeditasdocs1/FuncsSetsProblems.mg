(* Title "Functions as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2VZUMZGBmJfVam7ZU" *)

(*** lam X F = {(x,y) | x :e X, y :e F x} = \/_{x :e X} {(x,y) | y :e (F x)} = Sigma X F ***)
Definition lam : set -> (set -> set) -> set := Sigma.

(***  ap f x = {proj1 z | z :e f,  exists y, z = pair x y}} ***)
Definition ap : set -> set -> set := fun f x => {proj1 z|z :e f, exists y:set, z = pair x y}.

Notation SetImplicitOp ap.
Notation SetLam lam.

Theorem lamI : forall X:set, forall F:set->set, forall x :e X, forall y :e F x, pair x y :e fun x :e X => F x.
Admitted.

Theorem lamE : forall X:set, forall F:set->set, forall z:set, z :e (fun x :e X => F x) -> exists x :e X, exists y :e F x, z = pair x y.
Admitted.

Theorem lamEq : forall X:set, forall F:set->set, forall z, z :e (fun x :e X => F x) <-> exists x :e X, exists y :e F x, z = pair x y.
Admitted.

Theorem apI : forall f x y, pair x y :e f -> y :e f x.
Admitted.

Theorem apE : forall f x y, y :e f x -> pair x y :e f.
Admitted.

Theorem apEq : forall f x y, y :e f x <-> pair x y :e f.
Admitted.

Theorem beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.
Admitted.

Theorem beta0 : forall X:set, forall F:set -> set, forall x:set, x /:e X -> (fun x :e X => F x) x = 0.
Admitted.

Theorem proj0_ap_0 : forall u, proj0 u = u 0.
Admitted.

Theorem proj1_ap_1 : forall u, proj1 u = u 1.
Admitted.

Theorem pair_ap_0 : forall x y:set, (pair x y) 0 = x.
Admitted.

Theorem pair_ap_1 : forall x y:set, (pair x y) 1 = y.
Admitted.

Theorem pair_ap_n2 : forall x y i:set, i /:e 2 -> (pair x y) i = 0.
Admitted.

Theorem pair_eta_Subq : forall w, pair (w 0) (w 1) c= w.
Admitted.

Theorem ap0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 0) :e X.
Admitted.

Theorem ap1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 1) :e (Y (z 0)).
Admitted.

Theorem Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (z 0) (z 1) = z.
Admitted.

Definition pair_p:set->prop
:= fun u:set => pair (u 0) (u 1) = u.

Theorem pair_p_I : forall x y, pair_p (pair x y).
Admitted.

Theorem pair_p_I2 : forall w, (forall u :e w, pair_p u /\ u 0 :e 2) -> pair_p w.
Admitted.

Theorem pair_p_In_ap : forall w f, pair_p w -> w :e f -> w 1 :e ap f (w 0).
Admitted.

Definition tuple_p : set->set->prop :=
fun n u => forall z :e u, exists i :e n, exists x:set, z = pair i x.

Theorem pair_p_tuple2 : pair_p = tuple_p 2.
Admitted.

Theorem tuple_p_2_tuple : forall x y:set, tuple_p 2 (x,y).
Admitted.

Theorem tuple_p_3_tuple : forall x y z:set, tuple_p 3 (x,y,z).
Admitted.

Theorem tuple_p_4_tuple : forall x y z w:set, tuple_p 4 (x,y,z,w).
Admitted.

Theorem tuple_pair : forall x y:set, pair x y = (x,y).
Admitted.
