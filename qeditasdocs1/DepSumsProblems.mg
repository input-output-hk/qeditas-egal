(* Title "Dependent Sums and Simple Products of Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2y5gxoNPTwrc94awZ" *)

(*** Sigma X Y = {(x,y) | x in X, y in Y x} ***)
Definition Sigma : set -> (set -> set) -> set :=
fun X Y => \/_ x :e X, {pair x y|y :e Y x}.

(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

Theorem pair_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, pair x y :e Sigma_ x :e X, Y x.
Admitted.

Lemma Sigma_eta_proj0_proj1 : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z /\ proj0 z :e X /\ proj1 z :e Y (proj0 z).
Admitted.

Theorem proj_Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z.
Admitted.

Theorem proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.
Admitted.

Theorem proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).
Admitted.

Theorem pair_Sigma_E0 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> x :e X.
Admitted.

Theorem pair_Sigma_E1 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> y :e Y x.
Admitted.

Theorem Sigma_E : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) -> exists x :e X, exists y :e Y x, z = pair x y.
Admitted.

Theorem Sigma_Eq : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) <-> exists x :e X, exists y :e Y x, z = pair x y.
Admitted.

(*** Covariance of subsets of Sigmas ***)
Theorem Sigma_mon : forall X Y:set, X c= Y -> forall Z W:set->set, (forall x :e X, Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, W y.
Admitted.

Theorem Sigma_mon0 : forall X Y:set, X c= Y -> forall Z:set->set, (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, Z y.
Admitted.

Theorem Sigma_mon1 : forall X:set, forall Z W:set->set, (forall x, x :e X -> Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ x :e X, W x.
Admitted.

Theorem Sigma_Power_1 : forall X:set, X :e Power 1 -> forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Sigma_ x :e X, Y x) :e Power 1.
Admitted.

Definition setprod : set->set->set := fun X Y:set => Sigma_ x :e X, Y.

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

Theorem pair_setprod : forall X Y:set, forall (x :e X) (y :e Y), pair x y :e X :*: Y.
Admitted.

Theorem proj0_setprod : forall X Y:set, forall z :e X :*: Y, proj0 z :e X.
Admitted.

Theorem proj1_setprod : forall X Y:set, forall z :e X :*: Y, proj1 z :e Y.
Admitted.

Theorem setprod_mon : forall X Y:set, X c= Y -> forall Z W:set, Z c= W -> X :*: Z c= Y :*: W.
Admitted.

Theorem setprod_mon0 : forall X Y:set, X c= Y -> forall Z:set, X :*: Z c= Y :*: Z.
Admitted.

Theorem setprod_mon1 : forall X:set, forall Z W:set, Z c= W -> X :*: Z c= X :*: W.
Admitted.

Theorem pair_setprod_E0 : forall X Y x y:set, pair x y :e X :*: Y -> x :e X.
Admitted.

Theorem pair_setprod_E1 : forall X Y x y:set, pair x y :e X :*: Y -> y :e Y.
Admitted.
