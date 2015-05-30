(* Title "Dependent Sums and Simple Products of Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2y5gxoNPTwrc94awZ" *)

(*** Sigma X Y = {(x,y) | x in X, y in Y x} ***)
Definition Sigma : set -> (set -> set) -> set :=
fun X Y => \/_ x :e X, {pair x y|y :e Y x}.

(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

(* Treasure "1Q3dJNSRsXFEQkWzDB59JhNEeXCpVgKXhX" *)
Theorem pair_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, pair x y :e Sigma_ x :e X, Y x.
Admitted.

(* Treasure "15v3hrDgApb6BTmAmRJ6kLMjde85v695XF" *)
Lemma Sigma_eta_proj0_proj1 : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z /\ proj0 z :e X /\ proj1 z :e Y (proj0 z).
Admitted.

(* Treasure "1Fe7xZo746FQszefh2DXHscHTbEZMqPkAo" *)
Theorem proj_Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z.
Admitted.

(* Treasure "1CK7Wor96QMextHYmziw3FZu6NVrwaoQ7f" *)
Theorem proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.
Admitted.

(* Treasure "15TXzYP41rp7yZFj857FZTZ3YkSNyGsEts" *)
Theorem proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).
Admitted.

(* Treasure "1PPGW2so7qcu2Ct7D8uBw8W6v99rs618T7" *)
Theorem pair_Sigma_E0 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> x :e X.
Admitted.

(* Treasure "1HEdUz2YnYVxX8KxEXU4hq9YioYXBvBRRr" *)
Theorem pair_Sigma_E1 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> y :e Y x.
Admitted.

(* Treasure "13TQ2CLZXx2SHhMKfw5SJPCxnd2ck4Bg3R" *)
Theorem Sigma_E : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) -> exists x :e X, exists y :e Y x, z = pair x y.
Admitted.

(* Treasure "19dQY8Hevd7hLbGPondJV79nh114Y4UxVx" *)
Theorem Sigma_Eq : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) <-> exists x :e X, exists y :e Y x, z = pair x y.
Admitted.

(*** Covariance of subsets of Sigmas ***)
(* Treasure "1Gb91EerLiJ59qvxMCyk5VGkVzEjUtTNGn" *)
Theorem Sigma_mon : forall X Y:set, X c= Y -> forall Z W:set->set, (forall x :e X, Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, W y.
Admitted.

(* Treasure "1NxzSQXTktnPfRNhU4UovAWxSoqNb7cVv3" *)
Theorem Sigma_mon0 : forall X Y:set, X c= Y -> forall Z:set->set, (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, Z y.
Admitted.

(* Treasure "1LHC36pdabr2Y2jkof6J1ZRCsJAZDQeVBZ" *)
Theorem Sigma_mon1 : forall X:set, forall Z W:set->set, (forall x, x :e X -> Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ x :e X, W x.
Admitted.

(* Treasure "1JFa3yLY3FxMucyah6QkpjqQ8Pos3Jtno2" *)
Theorem Sigma_Power_1 : forall X:set, X :e Power 1 -> forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Sigma_ x :e X, Y x) :e Power 1.
Admitted.

Definition setprod : set->set->set := fun X Y:set => Sigma_ x :e X, Y.

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

(* Treasure "1PXBDmh7opbK5wJmiUxLxBNBZLp9XijCha" *)
Theorem pair_setprod : forall X Y:set, forall (x :e X) (y :e Y), pair x y :e X :*: Y.
Admitted.

(* Treasure "1CUZzZ9aGiSSsPbGeke4iaqQnDdDcJv1nW" *)
Theorem proj0_setprod : forall X Y:set, forall z :e X :*: Y, proj0 z :e X.
Admitted.

(* Treasure "14phuniVrhZsqc3uQ5arhe2XgfVGk292C6" *)
Theorem proj1_setprod : forall X Y:set, forall z :e X :*: Y, proj1 z :e Y.
Admitted.

(* Treasure "15eQFz9uibMjVoR5cg6hCmH26xqmGprsVD" *)
Theorem setprod_mon : forall X Y:set, X c= Y -> forall Z W:set, Z c= W -> X :*: Z c= Y :*: W.
Admitted.

(* Treasure "1GTQW14B14uYsBGiQbDrjzxTYshAhM1S5E" *)
Theorem setprod_mon0 : forall X Y:set, X c= Y -> forall Z:set, X :*: Z c= Y :*: Z.
Admitted.

(* Treasure "147QWhj3uq3grSnUCvRAJBhYRYMxAnSuZa" *)
Theorem setprod_mon1 : forall X:set, forall Z W:set, Z c= W -> X :*: Z c= X :*: W.
Admitted.

(* Treasure "1H8xQMttd622KpkEGHvM4PSDDyM1reQtTS" *)
Theorem pair_setprod_E0 : forall X Y x y:set, pair x y :e X :*: Y -> x :e X.
Admitted.

(* Treasure "1mex9DZE7VZ3w1f6gTKU9f1VziS3AtYsP" *)
Theorem pair_setprod_E1 : forall X Y x y:set, pair x y :e X :*: Y -> y :e Y.
Admitted.
