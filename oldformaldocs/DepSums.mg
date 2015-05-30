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
let X Y x.
assume Hx: x :e X.
let y.
assume Hy: y :e Y x.
prove pair x y :e \/_ x :e X, {pair x y|y :e Y x}.
apply (famunionI X (fun x => {pair x y|y :e Y x}) x (pair x y)).
- prove x :e X.
  exact Hx.
- prove pair x y :e {pair x y|y :e Y x}.
  apply ReplI.
  prove y :e Y x.
  exact Hy.
Qed.

(* Treasure "15v3hrDgApb6BTmAmRJ6kLMjde85v695XF" *)
Lemma Sigma_eta_proj0_proj1 : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z /\ proj0 z :e X /\ proj1 z :e Y (proj0 z).
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
claim L1: exists x :e X, z :e {pair x y|y :e Y x}.
{ exact (famunionE X (fun x => {pair x y|y :e Y x}) z H1). }
apply (exandE set (fun x => x :e X) (fun x => z :e {pair x y|y :e Y x}) L1).
let x.
assume H2: x :e X.
assume H3: z :e {pair x y|y :e Y x}.
apply (ReplE2 (Y x) (pair x) z H3).
let y.
assume H4: y :e Y x.
assume H5: z = pair x y.
rewrite H5.
prove pair (proj0 (pair x y)) (proj1 (pair x y)) = pair x y /\ proj0 (pair x y) :e X /\ proj1 (pair x y) :e Y (proj0 (pair x y)).
rewrite proj0_pair_eq.
prove pair x (proj1 (pair x y)) = pair x y /\ x :e X /\ proj1 (pair x y) :e Y x.
rewrite proj1_pair_eq.
prove pair x y = pair x y /\ x :e X /\ y :e Y x.
apply and3I.
- prove pair x y = pair x y.
  apply (eqI set).
- prove x :e X.
  exact H2.
- prove y :e Y x.
  exact H4.
Qed.

(* Treasure "1Fe7xZo746FQszefh2DXHscHTbEZMqPkAo" *)
Theorem proj_Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z.
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z H1)).
assume H2 _ _.
exact H2.
Qed.

(* Treasure "1CK7Wor96QMextHYmziw3FZu6NVrwaoQ7f" *)
Theorem proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z H1)).
assume _ H2 _.
exact H2.
Qed.

(* Treasure "15TXzYP41rp7yZFj857FZTZ3YkSNyGsEts" *)
Theorem proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z H1)).
assume _ _ H2.
exact H2.
Qed.

(* Treasure "1PPGW2so7qcu2Ct7D8uBw8W6v99rs618T7" *)
Theorem pair_Sigma_E0 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> x :e X.
let X Y x y.
assume H1: pair x y :e Sigma_ x :e X, Y x.
prove x :e X.
rewrite <- (proj0_pair_eq x y).
prove proj0 (pair x y) :e X.
exact (proj0_Sigma X Y (pair x y) H1).
Qed.

(* Treasure "1HEdUz2YnYVxX8KxEXU4hq9YioYXBvBRRr" *)
Theorem pair_Sigma_E1 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> y :e Y x.
let X Y x y.
assume H1: pair x y :e Sigma_ x :e X, Y x.
prove y :e Y x.
rewrite <- (proj0_pair_eq x y).
prove y :e Y (proj0 (pair x y)).
rewrite <- (proj1_pair_eq x y) at 1.
prove proj1 (pair x y) :e Y (proj0 (pair x y)).
exact (proj1_Sigma X Y (pair x y) H1).
Qed.

(* Treasure "13TQ2CLZXx2SHhMKfw5SJPCxnd2ck4Bg3R" *)
Theorem Sigma_E : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) -> exists x :e X, exists y :e Y x, z = pair x y.
let X Y z.
assume Hz: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z Hz)).
assume H1: pair (proj0 z) (proj1 z) = z.
assume H2: proj0 z :e X.
assume H3: proj1 z :e Y (proj0 z).
witness (proj0 z).
apply andI.
- prove proj0 z :e X. exact H2.
- witness (proj1 z).
  apply andI.
  + prove proj1 z :e Y (proj0 z). exact H3.
  + prove z = pair (proj0 z) (proj1 z).
    apply (eq_sym set).
    exact H1.
Qed.

(* Treasure "19dQY8Hevd7hLbGPondJV79nh114Y4UxVx" *)
Theorem Sigma_Eq : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) <-> exists x :e X, exists y :e Y x, z = pair x y.
let X Y z. apply iffI.
- apply Sigma_E.
- assume H1: exists x :e X, exists y :e Y x, z = pair x y.
  apply (exandE set (fun x => x :e X) (fun x => exists y :e Y x, z = pair x y) H1).
  let x.
  assume Hx: x :e X.
  assume H2: exists y :e Y x, z = pair x y.
  apply (exandE set (fun y => y :e Y x) (fun y => z = pair x y) H2).
  let y.
  assume Hy: y :e Y x.
  assume H3: z = pair x y.
  prove z :e Sigma_ x :e X, Y x.
  rewrite H3.
  prove pair x y :e Sigma_ x :e X, Y x.
  apply pair_Sigma.
  + exact Hx.
  + exact Hy.
Qed.

(*** Covariance of subsets of Sigmas ***)
(* Treasure "1Gb91EerLiJ59qvxMCyk5VGkVzEjUtTNGn" *)
Theorem Sigma_mon : forall X Y:set, X c= Y -> forall Z W:set->set, (forall x :e X, Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, W y.
let X Y.
assume H1: X c= Y.
let Z W.
assume H2: forall x :e X, Z x c= W x.
let u.
assume H3: u :e Sigma_ x :e X, Z x.
apply (and3E (pair (proj0 u) (proj1 u) = u) (proj0 u :e X) (proj1 u :e Z (proj0 u)) (Sigma_eta_proj0_proj1 X Z u H3)).
assume H4: pair (proj0 u) (proj1 u) = u.
assume H5: proj0 u :e X.
assume H6: proj1 u :e Z (proj0 u).
prove u :e Sigma_ y :e Y, W y.
rewrite <- H4.
apply (pair_Sigma Y W).
- prove proj0 u :e Y.
  exact (H1 (proj0 u) H5).
- prove proj1 u :e W (proj0 u).
  exact (H2 (proj0 u) H5 (proj1 u) H6).
Qed.

(* Treasure "1NxzSQXTktnPfRNhU4UovAWxSoqNb7cVv3" *)
Theorem Sigma_mon0 : forall X Y:set, X c= Y -> forall Z:set->set, (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, Z y.
exact (fun (X Y : set) (H1 : X c= Y) (Z : set -> set) => Sigma_mon X Y H1 Z Z (fun (x : set) (_ : x :e X) => Subq_ref (Z x))).
Qed.

(* Treasure "1LHC36pdabr2Y2jkof6J1ZRCsJAZDQeVBZ" *)
Theorem Sigma_mon1 : forall X:set, forall Z W:set->set, (forall x, x :e X -> Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ x :e X, W x.
exact (fun (X : set) (Z W : set -> set) (H1 : forall x : set, x :e X -> Z x c= W x) => Sigma_mon X X (Subq_ref X) Z W H1).
Qed.

(* Treasure "1JFa3yLY3FxMucyah6QkpjqQ8Pos3Jtno2" *)
Theorem Sigma_Power_1 : forall X:set, X :e Power 1 -> forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Sigma_ x :e X, Y x) :e Power 1.
let X.
assume HX: X :e Power 1.
let Y.
assume HY: forall x :e X, Y x :e Power 1.
prove (Sigma_ x :e X, Y x) :e Power 1.
apply PowerI.
prove (Sigma_ x :e X, Y x) c= 1.
let z.
assume Hz: z :e (Sigma_ x :e X, Y x).
prove z :e 1.
claim L: z = 0.
{
  apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z Hz)).
  assume H1: pair (proj0 z) (proj1 z) = z.
  assume H2: proj0 z :e X.
  assume H3: proj1 z :e Y (proj0 z).
  claim L2: proj0 z = 0.
  {
    exact (SingE 0 (proj0 z) (Subq_1_Sing0 (proj0 z) (PowerE 1 X HX (proj0 z) H2))).
  }
  claim L3: proj1 z = 0.
  {
    exact (SingE 0 (proj1 z) (Subq_1_Sing0 (proj1 z) (PowerE 1 (Y (proj0 z)) (HY (proj0 z) H2) (proj1 z) H3))).
  }
  rewrite <- H1.
  prove pair (proj0 z) (proj1 z) = 0.
  rewrite L2.
  rewrite L3.
  prove pair 0 0 = 0.
  exact pair_0_0.
}
rewrite L.
exact In_0_1.
Qed.

Definition setprod : set->set->set := fun X Y:set => Sigma_ x :e X, Y.

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

(* Treasure "1PXBDmh7opbK5wJmiUxLxBNBZLp9XijCha" *)
Theorem pair_setprod : forall X Y:set, forall (x :e X) (y :e Y), pair x y :e X :*: Y.
exact (fun X Y x Hx y Hy => pair_Sigma X (fun _ => Y) x Hx y Hy).
Qed.

(* Treasure "1CUZzZ9aGiSSsPbGeke4iaqQnDdDcJv1nW" *)
Theorem proj0_setprod : forall X Y:set, forall z :e X :*: Y, proj0 z :e X.
exact (fun X Y z Hz => proj0_Sigma X (fun _ => Y) z Hz).
Qed.

(* Treasure "14phuniVrhZsqc3uQ5arhe2XgfVGk292C6" *)
Theorem proj1_setprod : forall X Y:set, forall z :e X :*: Y, proj1 z :e Y.
exact (fun X Y z Hz => proj1_Sigma X (fun _ => Y) z Hz).
Qed.

(* Treasure "15eQFz9uibMjVoR5cg6hCmH26xqmGprsVD" *)
Theorem setprod_mon : forall X Y:set, X c= Y -> forall Z W:set, Z c= W -> X :*: Z c= Y :*: W.
exact (fun X Y H1 Z W H2 => Sigma_mon X Y H1 (fun _ => Z) (fun _ => W) (fun _ _ => H2)).
Qed.

(* Treasure "1GTQW14B14uYsBGiQbDrjzxTYshAhM1S5E" *)
Theorem setprod_mon0 : forall X Y:set, X c= Y -> forall Z:set, X :*: Z c= Y :*: Z.
exact (fun X Y H1 Z => Sigma_mon0 X Y H1 (fun _ => Z)).
Qed.

(* Treasure "147QWhj3uq3grSnUCvRAJBhYRYMxAnSuZa" *)
Theorem setprod_mon1 : forall X:set, forall Z W:set, Z c= W -> X :*: Z c= X :*: W.
exact (fun X => setprod_mon X X (Subq_ref X)).
Qed.

(* Treasure "1H8xQMttd622KpkEGHvM4PSDDyM1reQtTS" *)
Theorem pair_setprod_E0 : forall X Y x y:set, pair x y :e X :*: Y -> x :e X.
exact (fun X Y x y H => pair_Sigma_E0 X (fun _ => Y) x y H).
Qed.

(* Treasure "1mex9DZE7VZ3w1f6gTKU9f1VziS3AtYsP" *)
Theorem pair_setprod_E1 : forall X Y x y:set, pair x y :e X :*: Y -> y :e Y.
exact (fun X Y x y H => pair_Sigma_E1 X (fun _ => Y) x y H).
Qed.
