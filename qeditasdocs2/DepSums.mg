(* Title "Dependent Sums and Simple Products of Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2y5gxoNPTwrc94awZ" *)

(** Preamble **)
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
Axiom andI : forall A B : prop , A -> B -> A /\ B.
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Definition iff : prop -> prop -> prop := fun A B : prop => (A -> B) /\ (B -> A).
(* Unicode <-> "2194" *)
Infix <-> 805 := iff.
Axiom iffI : forall A B : prop , (A -> B) -> (B -> A) -> (A <-> B).
Axiom and3I : forall P1 P2 P3 : prop, P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
Axiom and3E : forall P1 P2 P3 : prop, P1 /\ P2 /\ P3 -> (forall p : prop , (P1 -> P2 -> P3 -> p) -> p).
Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
End Poly1_eq.
Infix = 502 := eq.
Section Poly1_eqthms.
Variable A : SType.
Axiom eqI : forall x : A , x = x.
Axiom eq_sym : forall x y : A , x = y -> y = x.
End Poly1_eqthms.
Section Poly1_exdef.
Variable A : SType.
Variable Q : A -> prop.
Definition ex : prop := forall P : prop , (forall x : A , Q x -> P) -> P.
End Poly1_exdef.
(* Unicode exists "2203" *)
Binder+ exists , := ex.
Section Poly1_exthms.
Variable A : SType.
Axiom exI : forall P : A -> prop , forall x : A , P x -> exists x : A , P x.
End Poly1_exthms.
Section Poly1.
Variable A : SType.
Variable P : A -> prop.
Variable Q : A -> prop.
Axiom exandE : (exists x : A , P x /\ Q x) -> forall p : prop , (forall x : A , P x -> Q x -> p) -> p.
End Poly1.
Parameter In : set -> set -> prop.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Binder+ exists , := ex ; and.
Axiom Subq_ref : forall X : set , X c= X.
(* Unicode Empty "2205" *)
Parameter Empty : set.
(* Unicode Power "1D4AB" *)
Parameter Power : set -> set.
Axiom PowerE : forall X Y : set , Y :e Power X -> Y c= X.
Axiom PowerI : forall X Y : set , Y c= X -> Y :e (Power X).
Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.
Axiom ReplE2 : forall X : set , forall F : set -> set , forall y : set , y :e {F x|x :e X} -> forall p : prop , (forall x : set , x :e X -> y = F x -> p) -> p.
Axiom ReplI : forall X : set , forall F : set -> set , forall x : set , x :e X -> F x :e {F x|x :e X}.
(* Parameter famunion MLDh3uxqogjACXY77fJZ4JFgSiaH8yJtXhRixVQDD4SpxxHJ *)
Parameter famunion : set -> (set -> set) -> set.
(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.
Axiom famunionI : forall X : set , forall F : (set -> set) , forall x y : set , x :e X -> y :e F x -> y :e \/_ x :e X , F x.
Axiom famunionE : forall X : set , forall F : (set -> set) , forall y : set , y :e (\/_ x :e X , F x) -> exists x : set , x :e X /\ y :e F x.
(* Parameter Sing MHQKaPMuqpPD7JYxt91FMGRr1nnP2YZ3625uoySLjwF6JjbU *)
Parameter Sing:set->set.
Notation SetEnum1 Sing.
Axiom SingI : forall x : set , x :e {x}.
Axiom SingE : forall x y : set , y :e {x} -> y = x.
(* Parameter ordsucc MJAVHZ4UTjfNkP94R1Y274wA1jSL4zvYwwczio73KbaM1Zkf *)
Parameter ordsucc : set -> set.
Notation Nat Empty ordsucc.
Axiom In_0_1 : 0 :e 1.
Axiom Subq_1_Sing0 : 1 c= {0}.
Definition nat_p : set -> prop := fun n : set => forall p : set -> prop , p 0 -> (forall x : set , p x -> p (ordsucc x)) -> p n.
(* Parameter pair MJmS5j2rXbcGEf2zSu7NM7dNRSPAF7wSkRVV2u9AJZfT9Gnm *)
Parameter pair : set -> set -> set.
Axiom pair_0_0 : pair 0 0 = 0.
Axiom pair_1_0_1 : pair 1 0 = 1.
Axiom pair_1_1_2 : pair 1 1 = 2.
Axiom nat_pair1_ordsucc : forall n : set , nat_p n -> pair 1 n = ordsucc n.
(* Parameter proj0 MLoaNtbgXqfmmr2Mj2LF6f8K89bDZosJkciwvhBYQPWj4DJg *)
Parameter proj0 : set -> set.
(* Parameter proj1 MLy8iM6ihThq9D7JHeXDKr7cDwsLSZPJcUTnP8i3Fn7Y13R4 *)
Parameter proj1 : set -> set.
Axiom pairI0 : forall X Y x , x :e X -> pair 0 x :e pair X Y.
Axiom pairI1 : forall X Y y , y :e Y -> pair 1 y :e pair X Y.
Axiom pairE : forall X Y z , z :e pair X Y -> (exists x :e X , z = pair 0 x) \/ (exists y :e Y , z = pair 1 y).
Axiom pairE0 : forall X Y x , pair 0 x :e pair X Y -> x :e X.
Axiom pairE1 : forall X Y y , pair 1 y :e pair X Y -> y :e Y.
Axiom pairEq : forall X Y z , z :e pair X Y <-> (exists x :e X , z = pair 0 x) \/ (exists y :e Y , z = pair 1 y).
Axiom pairSubq : forall X Y W Z , X c= W -> Y c= Z -> pair X Y c= pair W Z.
Axiom proj0I : forall w u : set , pair 0 u :e w -> u :e proj0 w.
Axiom proj0E : forall w u : set , u :e proj0 w -> pair 0 u :e w.
Axiom proj1I : forall w u : set , pair 1 u :e w -> u :e proj1 w.
Axiom proj1E : forall w u : set , u :e proj1 w -> pair 1 u :e w.
Axiom proj0_pair_eq : forall X Y : set , proj0 (pair X Y) = X.
Axiom proj1_pair_eq : forall X Y : set , proj1 (pair X Y) = Y.
Axiom pair_inj : forall x y w z : set , pair x y = pair w z -> x = w /\ y = z.
Axiom pair_eta_Subq_proj : forall w , pair (proj0 w) (proj1 w) c= w.

(** Main Body **)

(*** Sigma X Y = {(x,y) | x in X, y in Y x} ***)
Definition Sigma : set -> (set -> set) -> set :=
fun X Y => \/_ x :e X, {pair x y|y :e Y x}.

(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

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

Theorem proj_Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z.
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z H1)).
assume H2 _ _.
exact H2.
Qed.

Theorem proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z H1)).
assume _ H2 _.
exact H2.
Qed.

Theorem proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).
let X Y z.
assume H1: z :e Sigma_ x :e X, Y x.
apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e Y (proj0 z)) (Sigma_eta_proj0_proj1 X Y z H1)).
assume _ _ H2.
exact H2.
Qed.

Theorem pair_Sigma_E0 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> x :e X.
let X Y x y.
assume H1: pair x y :e Sigma_ x :e X, Y x.
prove x :e X.
rewrite <- (proj0_pair_eq x y).
prove proj0 (pair x y) :e X.
exact (proj0_Sigma X Y (pair x y) H1).
Qed.

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

Theorem Sigma_mon0 : forall X Y:set, X c= Y -> forall Z:set->set, (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, Z y.
exact (fun (X Y : set) (H1 : X c= Y) (Z : set -> set) => Sigma_mon X Y H1 Z Z (fun (x : set) (_ : x :e X) => Subq_ref (Z x))).
Qed.

Theorem Sigma_mon1 : forall X:set, forall Z W:set->set, (forall x, x :e X -> Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ x :e X, W x.
exact (fun (X : set) (Z W : set -> set) (H1 : forall x : set, x :e X -> Z x c= W x) => Sigma_mon X X (Subq_ref X) Z W H1).
Qed.

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

Theorem pair_setprod : forall X Y:set, forall (x :e X) (y :e Y), pair x y :e X :*: Y.
exact (fun X Y x Hx y Hy => pair_Sigma X (fun _ => Y) x Hx y Hy).
Qed.

Theorem proj0_setprod : forall X Y:set, forall z :e X :*: Y, proj0 z :e X.
exact (fun X Y z Hz => proj0_Sigma X (fun _ => Y) z Hz).
Qed.

Theorem proj1_setprod : forall X Y:set, forall z :e X :*: Y, proj1 z :e Y.
exact (fun X Y z Hz => proj1_Sigma X (fun _ => Y) z Hz).
Qed.

Theorem setprod_mon : forall X Y:set, X c= Y -> forall Z W:set, Z c= W -> X :*: Z c= Y :*: W.
exact (fun X Y H1 Z W H2 => Sigma_mon X Y H1 (fun _ => Z) (fun _ => W) (fun _ _ => H2)).
Qed.

Theorem setprod_mon0 : forall X Y:set, X c= Y -> forall Z:set, X :*: Z c= Y :*: Z.
exact (fun X Y H1 Z => Sigma_mon0 X Y H1 (fun _ => Z)).
Qed.

Theorem setprod_mon1 : forall X:set, forall Z W:set, Z c= W -> X :*: Z c= X :*: W.
exact (fun X => setprod_mon X X (Subq_ref X)).
Qed.

Theorem pair_setprod_E0 : forall X Y x y:set, pair x y :e X :*: Y -> x :e X.
exact (fun X Y x y H => pair_Sigma_E0 X (fun _ => Y) x y H).
Qed.

Theorem pair_setprod_E1 : forall X Y x y:set, pair x y :e X :*: Y -> y :e Y.
exact (fun X Y x y H => pair_Sigma_E1 X (fun _ => Y) x y H).
Qed.
