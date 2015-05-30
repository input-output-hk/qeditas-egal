(* Title "Functions as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2VZUMZGBmJfVam7ZU" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
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
Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
Definition neq : A -> A -> prop := fun x y => ~ eq x y.
End Poly1_eq.
Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.
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
Section Poly1.
Variable A : SType.
Axiom exI : forall P : A -> prop , forall x : A , P x -> exists x : A , P x.
Axiom exandE : forall P Q:A->prop, (exists x : A , P x /\ Q x) -> forall p : prop , (forall x : A , P x -> Q x -> p) -> p.
End Poly1.
Section PE.
Variable A : SType.
Axiom pred_ext : forall P Q : A -> prop , P c= Q -> Q c= P -> P = Q.
End PE.
Section Choice.
Variable A : SType.
Parameter Eps : (A -> prop) -> A.
End Choice.
Binder some , := Eps.
Section IfA.
Variable A : SType.
Definition If : prop -> A -> A -> A := (fun p x y => some z : A , p /\ z = x \/ ~ p /\ z = y).
Notation IfThenElse If.
Axiom If_0 : forall p : prop , forall x y : A , ~ p -> (if p then x else y) = y.
Axiom If_1 : forall p : prop , forall x y : A , p -> (if p then x else y) = x.
End IfA.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Binder+ exists , := ex ; and.
Axiom set_ext : forall X Y : set , X c= Y -> Y c= X -> X = Y.
(* Unicode Empty "2205" *)
Parameter Empty : set.
Axiom Empty_eq : forall X : set , (forall x , x /:e X) -> X = Empty.
(* Parameter UPair MM7DGQPznayt6juAGExgMfTfAFmB3TUo5yTKCJZ37zpfyzJN *)
Parameter UPair : set -> set -> set.
Notation SetEnum2 UPair.
Axiom UPairE : forall x y z : set , x :e {y,z} -> x = y \/ x = z.
(* Parameter ReplSep MGAW8vPDeBca3TgGDccKuPs1GHwwx8qMmaXxXv6jf5yqVv91 *)
Parameter ReplSep : set -> (set -> prop) -> (set -> set) -> set.
Notation ReplSep ReplSep.
Axiom ReplSepI : forall X : set , forall P : set -> prop , forall F : set -> set , forall x : set , x :e X -> P x -> F x :e {F x|x :e X,P x}.
Axiom ReplSepE : forall X : set , forall P : set -> prop , forall F : set -> set , forall y : set , y :e {F x|x :e X,P x} -> exists x : set , x :e X /\ P x /\ y = F x.
Axiom ReplSepE2 : forall X : set , forall P : set -> prop , forall F : set -> set , forall y : set , y :e {F x|x :e X,P x} -> forall p : prop , (forall x :e X , P x -> y = F x -> p) -> p.
(* Parameter ordsucc MJAVHZ4UTjfNkP94R1Y274wA1jSL4zvYwwczio73KbaM1Zkf *)
Parameter ordsucc : set -> set.
Notation Nat Empty ordsucc.
Axiom In_1_2 : 1 :e 2.
Axiom In_0_2 : 0 :e 2.
Axiom neq_1_0 : 1 <> 0.
Axiom Subq_2_UPair01 : 2 c= {0,1}.
(* Parameter pair MJmS5j2rXbcGEf2zSu7NM7dNRSPAF7wSkRVV2u9AJZfT9Gnm *)
Parameter pair : set -> set -> set.
(* Parameter proj0 MLoaNtbgXqfmmr2Mj2LF6f8K89bDZosJkciwvhBYQPWj4DJg *)
Parameter proj0 : set -> set.
(* Parameter proj1 MLy8iM6ihThq9D7JHeXDKr7cDwsLSZPJcUTnP8i3Fn7Y13R4 *)
Parameter proj1 : set -> set.
Axiom pairI0 : forall X Y x , x :e X -> pair 0 x :e pair X Y.
Axiom pairI1 : forall X Y y , y :e Y -> pair 1 y :e pair X Y.
Axiom pairE : forall X Y z , z :e pair X Y -> (exists x :e X , z = pair 0 x) \/ (exists y :e Y , z = pair 1 y).
Axiom proj0I : forall w u : set , pair 0 u :e w -> u :e proj0 w.
Axiom proj0E : forall w u : set , u :e proj0 w -> pair 0 u :e w.
Axiom proj1I : forall w u : set , pair 1 u :e w -> u :e proj1 w.
Axiom proj1E : forall w u : set , u :e proj1 w -> pair 1 u :e w.
Axiom proj0_pair_eq : forall X Y : set , proj0 (pair X Y) = X.
Axiom proj1_pair_eq : forall X Y : set , proj1 (pair X Y) = Y.
Axiom pair_inj : forall x y w z : set , pair x y = pair w z -> x = w /\ y = z.
Axiom pair_eta_Subq_proj : forall w , pair (proj0 w) (proj1 w) c= w.
(* Parameter Sigma MHMjeodfKZVQDpM5vx4QZCQf3j9mMxhzXxFc99Ytj6RVM875 *)
Parameter Sigma : set -> (set -> set) -> set.
(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.
Axiom pair_Sigma : forall X : set , forall Y : set -> set , forall x :e X , forall y :e Y x , pair x y :e Sigma_ x :e X , Y x.
Axiom proj_Sigma_eta : forall X : set , forall Y : set -> set , forall z :e (Sigma_ x :e X , Y x) , pair (proj0 z) (proj1 z) = z.
Axiom proj0_Sigma : forall X : set , forall Y : set -> set , forall z : set , z :e (Sigma_ x :e X , Y x) -> proj0 z :e X.
Axiom proj1_Sigma : forall X : set , forall Y : set -> set , forall z : set , z :e (Sigma_ x :e X , Y x) -> proj1 z :e Y (proj0 z).
Axiom pair_Sigma_E0 : forall X : set , forall Y : set -> set , forall x y : set , pair x y :e (Sigma_ x :e X , Y x) -> x :e X.
Axiom pair_Sigma_E1 : forall X : set , forall Y : set -> set , forall x y : set , pair x y :e (Sigma_ x :e X , Y x) -> y :e Y x.
Axiom Sigma_E : forall X : set , forall Y : set -> set , forall z : set , z :e (Sigma_ x :e X , Y x) -> exists x :e X , exists y :e Y x , z = pair x y.
Axiom Sigma_Eq : forall X : set , forall Y : set -> set , forall z : set , z :e (Sigma_ x :e X , Y x) <-> exists x :e X , exists y :e Y x , z = pair x y.

(** Main Body **)

(*** lam X F = {(x,y) | x :e X, y :e F x} = \/_{x :e X} {(x,y) | y :e (F x)} = Sigma X F ***)
Definition lam : set -> (set -> set) -> set := Sigma.

(***  ap f x = {proj1 z | z :e f,  exists y, z = pair x y}} ***)
Definition ap : set -> set -> set := fun f x => {proj1 z|z :e f, exists y:set, z = pair x y}.

Notation SetImplicitOp ap.
Notation SetLam lam.

Theorem lamI : forall X:set, forall F:set->set, forall x :e X, forall y :e F x, pair x y :e fun x :e X => F x.
exact pair_Sigma.
Qed.

Theorem lamE : forall X:set, forall F:set->set, forall z:set, z :e (fun x :e X => F x) -> exists x :e X, exists y :e F x, z = pair x y.
exact Sigma_E.
Qed.

Theorem lamEq : forall X:set, forall F:set->set, forall z, z :e (fun x :e X => F x) <-> exists x :e X, exists y :e F x, z = pair x y.
exact Sigma_Eq.
Qed.

Theorem apI : forall f x y, pair x y :e f -> y :e f x.
let f x y.
assume H1: pair x y :e f.
prove y :e {proj1 z|z :e f, exists y:set, z = pair x y}.
rewrite <- (proj1_pair_eq x y).
prove proj1 (pair x y) :e {proj1 z|z :e f, exists y:set, z = pair x y}.
apply (ReplSepI f (fun z => exists y:set, z = pair x y) proj1 (pair x y) H1).
prove exists y':set, pair x y = pair x y'.
witness y.
apply (eqI set).
Qed.

Theorem apE : forall f x y, y :e f x -> pair x y :e f.
let f x y.
assume H1: y :e {proj1 z|z :e f, exists y:set, z = pair x y}.
prove pair x y :e f.
apply (ReplSepE2 f (fun z => exists y:set, z = pair x y) proj1 y H1).
let z.
assume Hz: z :e f.
assume H1: exists y:set, z = pair x y.
assume H2: y = proj1 z.
apply H1.
let v.
assume H3: z = pair x v.
claim L1: y = v.
{
  rewrite H2.
  rewrite H3.
  prove proj1 (pair x v) = v.
  apply proj1_pair_eq.
}
claim L2: z = pair x y.
{
  rewrite L1.
  exact H3.
}
rewrite <- L2.
exact Hz.
Qed.

Theorem apEq : forall f x y, y :e f x <-> pair x y :e f.
let f x y. apply iffI.
- apply apE.
- apply apI.
Qed.

Theorem beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.
let X F x.
assume Hx: x :e X.
apply set_ext.
- let w.
  assume Hw: w :e (fun x :e X => F x) x.
  claim L1: pair x w :e (fun x :e X => F x).
  { exact (apE (fun x :e X => F x) x w Hw). }
  exact (pair_Sigma_E1 X F x w L1).
- let w.
  assume Hw: w :e F x.
  prove w :e (fun x :e X => F x) x.
  apply apI.
  prove pair x w :e fun x :e X => F x.
  prove pair x w :e Sigma_ x :e X, F x.
  apply pair_Sigma.
  + exact Hx.
  + exact Hw.
Qed.

Theorem beta0 : forall X:set, forall F:set -> set, forall x:set, x /:e X -> (fun x :e X => F x) x = 0.
let X F x.
assume Hx: x /:e X.
apply (Empty_eq ((fun x :e X => F x) x)).
let w.
assume Hw: w :e ((fun x :e X => F x) x).
claim L1: pair x w :e fun x :e X => F x.
{ exact (apE (fun x :e X => F x) x w Hw). }
claim L2: x :e X.
{ exact (pair_Sigma_E0 X F x w L1). }
exact (Hx L2).
Qed.

Theorem proj0_ap_0 : forall u, proj0 u = u 0.
let u. apply set_ext.
- let w.
  assume H1: w :e proj0 u.
  prove w :e u 0.
  apply apI.
  prove pair 0 w :e u.
  apply proj0E.
  prove w :e proj0 u.
  exact H1.
- let w.
  assume H1: w :e u 0.
  prove w :e proj0 u.
  apply proj0I.
  prove pair 0 w :e u.
  apply apE.
  prove w :e u 0.
  exact H1.
Qed.

Theorem proj1_ap_1 : forall u, proj1 u = u 1.
let u. apply set_ext.
- let w.
  assume H1: w :e proj1 u.
  prove w :e u 1.
  apply apI.
  prove pair 1 w :e u.
  apply proj1E.
  prove w :e proj1 u.
  exact H1.
- let w.
  assume H1: w :e u 1.
  prove w :e proj1 u.
  apply proj1I.
  prove pair 1 w :e u.
  apply apE.
  prove w :e u 1.
  exact H1.
Qed.

Theorem pair_ap_0 : forall x y:set, (pair x y) 0 = x.
let x y.
rewrite <- (proj0_ap_0 (pair x y)).
prove proj0 (pair x y) = x.
apply proj0_pair_eq.
Qed.

Theorem pair_ap_1 : forall x y:set, (pair x y) 1 = y.
let x y.
rewrite <- (proj1_ap_1 (pair x y)).
prove proj1 (pair x y) = y.
apply proj1_pair_eq.
Qed.

Theorem pair_ap_n2 : forall x y i:set, i /:e 2 -> (pair x y) i = 0.
let x y i.
assume Hi: i /:e 2.
apply Empty_eq.
let w.
assume Hw: w :e (pair x y) i.
claim L1: pair i w :e pair x y.
{
  apply apE.
  exact Hw.
}
apply (pairE x y (pair i w) L1).
- assume H1: exists u :e x, pair i w = pair 0 u.
  apply (exandE set (fun u => u :e x) (fun u => pair i w = pair 0 u) H1).
  let u.
  assume Hu: u :e x.
  assume H2: pair i w = pair 0 u.
  apply (pair_inj i w 0 u H2).
  assume H3: i = 0.
  assume _.
  apply Hi.
  rewrite H3.
  exact In_0_2.
- assume H1: exists v :e y, pair i w = pair 1 v.
  apply (exandE set (fun v => v :e y) (fun v => pair i w = pair 1 v) H1).
  let v.
  assume Hv: v :e y.
  assume H2: pair i w = pair 1 v.
  apply (pair_inj i w 1 v H2).
  assume H3: i = 1.
  assume _.
  apply Hi.
  rewrite H3.
  exact In_1_2.
Qed.

Theorem pair_eta_Subq : forall w, pair (w 0) (w 1) c= w.
let w.
rewrite <- (proj0_ap_0 w).
prove pair (proj0 w) (w 1) c= w.
rewrite <- (proj1_ap_1 w).
prove pair (proj0 w) (proj1 w) c= w.
exact (pair_eta_Subq_proj w).
Qed.

Theorem ap0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 0) :e X.
let X Y z.
rewrite <- proj0_ap_0.
apply proj0_Sigma.
Qed.

Theorem ap1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 1) :e (Y (z 0)).
let X Y z.
rewrite <- proj0_ap_0.
rewrite <- proj1_ap_1.
apply proj1_Sigma.
Qed.

Theorem Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (z 0) (z 1) = z.
let X Y z.
rewrite <- proj0_ap_0.
rewrite <- proj1_ap_1.
apply proj_Sigma_eta.
Qed.

Definition pair_p:set->prop
:= fun u:set => pair (u 0) (u 1) = u.

Theorem pair_p_I : forall x y, pair_p (pair x y).
let x y.
prove pair (pair x y 0) (pair x y 1) = pair x y.
rewrite pair_ap_0.
rewrite pair_ap_1.
apply (eqI set).
Qed.

Theorem pair_p_I2 : forall w, (forall u :e w, pair_p u /\ u 0 :e 2) -> pair_p w.
let w.
assume H1: forall u :e w, pair_p u /\ u 0 :e 2.
claim L1: pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w} = w.
{
  apply set_ext.
  - prove pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w} c= w.
    let v.
    assume Hv: v :e pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}.
    prove v :e w.
    apply (pairE {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w} v Hv).
    + assume H2: exists x :e {u 1|u :e w, pair 0 (u 1) :e w}, v = pair 0 x.
      apply (exandE set (fun x => x :e {u 1|u :e w, pair 0 (u 1) :e w}) (fun x => v = pair 0 x) H2).
      let x.
      assume Hx: x :e {u 1|u :e w, pair 0 (u 1) :e w}.
      assume H3: v = pair 0 x.
      apply (ReplSepE2 w (fun u => pair 0 (u 1) :e w) (fun u => u 1) x Hx).
      let z.
      assume Hv: z :e w.
      assume H4: pair 0 (z 1) :e w.
      assume H5: x = z 1.
      rewrite H3.
      prove pair 0 x :e w.
      rewrite H5.
      exact H4.
    + assume H2: exists y :e {u 1|u :e w, pair 1 (u 1) :e w}, v = pair 1 y.
      apply (exandE set (fun y => y :e {u 1|u :e w, pair 1 (u 1) :e w}) (fun y => v = pair 1 y) H2).
      let y.
      assume Hy: y :e {u 1|u :e w, pair 1 (u 1) :e w}.
      assume H3: v = pair 1 y.
      apply (ReplSepE2 w (fun u => pair 1 (u 1) :e w) (fun u => u 1) y Hy).
      let z.
      assume Hv: z :e w.
      assume H4: pair 1 (z 1) :e w.
      assume H5: y = z 1.
      rewrite H3.
      prove pair 1 y :e w.
      rewrite H5.
      exact H4.
  - prove w c= pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}.
    let v.
    assume Hv: v :e w.
    prove v :e pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}.
    apply (H1 v Hv).
    assume H2: pair (v 0) (v 1) = v.
    assume H3: v 0 :e 2.
    rewrite <- H2.
    prove pair (v 0) (v 1) :e pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}.
    claim L1: v 0 :e {0,1}.
    { exact (Subq_2_UPair01 (v 0) H3). }    
    apply (UPairE (v 0) 0 1 L1).
    + assume H4: v 0 = 0.
      rewrite H4.
      prove pair 0 (v 1) :e pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}.
      apply pairI0.
      prove v 1 :e {u 1|u :e w, pair 0 (u 1) :e w}.
      apply (ReplSepI w (fun u => pair 0 (u 1) :e w) (fun u => u 1) v).
      * prove v :e w.
        exact Hv.
      * prove pair 0 (v 1) :e w.
        rewrite <- H4 at 1. (*** Remember that 1 is notation for ordsucc 0, so we need the "at 1" here. ***)
	prove pair (v 0) (v 1) :e w.
	rewrite H2.
	prove v :e w.
	exact Hv.
    + assume H4: v 0 = 1.
      rewrite H4.
      prove pair 1 (v 1) :e pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}.
      apply pairI1.
      prove v 1 :e {u 1|u :e w, pair 1 (u 1) :e w}.
      apply (ReplSepI w (fun u => pair 1 (u 1) :e w) (fun u => u 1) v).
      * prove v :e w.
        exact Hv.
      * prove pair 1 (v 1) :e w.
        rewrite <- H4 at 1.
	prove pair (v 0) (v 1) :e w.
	rewrite H2.
	prove v :e w.
	exact Hv.
}
prove pair_p w.
rewrite <- L1.
prove pair_p (pair {u 1|u :e w, pair 0 (u 1) :e w} {u 1|u :e w, pair 1 (u 1) :e w}).
apply pair_p_I.
Qed.

Theorem pair_p_In_ap : forall w f, pair_p w -> w :e f -> w 1 :e ap f (w 0).
let w f.
assume H1: pair (w 0) (w 1) = w.
assume H2: w :e f.
prove w 1 :e ap f (w 0).
apply apI.
prove pair (w 0) (w 1) :e f.
rewrite H1.
exact H2.
Qed.

Definition tuple_p : set->set->prop :=
fun n u => forall z :e u, exists i :e n, exists x:set, z = pair i x.

Theorem pair_p_tuple2 : pair_p = tuple_p 2.
apply (pred_ext set).
- let u.
  assume H1: pair (u 0) (u 1) = u.
  prove tuple_p 2 u.
  rewrite <- H1.
  let z.
  assume H2: z :e pair (u 0) (u 1).
  prove exists i :e 2, exists x:set, z = pair i x.
  apply (pairE (u 0) (u 1) z H2).
  + assume H3: exists x :e u 0, z = pair 0 x.
    apply (exandE set (fun x => x :e u 0) (fun x => z = pair 0 x) H3).
    let x.
    assume H4: x :e u 0.
    assume H5: z = pair 0 x.
    witness 0.
    prove 0 :e 2 /\ exists x':set, z = pair 0 x'.
    apply andI.
    * exact In_0_2.
    * witness x.
      prove z = pair 0 x.
      exact H5.
  + assume H3: exists y :e u 1, z = pair 1 y.
    apply (exandE set (fun y => y :e u 1) (fun y => z = pair 1 y) H3).
    let y.
    assume H4: y :e u 1.
    assume H5: z = pair 1 y.
    witness 1.
    prove 1 :e 2 /\ exists y':set, z = pair 1 y'.
    apply andI.
    * exact In_1_2.
    * witness y.
      prove z = pair 1 y.
      exact H5.
- let u.
  assume H1: tuple_p 2 u.
  prove pair_p u.
  apply pair_p_I2.
  prove forall z :e u, pair_p z /\ z 0 :e 2.
  let z.
  assume H2: z :e u.
  apply (exandE set (fun i => i :e 2) (fun i => exists x:set, z = pair i x) (H1 z H2)).
  let i.
  assume H3: i :e 2.
  assume H4: exists x:set, z = pair i x.
  apply H4.
  let x.
  assume H5: z = pair i x.
  rewrite H5.
  apply andI.
  + prove pair_p (pair i x).
    apply pair_p_I.
  + prove pair i x 0 :e 2.
    rewrite pair_ap_0.
    exact H3.
Qed.

Theorem tuple_p_2_tuple : forall x y:set, tuple_p 2 (x,y).
let x y.
prove forall v :e (x,y), exists i :e 2, exists u:set, v = pair i u.
let v.
assume Hv : v :e fun i :e 2 => if i = 0 then x else y.
prove exists i :e 2, exists x:set, v = pair i x.
claim L1: exists i :e 2, exists u :e if i = 0 then x else y, v = pair i u.
{ exact (lamE 2 (fun i => if i = 0 then x else y) v Hv). }
apply (exandE set (fun i => i :e 2) (fun i => exists u :e if i = 0 then x else y, v = pair i u) L1).
let i.
assume Hi: i :e 2.
assume H1: exists u :e if i = 0 then x else y, v = pair i u.
apply (exandE set (fun u => u :e if i = 0 then x else y) (fun u => v = pair i u) H1).
let u.
assume Hu : u :e if i = 0 then x else y.
assume H2: v = pair i u.
witness i.
prove i :e 2 /\ exists u:set, v = pair i u.
apply andI.
- exact Hi.
- witness u. exact H2.
Qed.

Theorem tuple_p_3_tuple : forall x y z:set, tuple_p 3 (x,y,z).
let x y z.
prove forall v :e (x,y,z), exists i :e 3, exists u:set, v = pair i u.
let v.
assume Hv : v :e fun i :e 3 => if i = 0 then x else if i = 1 then y else z.
prove exists i :e 3, exists x:set, v = pair i x.
claim L1: exists i :e 3, exists u :e (if i = 0 then x else if i = 1 then y else z), v = pair i u.
{ exact (lamE 3 (fun i => if i = 0 then x else if i = 1 then y else z) v Hv). }
apply (exandE set (fun i => i :e 3) (fun i => exists u :e (if i = 0 then x else if i = 1 then y else z), v = pair i u) L1).
let i.
assume Hi: i :e 3.
assume H1: exists u :e (if i = 0 then x else if i = 1 then y else z), v = pair i u.
apply (exandE set (fun u => u :e if i = 0 then x else if i = 1 then y else z) (fun u => v = pair i u) H1).
let u.
assume Hu : u :e if i = 0 then x else if i = 1 then y else z.
assume H2: v = pair i u.
witness i.
prove i :e 3 /\ exists u:set, v = pair i u.
apply andI.
- exact Hi.
- witness u. exact H2.
Qed.

Theorem tuple_p_4_tuple : forall x y z w:set, tuple_p 4 (x,y,z,w).
let x y z w.
prove forall v :e (x,y,z,w), exists i :e 4, exists u:set, v = pair i u.
let v.
assume Hv : v :e fun i :e 4 => if i = 0 then x else if i = 1 then y else if i = 2 then z else w.
prove exists i :e 4, exists x:set, v = pair i x.
claim L1: exists i :e 4, exists u :e (if i = 0 then x else if i = 1 then y else if i = 2 then z else w), v = pair i u.
{ exact (lamE 4 (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) v Hv). }
apply (exandE set (fun i => i :e 4) (fun i => exists u :e (if i = 0 then x else if i = 1 then y else if i = 2 then z else w), v = pair i u) L1).
let i.
assume Hi: i :e 4.
assume H1: exists u :e (if i = 0 then x else if i = 1 then y else if i = 2 then z else w), v = pair i u.
apply (exandE set (fun u => u :e if i = 0 then x else if i = 1 then y else if i = 2 then z else w) (fun u => v = pair i u) H1).
let u.
assume Hu : u :e if i = 0 then x else if i = 1 then y else if i = 2 then z else w.
assume H2: v = pair i u.
witness i.
prove i :e 4 /\ exists u:set, v = pair i u.
apply andI.
- exact Hi.
- witness u. exact H2.
Qed.

Theorem tuple_pair : forall x y:set, pair x y = (x,y).
let x y. apply set_ext.
- let z.
  assume Hz: z :e pair x y.
  apply (pairE x y z Hz).
  + assume H1: exists u :e x, z = pair 0 u.
    apply (exandE set (fun u => u :e x) (fun u => z = pair 0 u) H1).
    let u.
    assume Hu: u :e x.
    assume H2: z = pair 0 u.
    prove z :e (x,y).
    prove z :e fun i :e 2 => if i = 0 then x else y.
    rewrite H2.
    prove pair 0 u :e fun i :e 2 => if i = 0 then x else y.
    apply (lamI 2 (fun i => if i = 0 then x else y) 0 In_0_2 u).
    prove u :e if 0 = 0 then x else y.
    rewrite (If_1 set (0 = 0) x y (eqI set 0)).
    prove u :e x.
    exact Hu.
  + assume H1: exists u :e y, z = pair 1 u.
    apply (exandE set (fun u => u :e y) (fun u => z = pair 1 u) H1).
    let u.
    assume Hu: u :e y.
    assume H2: z = pair 1 u.
    prove z :e (x,y).
    prove z :e fun i :e 2 => if i = 0 then x else y.
    rewrite H2.
    prove pair 1 u :e fun i :e 2 => if i = 0 then x else y.
    apply (lamI 2 (fun i => if i = 0 then x else y) 1 In_1_2 u).
    prove u :e if 1 = 0 then x else y.
    rewrite (If_0 set (1 = 0) x y neq_1_0).
    prove u :e y.
    exact Hu.
- let z.
  assume Hz: z :e (x,y).
  prove z :e pair x y.
  claim L1: exists i :e 2, exists w :e (if i = 0 then x else y), z = pair i w.
  { exact (lamE 2 (fun i => if i = 0 then x else y) z Hz). }
  apply (exandE set (fun i => i :e 2) (fun i => exists w :e (if i = 0 then x else y), z = pair i w) L1).
  let i.
  assume Hi: i :e 2.
  assume H1: exists w :e (if i = 0 then x else y), z = pair i w.
  apply (exandE set (fun w => w :e if i = 0 then x else y) (fun w => z = pair i w) H1).
  let w.
  assume Hw: w :e if i = 0 then x else y.
  assume H2: z = pair i w.
  prove z :e pair x y.
  rewrite H2.
  prove pair i w :e pair x y.
  claim L2: i :e {0,1}.
  { exact (Subq_2_UPair01 i Hi). }
  apply (UPairE i 0 1 L2).
  + assume Hi0: i = 0.
    rewrite Hi0.
    prove pair 0 w :e pair x y.
    apply pairI0.
    prove w :e x.
    claim L3: (if i = 0 then x else y) = x.
    { exact (If_1 set (i = 0) x y Hi0). }
    rewrite <- L3.
    exact Hw.
  + assume Hi1: i = 1.
    rewrite Hi1.
    prove pair 1 w :e pair x y.
    apply pairI1.
    prove w :e y.
    claim L3: (if i = 0 then x else y) = y.
    {
      rewrite Hi1.
      exact (If_0 set (1 = 0) x y neq_1_0).
    }
    rewrite <- L3.
    exact Hw.
Qed.
