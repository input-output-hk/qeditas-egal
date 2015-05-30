(* Title "Introduction to Ordinals" *)
(* Author "Chad E. Brown" *)

(* Salt "tgrf8cu2HQz7s5oc" *)

(** Preamble **)
Section BasicSystemExercises1.
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
Axiom FalseE : forall P : prop , False -> P.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
Axiom andI : forall A B : prop , A -> B -> A /\ B.
Axiom andEL : forall A B : prop , A /\ B -> A.
Axiom andER : forall A B : prop , A /\ B -> B.
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Axiom orIL : forall A B : prop , A -> A \/ B.
Axiom orIR : forall A B : prop , B -> A \/ B.
Axiom orE : forall A B C : prop , (A -> C) -> (B -> C) -> A \/ B -> C.
Section PropN.
Variable P1 P2 P3 : prop.
Axiom or3I1 : P1 -> P1 \/ P2 \/ P3.
Axiom or3I2 : P2 -> P1 \/ P2 \/ P3.
Axiom or3I3 : P3 -> P1 \/ P2 \/ P3.
Axiom or3E : P1 \/ P2 \/ P3 -> (forall p : prop , (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> p).
End PropN.
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
Section RelnPoly1.
Variable A:SType.
Definition reflexive : (A->A->prop)->prop := fun R => forall x:A, R x x.
Definition irreflexive : (A->A->prop)->prop := fun R => forall x:A, ~R x x.
Definition antisymmetric : (A->A->prop)->prop := fun R => forall x y:A, R x y -> R y x -> x = y.
Definition transitive : (A->A->prop)->prop := fun R => forall x y z:A, R x y -> R y z -> R x z.
Definition linear : (A->A->prop)->prop := fun R => forall x y:A, R x y \/ R y x.
Definition trichotomous_or : (A->A->prop)->prop := fun R => forall x y:A, R x y \/ x = y \/ R y x.
Definition partialorder : (A->A->prop)->prop := fun R => reflexive R /\ antisymmetric R /\ transitive R.
Definition totalorder : (A->A->prop)->prop := fun R => partialorder R /\ linear R.
Definition strictpartialorder : (A->A->prop)->prop := fun R => irreflexive R /\ transitive R.
Definition stricttotalorder : (A->A->prop)->prop := fun R => strictpartialorder R /\ trichotomous_or R.
End RelnPoly1.
Axiom classic : forall P : prop , P \/ ~ P.
Definition exactly1of2 : prop -> prop -> prop := fun A B : prop => A /\ ~ B \/ ~ A /\ B.
Definition exactly1of3 : prop -> prop -> prop -> prop := fun A B C : prop => exactly1of2 A B /\ ~ C \/ ~ A /\ ~ B /\ C.
Axiom exactly1of3_I1 : forall A B C : prop , A -> ~ B -> ~ C -> exactly1of3 A B C.
Axiom exactly1of3_I2 : forall A B C : prop , ~ A -> B -> ~ C -> exactly1of3 A B C.
Axiom exactly1of3_I3 : forall A B C : prop , ~ A -> ~ B -> C -> exactly1of3 A B C.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Axiom Subq_ref : forall X : set , X c= X.
Axiom set_ext : forall X Y : set , X c= Y -> Y c= X -> X = Y.
(* Unicode Empty "2205" *)
Parameter Empty : set.
Axiom EmptyE : forall x : set , x /:e Empty.
(* Unicode Union "22C3" *)
Parameter Union : set -> set.
Axiom UnionE2 : forall X x : set , x :e (Union X) -> forall p : prop , (forall Y : set , x :e Y -> Y :e X -> p) -> p.
Axiom UnionI : forall X x Y : set , x :e Y -> Y :e X -> x :e (Union X).
Axiom In_ind : forall P : set -> prop , (forall X : set , (forall x : set , x :e X -> P x) -> P X) -> forall X : set , P X.
Axiom In_irref : forall x , x /:e x.
Axiom In_no2cycle : forall x y , x :e y -> y /:e x.
(* Parameter ordsucc MJAVHZ4UTjfNkP94R1Y274wA1jSL4zvYwwczio73KbaM1Zkf *)
Parameter ordsucc : set -> set.
Axiom ordsuccI1 : forall x : set , x c= ordsucc x.
Axiom ordsuccI2 : forall x : set , x :e ordsucc x.
Axiom ordsuccE : forall x y : set , y :e ordsucc x -> y :e x \/ y = x.
Notation Nat Empty ordsucc.
Definition nat_p : set -> prop := fun n : set => forall p : set -> prop , p 0 -> (forall x : set , p x -> p (ordsucc x)) -> p n.
Axiom nat_ind : forall p : set -> prop , p 0 -> (forall n , nat_p n -> p n -> p (ordsucc n)) -> forall n , nat_p n -> p n.
Axiom nat_p_trans : forall n , nat_p n -> forall m :e n , nat_p m.
(* Parameter omega MGrsGXyVjZQXLz9e4WKX4oemBXWYjVvmoieFHPb5kLfJQc3c *)
Parameter omega : set.
Axiom omega_nat_p : forall n :e omega , nat_p n.
Axiom nat_p_omega : forall n : set , nat_p n -> n :e omega.

(** Main Body **)

(* Unicode alpha "3b1" *)
(* Unicode beta "3b2" *)
(* Unicode gamma "3b3" *)
(* Unicode delta "3b4" *)

Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Theorem ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.
exact (fun alpha H => andEL (TransSet alpha) (forall beta :e alpha, TransSet beta) H).
Qed.

Theorem ordinal_In_TransSet : forall alpha:set, ordinal alpha -> forall beta :e alpha, TransSet beta.
exact (fun alpha H => andER (TransSet alpha) (forall beta :e alpha, TransSet beta) H).
Qed.

Theorem ordinal_Empty : ordinal Empty.
prove TransSet Empty /\ forall x :e Empty, TransSet x.
apply andI.
- let x.
  assume Hx: x :e Empty.
  prove False.
  exact (EmptyE x Hx).
- let x.
  assume Hx: x :e Empty.
  prove False.
  exact (EmptyE x Hx).
Qed.

Theorem ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.
let alpha.
assume H1: TransSet alpha /\ forall x :e alpha, TransSet x.
let beta.
assume H2: beta :e alpha.
prove TransSet beta /\ forall x :e beta, TransSet x.
apply H1.
assume H3: TransSet alpha.
assume H4: forall x :e alpha, TransSet x.
apply andI.
- exact (H4 beta H2).
- prove forall x :e beta, TransSet x.
  let x.
  assume Hx: x :e beta.
  claim L1: x :e alpha.
  { exact (H3 beta H2 x Hx). }
  prove TransSet x.
  exact (H4 x L1).
Qed.

Theorem ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.
let p.
assume H1: forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha.
apply In_ind.
let alpha.
assume IH: forall beta :e alpha, ordinal beta -> p beta.
assume H2: ordinal alpha.
prove p alpha.
apply (H1 alpha H2).
let beta.
assume H3: beta :e alpha.
prove p beta.
apply (IH beta H3).
prove ordinal beta.
exact (ordinal_Hered alpha H2 beta H3).
Qed.

Theorem TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).
let X.
assume H1: TransSet X.
let x.
assume H2: x :e ordsucc X.
let y.
assume H3: y :e x.
prove y :e ordsucc X.
apply (ordsuccE X x H2).
- assume H4: x :e X.
  apply ordsuccI1.
  prove y :e X.
  exact (H1 x H4 y H3).
- assume H4: x = X.
  apply ordsuccI1.
  prove y :e X.
  rewrite <- H4.
  prove y :e x.
  exact H3.
Qed.

Theorem ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).
let alpha.
assume H1: TransSet alpha /\ forall beta :e alpha, TransSet beta.
apply H1.
assume H2: TransSet alpha.
assume H3: forall beta :e alpha, TransSet beta.
prove TransSet (ordsucc alpha) /\ forall beta :e ordsucc alpha, TransSet beta.
apply andI.
- exact (TransSet_ordsucc alpha H2).
- let beta.
  assume H4: beta :e ordsucc alpha.
  prove TransSet beta.
  apply (ordsuccE alpha beta H4).
  + assume H5: beta :e alpha.
    exact (H3 beta H5).
  + assume H5: beta = alpha.
    rewrite H5.
    exact H2.
Qed.

Theorem nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
apply nat_ind.
- prove ordinal 0.
  exact ordinal_Empty.
- let n.
  assume Hn: nat_p n.
  assume IHn: ordinal n.
  prove ordinal (ordsucc n).
  exact (ordinal_ordsucc n IHn).
Qed.

Theorem omega_TransSet : TransSet omega.
let n.
assume Hn: n :e omega.
let m.
assume Hm: m :e n.
prove m :e omega.
apply nat_p_omega.
prove nat_p m.
apply (nat_p_trans n).
- prove nat_p n. exact (omega_nat_p n Hn).
- prove m :e n. exact Hm.
Qed.

Theorem omega_ordinal : ordinal omega.
prove TransSet omega /\ forall n :e omega, TransSet n.
apply andI.
- exact omega_TransSet.
- let n.
  assume Hn: n :e omega.
  prove TransSet n.
  apply ordinal_TransSet.
  prove ordinal n.
  apply nat_p_ordinal.
  prove nat_p n.
  exact (omega_nat_p n Hn).
Qed.

Theorem TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.
let X.
assume H1: TransSet X.
let x.
assume H2: x :e X.
let y.
assume H3: y :e ordsucc x.
prove y :e X.
apply (ordsuccE x y H3).
- assume H4: y :e x.
  exact (H1 x H2 y H4).
- assume H4: y = x.
  rewrite H4.
  prove x :e X.
  exact H2.
Qed.

Theorem ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.
let alpha.
assume H: ordinal alpha.
exact (TransSet_ordsucc_In_Subq alpha (ordinal_TransSet alpha H)).
Qed.

Theorem ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply In_ind.
let alpha.
assume IHalpha: forall gamma :e alpha, forall beta:set, ordinal gamma -> ordinal beta -> gamma :e beta \/ gamma = beta \/ beta :e gamma.
prove forall beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply In_ind.
let beta.
assume IHbeta: forall delta :e beta, ordinal alpha -> ordinal delta -> alpha :e delta \/ alpha = delta \/ delta :e alpha.
assume Halpha : ordinal alpha.
assume Hbeta : ordinal beta.
prove alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply (classic (alpha :e beta)).
- assume H1: alpha :e beta.
  apply or3I1.
  exact H1.
- assume H1: alpha /:e beta.
  apply (classic (beta :e alpha)).
  + assume H2: beta :e alpha.
    apply or3I3.
    exact H2.
  + assume H2: beta /:e alpha.
    apply or3I2.
    prove alpha = beta.
    apply set_ext.
    * { prove alpha c= beta.
        let gamma.
	assume H3: gamma :e alpha.
	prove gamma :e beta.
	claim Lgamma: ordinal gamma.
	{ exact (ordinal_Hered alpha Halpha gamma H3). }
	apply (or3E (gamma :e beta) (gamma = beta) (beta :e gamma) (IHalpha gamma H3 beta Lgamma Hbeta)).
	- assume H4: gamma :e beta.
	  exact H4.
        - assume H4: gamma = beta.
          prove False.
          apply H2.
          prove beta :e alpha.
	  rewrite <- H4.
	  exact H3.
        - assume H4: beta :e gamma.
          prove False.
          apply H2.
          prove beta :e alpha.
          exact (ordinal_TransSet alpha Halpha gamma H3 beta H4).
      }
    * { prove beta c= alpha.
        let delta.
	assume H3: delta :e beta.
	prove delta :e alpha.
	claim Ldelta: ordinal delta.
	{ exact (ordinal_Hered beta Hbeta delta H3). }
	apply (or3E (alpha :e delta) (alpha = delta) (delta :e alpha) (IHbeta delta H3 Halpha Ldelta)).
        - assume H4: alpha :e delta.
          prove False.
          apply H1.
          prove alpha :e beta.
          exact (ordinal_TransSet beta Hbeta delta H3 alpha H4).
        - assume H4: alpha = delta.
          prove False.
          apply H1.
          prove alpha :e beta.
	  rewrite H4.
	  exact H3.
	- assume H4: delta :e alpha.
	  exact H4.
      }
Qed.    

Theorem ordinal_trichotomy : forall alpha beta:set,
 ordinal alpha -> ordinal beta -> exactly1of3 (alpha :e beta) (alpha = beta) (beta :e alpha).
let alpha beta.
assume H1: ordinal alpha.
assume H2: ordinal beta.
apply (or3E (alpha :e beta) (alpha = beta) (beta :e alpha) (ordinal_trichotomy_or alpha beta H1 H2)).
- assume H3: alpha :e beta.
  apply exactly1of3_I1.
  + prove alpha :e beta.
    exact H3.
  + prove alpha <> beta.
    assume H4: alpha = beta.
    apply (In_irref alpha).
    prove alpha :e alpha.
    rewrite H4 at 2.
    exact H3.
  + prove beta /:e alpha.
    assume H4: beta :e alpha.
    exact (In_no2cycle alpha beta H3 H4).
- assume H3: alpha = beta.
  apply exactly1of3_I2.
  + prove alpha /:e beta.
    rewrite H3.
    apply In_irref.
  + prove alpha = beta.
    exact H3.
  + prove beta /:e alpha.
    rewrite H3.
    apply In_irref.
- assume H3: beta :e alpha.
  apply exactly1of3_I3.
  + prove alpha /:e beta.
    assume H4: alpha :e beta.
    exact (In_no2cycle alpha beta H4 H3).
  + prove alpha <> beta.
    assume H4: alpha = beta.
    apply (In_irref alpha).
    prove alpha :e alpha.
    rewrite H4 at 1.
    exact H3.
  + prove beta :e alpha.
    exact H3.
Qed.

Theorem ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.
let alpha beta.
assume H1: ordinal alpha.
assume H2: ordinal beta.
apply (or3E (alpha :e beta) (alpha = beta) (beta :e alpha) (ordinal_trichotomy_or alpha beta H1 H2)).
- assume H3: alpha :e beta.
  apply orIL.
  exact H3.
- assume H3: alpha = beta.
  apply orIR.
  rewrite H3.
  apply Subq_ref.
- assume H3: beta :e alpha.
  apply orIR.
  exact (ordinal_TransSet alpha H1 beta H3).
Qed.

Theorem ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.
let alpha beta.
assume H1: ordinal alpha.
assume H2: ordinal beta.
apply (ordinal_In_Or_Subq alpha beta H1 H2).
- assume H3: alpha :e beta.
  apply orIL.
  exact (ordinal_TransSet beta H2 alpha H3).
- assume H3: beta c= alpha.
  apply orIR.
  exact H3.
Qed.
