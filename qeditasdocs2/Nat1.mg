(* Title "Natural Numbers as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2nPDtwmgvfam3ctmf" *)

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
Axiom andEL : forall A B : prop , A /\ B -> A.
Axiom andER : forall A B : prop , A /\ B -> B.
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Axiom orIL : forall A B : prop , A -> A \/ B.
Axiom orIR : forall A B : prop , B -> A \/ B.
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
Section Poly1_exthms.
Variable A : SType.
Axiom exI : forall P : A -> prop , forall x : A , P x -> exists x : A , P x.
End Poly1_exthms.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Definition nSubq : set -> set -> prop := fun X Y => ~ Subq X Y.
(* Unicode /c= "2288" *)
Infix /c= 502 := nSubq.
Axiom Subq_ref : forall X : set , X c= X.
Axiom Subq_tra : forall X Y Z : set , X c= Y -> Y c= Z -> X c= Z.
Binder+ exists , := ex ; and.
Axiom set_ext : forall X Y : set , X c= Y -> Y c= X -> X = Y.
(* Unicode Empty "2205" *)
Parameter Empty : set.
Axiom EmptyE : forall x : set , x /:e Empty.
Axiom Subq_Empty : forall X : set , Empty c= X.
(* Unicode Union "22C3" *)
Parameter Union : set -> set.
Axiom UnionE2 : forall X x : set , x :e (Union X) -> forall p : prop , (forall Y : set , x :e Y -> Y :e X -> p) -> p.
Axiom UnionI : forall X x Y : set , x :e Y -> Y :e X -> x :e (Union X).
(* Parameter UPair MM7DGQPznayt6juAGExgMfTfAFmB3TUo5yTKCJZ37zpfyzJN *)
Parameter UPair : set -> set -> set.
Notation SetEnum2 UPair.
Axiom UPairE : forall x y z : set , x :e {y,z} -> x = y \/ x = z.
Axiom UPairI1 : forall y z : set , y :e {y,z}.
Axiom UPairI2 : forall y z : set , z :e {y,z}.
(* Parameter Sing MHQKaPMuqpPD7JYxt91FMGRr1nnP2YZ3625uoySLjwF6JjbU *)
Parameter Sing : set -> set.
Notation SetEnum1 Sing.
Axiom SingI : forall x : set , x :e {x}.
Axiom SingE : forall x y : set , y :e {x} -> y = x.
(* Parameter binunion ML3UdJ5oRKTbTCgPXuRbFVretWXebaxqPiNqmx7tWWJMoYBi *)
Parameter binunion : set -> set -> set.
(* Unicode :\/: "222a" *)
Infix :\/: 345 left  := binunion.
Axiom binunionI1 : forall X Y z : set , z :e X -> z :e X :\/: Y.
Axiom binunionI2 : forall X Y z : set , z :e Y -> z :e X :\/: Y.
Axiom binunionE : forall X Y z : set , z :e X :\/: Y -> z :e X \/ z :e Y.
Axiom In_irref : forall x , x /:e x.
Axiom In_no2cycle : forall x y , x :e y -> y /:e x.

(** Main Body **)

Definition ordsucc : set->set := fun x:set => x :\/: {x}.

Lemma ordsuccI1 : forall x:set, x c= ordsucc x.
exact (fun (x y : set) (H1 : y :e x) => binunionI1 x {x} y H1).
Qed.

Lemma ordsuccI2 : forall x:set, x :e ordsucc x.
exact (fun x : set => binunionI2 x {x} x (SingI x)).
Qed.

Lemma ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
let x y.
assume H1: y :e x :\/: {x}.
apply (binunionE x {x} y H1).
- assume H2: y :e x. apply orIL. exact H2.
- assume H2: y :e {x}. apply orIR. exact (SingE x y H2).
Qed.

Notation Nat Empty ordsucc.

Lemma neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
let a.
assume H1: 0 = ordsucc a.
claim L1: a /:e ordsucc a.
{ rewrite <- H1. exact (EmptyE a). }
exact (L1 (ordsuccI2 a)).
Qed.

Lemma neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
exact (fun (a : set) (H1 : ordsucc a = 0) => neq_0_ordsucc a (eq_sym set (ordsucc a) 0 H1)).
Qed.

Lemma ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
let a b.
assume H1: ordsucc a = ordsucc b.
claim L1: a :e ordsucc b.
{
  rewrite <- H1.
  exact (ordsuccI2 a).
}
apply (ordsuccE b a L1).
- assume H2: a :e b.
  claim L2: b :e ordsucc a.
  {
    rewrite H1.
    exact (ordsuccI2 b).
  }
  apply (ordsuccE a b L2).
  + assume H3: b :e a. prove False. exact (In_no2cycle a b H2 H3).
  + assume H3: b = a. apply (eq_sym set). exact H3.
- assume H2: a = b. exact H2.
Qed.

Lemma ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.
exact (fun a b H1 H2 => H1 (ordsucc_inj a b H2)).
Qed.

Lemma In_0_1 : 0 :e 1.
exact (ordsuccI2 0).
Qed.

Lemma In_1_2 : 1 :e 2.
exact (ordsuccI2 1).
Qed.

Lemma In_0_2 : 0 :e 2.
exact (ordsuccI1 1 0 In_0_1).
Qed.

Lemma neq_0_1 : 0 <> 1.
exact (neq_0_ordsucc 0).
Qed.

Lemma neq_1_0 : 1 <> 0.
exact (neq_ordsucc_0 0).
Qed.

Lemma neq_0_2 : 0 <> 2.
exact (neq_0_ordsucc 1).
Qed.

Lemma neq_2_0 : 2 <> 0.
exact (neq_ordsucc_0 1).
Qed.

Lemma neq_1_2 : 1 <> 2.
exact (ordsucc_inj_contra 0 1 neq_0_1).
Qed.

Lemma neq_2_1 : 2 <> 1.
exact (ordsucc_inj_contra 1 0 neq_1_0).
Qed.

Lemma nIn_0_0 : 0 /:e 0.
exact (EmptyE 0).
Qed.

Lemma nIn_1_0 : 1 /:e 0.
exact (EmptyE 1).
Qed.

Lemma nIn_2_0 : 2 /:e 0.
exact (EmptyE 2).
Qed.

Lemma nIn_1_1 : 1 /:e 1.
exact (In_irref 1).
Qed.

Lemma nIn_2_1 : 2 /:e 1.
exact (fun H => ordsuccE 0 2 H False (EmptyE 2) neq_2_0).
Qed.

Lemma nIn_2_2 : 2 /:e 2.
exact (In_irref 2).
Qed.

Lemma Subq_0_0 : 0 c= 0.
exact (Subq_Empty 0).
Qed.

Lemma Subq_0_1 : 0 c= 1.
exact (Subq_Empty 1).
Qed.

Lemma Subq_0_2 : 0 c= 2.
exact (Subq_Empty 2).
Qed.

Lemma nSubq_1_0 : 1 /c= 0.
exact (fun H => nIn_0_0 (H 0 In_0_1)).
Qed.

Lemma Subq_1_1 : 1 c= 1.
exact (Subq_ref 1).
Qed.

Lemma Subq_1_2 : 1 c= 2.
exact (ordsuccI1 1).
Qed.

Lemma nSubq_2_0 : 2 /c= 0.
exact (fun H => nIn_0_0 (H 0 In_0_2)).
Qed.

Lemma nSubq_2_1 : 2 /c= 1.
exact (fun H => nIn_1_1 (H 1 In_1_2)).
Qed.

Lemma Subq_2_2 : 2 c= 2.
exact (Subq_ref 2).
Qed.

Lemma Subq_1_Sing0 : 1 c= {0}.
let x.
assume H1: x :e 1.
prove x :e {0}.
apply (ordsuccE 0 x H1).
- assume H2: x :e 0.
  prove False.
  exact (EmptyE x H2).
- assume H2: x = 0.
  rewrite H2.
  prove 0 :e {0}.
  exact (SingI 0).
Qed.

Lemma Subq_Sing0_1 : {0} c= 1.
exact (fun x H1 => SingE 0 x H1 (fun s : set => x :e ordsucc s) (ordsuccI2 x)).
Qed.

Lemma eq_1_Sing0 : 1 = {0}.
exact (set_ext 1 (Sing 0) Subq_1_Sing0 Subq_Sing0_1).
Qed.

Lemma Subq_2_UPair01 : 2 c= {0,1}.
let x.
assume H1: x :e 2.
apply (ordsuccE 1 x H1).
- assume H2: x :e 1.
  claim L1: x = 0.
  { exact (SingE 0 x (Subq_1_Sing0 x H2)). }
  prove x :e {0,1}.
  rewrite L1.
  prove 0 :e {0,1}.
  exact (UPairI1 0 1).
- assume H2: x = 1.
  prove x :e {0,1}.
  rewrite H2.
  prove 1 :e {0,1}.
  exact (UPairI2 0 1).
Qed.

Lemma Subq_UPair01_2 : {0,1} c= 2.
let x.
assume H1: x :e {0,1}.
apply (UPairE x 0 1 H1).
- assume H2: x = 0.
  prove x :e 2.
  rewrite H2.
  prove 0 :e 2.
  exact In_0_2.
- assume H2: x = 1.
  prove x :e 2.
  rewrite H2.
  prove 1 :e 2.
  exact In_1_2.
Qed.

Lemma eq_2_UPair01 : 2 = {0,1}.
exact (set_ext 2 {0, 1} Subq_2_UPair01 Subq_UPair01_2).
Qed.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

Lemma nat_0 : nat_p 0.
exact (fun p H _ => H).
Qed.

Lemma nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
exact (fun n H1 p H2 H3 => H3 n (H1 p H2 H3)).
Qed.

Lemma nat_1 : nat_p 1.
exact (nat_ordsucc 0 nat_0).
Qed.

Lemma nat_2 : nat_p 2.
exact (nat_ordsucc 1 nat_1).
Qed.

Lemma nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
let n.
assume H1: nat_p n.
apply (H1 (fun n => 0 :e ordsucc n)).
- prove 0 :e ordsucc 0.
  exact In_0_1.
- let n.
  assume IH: 0 :e ordsucc n.
  prove 0 :e ordsucc (ordsucc n).
  exact (ordsuccI1 (ordsucc n) 0 IH).
Qed.

Lemma nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
let n.
assume H1: nat_p n.
apply (H1 (fun n => forall m :e n, ordsucc m :e ordsucc n)).
- prove forall m :e 0, ordsucc m :e ordsucc 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume IH: forall m :e n, ordsucc m :e ordsucc n.
  prove forall m :e ordsucc n, ordsucc m :e ordsucc (ordsucc n).
  let m.
  assume H2: m :e ordsucc n.
  prove ordsucc m :e ordsucc (ordsucc n).
  apply (ordsuccE n m H2).
  + assume H3: m :e n.
    claim L1: ordsucc m :e ordsucc n.
    { exact (IH m H3). }
    exact (ordsuccI1 (ordsucc n) (ordsucc m) L1).
  + assume H3: m = n.
    rewrite H3.
    prove ordsucc n :e ordsucc (ordsucc n).
    exact (ordsuccI2 (ordsucc n)).
Qed.

Lemma nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
let p.
assume H1: p 0.
assume H2: forall n, nat_p n -> p n -> p (ordsucc n).
claim L1: nat_p 0 /\ p 0.
{
  exact (andI (nat_p 0) (p 0) nat_0 H1).
}
claim L2: forall n, nat_p n /\ p n -> nat_p (ordsucc n) /\ p (ordsucc n).
{
  let n.
  assume H3: nat_p n /\ p n.
  apply H3.
  assume H4: nat_p n.
  assume H5: p n.
  apply andI.
  - prove nat_p (ordsucc n).
    exact (nat_ordsucc n H4).
  - prove p (ordsucc n).
    exact (H2 n H4 H5).
}
let n.
assume H3: nat_p n.
claim L3: nat_p n /\ p n.
{ exact (H3 (fun n => nat_p n /\ p n) L1 L2). }
exact (andER (nat_p n) (p n) L3).
Qed.

Lemma nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
apply nat_ind.
- prove 0 = 0 \/ exists x, nat_p x /\ 0 = ordsucc x.
  apply orIL.
  apply (eqI set).
- let n.
  assume H1 _.
  prove ordsucc n = 0 \/ exists x, nat_p x /\ ordsucc n = ordsucc x.
  apply orIR.
  witness n.
  apply andI.
  + exact H1.
  + apply (eqI set).
Qed.

Lemma nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
let p.
assume H1: forall n, nat_p n -> (forall m :e n, p m) -> p n.
claim L1: forall n:set, nat_p n -> forall m :e n, p m.
{
  apply nat_ind.
  - prove forall m :e 0, p m.
    let m.
    assume Hm: m :e 0.
    prove False.
    exact (EmptyE m Hm).
  - let n.
    assume Hn: nat_p n.
    assume IHn: forall m :e n, p m.
    prove forall m :e ordsucc n, p m.
    let m.
    assume Hm: m :e ordsucc n.
    prove p m.
    apply (ordsuccE n m Hm).
    + assume H2: m :e n.
      exact (IHn m H2).
    + assume H2: m = n.
      prove p m.
      rewrite H2.
      prove p n.
      exact (H1 n Hn IHn).
}
prove forall n, nat_p n -> p n.
exact (fun n Hn => H1 n Hn (L1 n Hn)).
Qed.

Lemma nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
apply nat_ind.
- prove forall m :e 0, nat_p m.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, nat_p m.
  prove forall m :e ordsucc n, nat_p m.
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    exact (IHn m H1).
  + assume H1: m = n.
    rewrite H1.
    exact Hn.
Qed.

Lemma nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
apply nat_ind.
- prove forall m :e 0, m c= 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, m c= n.
  prove forall m :e ordsucc n, m c= ordsucc n.
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    prove m c= ordsucc n.
    apply (Subq_tra m n (ordsucc n)).
    * exact (IHn m H1).
    * exact (ordsuccI1 n).
  + assume H1: m = n.
    prove m c= ordsucc n.
    rewrite H1.
    prove n c= ordsucc n.
    exact (ordsuccI1 n).
Qed.

Lemma nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.
let n.
assume Hn: nat_p n.
let m.
assume Hm: m :e ordsucc n.
let k.
assume Hk: k :e m.
prove k :e n.
apply (ordsuccE n m Hm).
- assume H1: m :e n.
  exact (nat_trans n Hn m H1 k Hk).
- assume H1: m = n.
  rewrite <- H1.
  exact Hk.
Qed.

Lemma Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.
apply nat_complete_ind.
let n.
assume Hn: nat_p n.
assume IHn: forall m :e n, Union (ordsucc m) = m.
prove Union (ordsucc n) = n.
apply set_ext.
- let m.
  assume Hm: m :e Union (ordsucc n).
  apply (UnionE2 (ordsucc n) m Hm).
  let k.
  assume H1: m :e k.
  assume H2: k :e ordsucc n.
  prove m :e n.
  exact (nat_ordsucc_trans n Hn k H2 m H1).
- let m.
  assume Hm: m :e n.
  prove m :e Union (ordsucc n).
  apply (UnionI (ordsucc n) m n).
  + exact Hm.
  + exact (ordsuccI2 n).
Qed.
