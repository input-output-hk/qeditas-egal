(* Title "Disjoint Unions" *)
(* Author "Chad E. Brown" *)

(* Salt "3HmtMxzQo7ZHzs1du" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
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
Section Poly1.
Variable A : SType.
Variable P : A -> prop.
Variable Q : A -> prop.
Axiom exandE : (exists x : A , P x /\ Q x) -> forall p : prop , (forall x : A , P x -> Q x -> p) -> p.
End Poly1.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Binder+ exists , := ex ; and.
Axiom set_ext : forall X Y : set , X c= Y -> Y c= X -> X = Y.
(* Unicode Empty "2205" *)
Parameter Empty : set.
Axiom EmptyE : forall x : set , x /:e Empty.
Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.
Axiom ReplE : forall X : set , forall F : set -> set , forall y : set , y :e {F x|x :e X} -> exists x : set , x :e X /\ y = F x.
Axiom ReplE2 : forall X : set , forall F : set -> set , forall y : set , y :e {F x|x :e X} -> forall p : prop , (forall x : set , x :e X -> y = F x -> p) -> p.
Axiom ReplI : forall X : set , forall F : set -> set , forall x : set , x :e X -> F x :e {F x|x :e X}.
Axiom Repl_Empty : forall F : set -> set , {F x|x :e Empty} = Empty.
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
(* Parameter setminus MM2vZGhovsWD5SmnoAE8Rbigs7TsyoBfdzgq2k3UACNamCG7 *)
Parameter setminus : set -> set -> set.
(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.
Axiom setminusI : forall X Y z , (z :e X) -> (z /:e Y) -> z :e X :\: Y.
Axiom setminusE : forall X Y z , (z :e X :\: Y) -> z :e X /\ z /:e Y.
Axiom setminusE1 : forall X Y z , (z :e X :\: Y) -> z :e X.
Axiom Repl_restr : forall X : set , forall F G : set -> set , (forall x : set , x :e X -> F x = G x) -> {F x|x :e X} = {G x|x :e X}.
Axiom In_ind : forall P : set -> prop , (forall X : set , (forall x : set , x :e X -> P x) -> P X) -> forall X : set , P X.
(* Parameter In_rec MK74iPEyb2n2boTzfPvwdtg5EW5kMbn6cAH6g2Bpcyn2bpow *)
Parameter In_rec : (set -> (set -> set) -> set) -> set -> set.
Axiom In_rec_eq : forall F : set -> (set -> set) -> set , (forall X : set , forall g h : set -> set , (forall x , x :e X -> g x = h x) -> F X g = F X h) -> forall X : set , In_rec F X = F X (In_rec F).
(* Parameter ordsucc MJAVHZ4UTjfNkP94R1Y274wA1jSL4zvYwwczio73KbaM1Zkf *)
Parameter ordsucc : set -> set.
Axiom ordsuccI2 : forall x : set , x :e ordsucc x.
Axiom ordsuccE : forall x y : set , y :e ordsucc x -> y :e x \/ y = x.
Notation Nat Empty ordsucc.
Axiom In_0_1 : 0 :e 1.
Axiom Subq_1_Sing0 : 1 c= {0}.
Definition nat_p : set -> prop := fun n : set => forall p : set -> prop , p 0 -> (forall x : set , p x -> p (ordsucc x)) -> p n.
Axiom nat_0 : nat_p 0.
Axiom nat_ordsucc : forall n : set , nat_p n -> nat_p (ordsucc n).
Axiom nat_1 : nat_p 1.
Axiom nat_ordsucc_in_ordsucc : forall n , nat_p n -> forall m :e n , ordsucc m :e ordsucc n.
Axiom nat_inv : forall n , nat_p n -> n = 0 \/ exists x , nat_p x /\ n = ordsucc x.
Axiom nat_p_trans : forall n , nat_p n -> forall m :e n , nat_p m.
Axiom nat_trans : forall n , nat_p n -> forall m :e n , m c= n.
Axiom nat_complete_ind : forall p : set -> prop , (forall n , nat_p n -> (forall m :e n , p m) -> p n) -> forall n , nat_p n -> p n.
Axiom nat_0_in_ordsucc : forall n , nat_p n -> 0 :e ordsucc n.

(** Main Body **)

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec (fun X f => {0} :\/: {f x|x :e X}).

Theorem Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
claim L1: forall X:set, forall g h:set->set, (forall x :e X, g x = h x)
                         -> {0} :\/: {g x|x :e X} = {0} :\/: {h x|x :e X}.
{
  let X g h.
   assume H: forall x :e X, g x = h x.
   claim L1a: {g x|x :e X} = {h x|x :e X}.
   {
     exact (Repl_restr X g h H).
   }
   prove {0} :\/: {g x|x :e X} = {0} :\/: {h x|x :e X}.
   rewrite L1a.
   apply (eqI set).
}
exact (In_rec_eq (fun X f => {0} :\/: {f x|x :e X}) L1).
Qed.

Theorem Inj1I1 : forall X:set, 0 :e Inj1 X.
let X.
rewrite (Inj1_eq X).
prove 0 :e {0} :\/: {Inj1 x|x :e X}.
apply binunionI1.
apply SingI.
Qed.

Theorem Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
let X x.
assume H: x :e X.
rewrite (Inj1_eq X).
prove Inj1 x :e {0} :\/: {Inj1 x|x :e X}.
apply binunionI2.
exact (ReplI X Inj1 x H).
Qed.

Theorem Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
let X y.
rewrite (Inj1_eq X).
assume H1: y :e {0} :\/: {Inj1 x|x :e X}.
prove y = 0 \/ exists x :e X, y = Inj1 x.
apply (binunionE {0} {Inj1 x|x :e X} y H1).
- assume H2: y :e {0}.
  apply orIL.
  exact (SingE 0 y H2).
- assume H2: y :e {Inj1 x|x :e X}.
  apply orIR.
  prove exists x :e X, y = Inj1 x.
  exact (ReplE X Inj1 y H2).
Qed.

Theorem Inj1NE1 : forall x:set, Inj1 x <> 0.
let x.
assume H1: Inj1 x = 0.
apply (EmptyE 0).
prove 0 :e 0.
rewrite <- H1 at 2.
prove 0 :e Inj1 x.
exact (Inj1I1 x).
Qed.

Theorem Inj1NE2 : forall x:set, Inj1 x /:e {0}.
let x.
assume H1: Inj1 x :e {0}.
exact (Inj1NE1 x (SingE 0 (Inj1 x) H1)).
Qed.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

Theorem Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
exact (fun X x H => ReplI X Inj1 x H).
Qed.

Theorem Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.
exact (fun X y H => ReplE X Inj1 y H).
Qed.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec (fun X f => {f x|x :e X :\: {0}}).

Theorem Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
claim L1: forall X:set, forall g h:set->set, (forall x :e X, g x = h x) -> {g x|x :e X :\: {0}} = {h x|x :e X :\: {0}}.
{
  let X g h.
  assume H1: forall x :e X, g x = h x.
  prove {g x|x :e X :\: {0}} = {h x|x :e X :\: {0}}.
  apply (Repl_restr (X :\: {0}) g h).
  let x.
  assume H2: x :e X :\: {0}.
  prove g x = h x.
  apply H1.
  prove x :e X.
  exact (setminusE1 X {0} x H2).
}
exact (In_rec_eq (fun X f => {f x|x :e X :\: {0}}) L1).
Qed.

Theorem Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
apply In_ind.
let X.
assume IH: forall x :e X, Unj (Inj1 x) = x.
prove Unj (Inj1 X) = X.
rewrite Unj_eq.
prove {Unj x|x :e Inj1 X :\: {0}} = X.
apply set_ext.
- prove {Unj x|x :e Inj1 X :\: {0}} c= X.
  let x.
  assume H1: x :e {Unj x|x :e Inj1 X :\: {0}}.
  prove x :e X.
  apply (ReplE2 (Inj1 X :\: {0}) Unj x H1).
  let y.
  assume H2: y :e Inj1 X :\: {0}.
  assume H3: x = Unj y.
  rewrite H3.
  prove Unj y :e X.
  apply (setminusE (Inj1 X) {0} y H2).
  assume H4: y :e Inj1 X.
  assume H5: y /:e {0}.
  apply (Inj1E X y H4).
  + assume H6: y = 0.
    prove False.
    apply H5.
    rewrite H6.
    prove 0 :e {0}.
    apply SingI.
  + assume H6: exists x :e X, y = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => y = Inj1 x) H6).
    let z.
    assume H7: z :e X.
    assume H8: y = Inj1 z.
    rewrite H8.
    prove Unj (Inj1 z) :e X.
    rewrite (IH z H7).
    prove z :e X.
    exact H7.
- prove X c= {Unj x|x :e Inj1 X :\: {0}}.
  let x.
  assume H1: x :e X.
  prove x :e {Unj x|x :e Inj1 X :\: {0}}.
  rewrite <- (IH x H1).
  prove Unj (Inj1 x) :e {Unj x|x :e Inj1 X :\: {0}}.
  apply (ReplI (Inj1 X :\: {0}) Unj).
  prove Inj1 x :e Inj1 X :\: {0}.
  apply setminusI.
  + exact (Inj1I2 X x H1).
  + prove Inj1 x /:e {0}.
    exact (Inj1NE2 x).
Qed.

Theorem Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
let X Y.
assume H1: Inj1 X = Inj1 Y.
prove X = Y.
rewrite <- (Unj_Inj1_eq X).
rewrite <- (Unj_Inj1_eq Y).
rewrite H1.
apply (eqI set).
Qed.

Theorem Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
let X.
rewrite (Unj_eq (Inj0 X)).
prove {Unj x|x :e Inj0 X :\: {0}} = X.
apply set_ext.
- prove {Unj x|x :e Inj0 X :\: {0}} c= X.
  let x.
  assume H1: x :e {Unj x|x :e Inj0 X :\: {0}}.
  prove x :e X.
  apply (ReplE2 (Inj0 X :\: {0}) Unj x H1).
  let y.
  assume H2: y :e Inj0 X :\: {0}.
  assume H3: x = Unj y.
  apply (setminusE (Inj0 X) {0} y H2).
  assume H4: y :e {Inj1 x|x :e X}.
  assume H5: y /:e {0}.
  apply (ReplE2 X Inj1 y H4).
  let z.
  assume H6: z :e X.
  assume H7: y = Inj1 z.
  claim L1: x = z.
  {
    rewrite H3.
    prove Unj y = z.
    rewrite H7.
    prove Unj (Inj1 z) = z.
    exact (Unj_Inj1_eq z).
  }
  prove x :e X.
  rewrite L1.
  prove z :e X.
  exact H6.
- prove X c= {Unj x|x :e Inj0 X :\: {0}}.
  let x.
  assume H1: x :e X.
  prove x :e {Unj x|x :e Inj0 X :\: {0}}.
  rewrite <- (Unj_Inj1_eq x).
  prove Unj (Inj1 x) :e {Unj x|x :e Inj0 X :\: {0}}.
  apply (ReplI (Inj0 X :\: {0}) Unj).
  prove Inj1 x :e Inj0 X :\: {0}.
  apply setminusI.
  + prove Inj1 x :e {Inj1 x|x :e X}.
    apply ReplI.
    exact H1.
  + prove Inj1 x /:e {0}.
    exact (Inj1NE2 x).
Qed.

Theorem Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
let X Y.
assume H1: Inj0 X = Inj0 Y.
prove X = Y.
rewrite <- (Unj_Inj0_eq X).
rewrite <- (Unj_Inj0_eq Y).
rewrite H1.
apply (eqI set).
Qed.

Theorem Inj0_0 : Inj0 0 = 0.
exact (Repl_Empty Inj1).
Qed.

Theorem Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.
let X Y.
assume H1 : Inj0 X = Inj1 Y.
claim L1: 0 :e Inj1 Y.
{ exact (Inj1I1 Y). }
claim L2: 0 :e Inj0 X.
{ rewrite H1. exact L1. }
apply (Inj0E X 0 L2).
let x.
assume H2: x :e X /\ 0 = Inj1 x.
exact (Inj1NE1 x (eq_sym set 0 (Inj1 x) (andER (x :e X) (0 = Inj1 x) H2))).
Qed.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.

(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

Theorem Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
let X Y x.
assume H: x :e X.
prove Inj0 x :e {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
apply binunionI1.
prove Inj0 x :e {Inj0 x|x :e X}.
apply ReplI.
exact H.
Qed.

Theorem Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
let X Y y.
assume H: y :e Y.
prove Inj1 y :e {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
apply binunionI2.
prove Inj1 y :e {Inj1 y|y :e Y}.
apply ReplI.
exact H.
Qed.

Theorem setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).
let X Y z.
assume H1 : z :e {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
apply (binunionE {Inj0 x|x :e X} {Inj1 y|y :e Y} z H1).
- assume H2: z :e {Inj0 x|x :e X}.
  apply orIL.
  exact (ReplE X Inj0 z H2).
- assume H2: z :e {Inj1 y|y :e Y}.
  apply orIR.
  exact (ReplE Y Inj1 z H2).
Qed.

Theorem Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
let X. apply set_ext.
- let z.
  assume H1: z :e 0 :+: X.
  prove z :e Inj0 X.
  apply (setsum_Inj_inv 0 X z H1).
  + assume H2: exists x :e 0, z = Inj0 x.
    apply (exandE set (fun x => x :e 0) (fun x => z = Inj0 x) H2).
    let x.
    assume H3: x :e 0.
    prove False.
    exact (EmptyE x H3).
  + assume H2: exists x :e X, z = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) H2).
    let x.
    assume H3: x :e X.
    assume H4: z = Inj1 x.
    rewrite H4.
    prove Inj1 x :e Inj0 X.
    exact (Inj0I X x H3).
- let z.
  assume H1: z :e Inj0 X.
  prove z :e 0 :+: X.
  apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) (Inj0E X z H1)).
  let x.
  assume H2: x :e X.
  assume H3: z = Inj1 x.
  rewrite H3.
  prove Inj1 x :e 0 :+: X.
  apply Inj1_setsum.
  exact H2.
Qed.

Theorem Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
let X. apply set_ext.
- let z.
  assume H1: z :e 1 :+: X.
  prove z :e Inj1 X.
  apply (setsum_Inj_inv 1 X z H1).
  + assume H2: exists x :e 1, z = Inj0 x.
    apply (exandE set (fun x => x :e 1) (fun x => z = Inj0 x) H2).
    let x.
    assume H3: x :e 1.
    assume H4: z = Inj0 x.
    rewrite H4.
    prove Inj0 x :e Inj1 X.
    claim L1: x = 0.
    { exact (SingE 0 x (Subq_1_Sing0 x H3)). }
    rewrite L1.
    prove Inj0 0 :e Inj1 X.
    rewrite Inj0_0.
    prove 0 :e Inj1 X.
    exact (Inj1I1 X).
  + assume H2: exists x :e X, z = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) H2).
    let x.
    assume H3: x :e X.
    assume H4: z = Inj1 x.
    rewrite H4.
    prove Inj1 x :e Inj1 X.
    exact (Inj1I2 X x H3).
- let z.
  assume H1: z :e Inj1 X.
  prove z :e 1 :+: X.
  apply (Inj1E X z H1).
  + assume H2: z = 0.
    rewrite H2.
    prove 0 :e 1 :+: X.
    rewrite <- Inj0_0 at 1. (*** This is a little tricky. Recall that 1 is notation for ordsucc 0, so without "at 1" this hidden 0 would also be rewritten. ***)
    prove Inj0 0 :e 1 :+: X.
    apply Inj0_setsum.
    prove 0 :e 1.
    exact In_0_1.
  + assume H2: exists x :e X, z = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) H2).
    let x.
    assume H2: x :e X.
    assume H3: z = Inj1 x.
    rewrite H3.
    prove Inj1 x :e 1 :+: X.
    apply Inj1_setsum.
    exact H2.
Qed.

Theorem nat_setsum1_ordsucc : forall n:set, nat_p n -> 1 :+: n = ordsucc n.
claim L: forall n:set, nat_p n -> Inj1 n = ordsucc n.
{
  apply nat_complete_ind.
  let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, Inj1 m = ordsucc m.
  prove Inj1 n = ordsucc n.
  apply set_ext.
  - prove Inj1 n c= ordsucc n.
    let z.
    assume H1: z :e Inj1 n.
    prove z :e ordsucc n.
    apply (Inj1E n z H1).
    + assume H2: z = 0.
      rewrite H2.
      prove 0 :e ordsucc n.
      exact (nat_0_in_ordsucc n Hn).
    + assume H2: exists m :e n, z = Inj1 m.
      apply (exandE set (fun m => m :e n) (fun m => z = Inj1 m) H2).
      let m.
      assume H3: m :e n.
      assume H4: z = Inj1 m.
      rewrite H4.
      prove Inj1 m :e ordsucc n.
      rewrite (IHn m H3).
      prove ordsucc m :e ordsucc n.
      exact (nat_ordsucc_in_ordsucc n Hn m H3).
  - prove ordsucc n c= Inj1 n.
    let m.
    assume H1: m :e ordsucc n.
    prove m :e Inj1 n.
    apply (ordsuccE n m H1).
    + assume H2: m :e n.
      apply (nat_inv m (nat_p_trans n Hn m H2)).
      * assume H3: m = 0.
        rewrite H3.
        prove 0 :e Inj1 n.
        exact (Inj1I1 n).
      * assume H3: exists k, nat_p k /\ m = ordsucc k.
        apply (exandE set nat_p (fun k => m = ordsucc k) H3).
        let k.
        assume H4: nat_p k.
        assume H5: m = ordsucc k.
        rewrite H5.
        prove ordsucc k :e Inj1 n.
        claim L1: k :e m.
        {
          rewrite H5.
  	  exact (ordsuccI2 k).
        }
        claim L2: k :e n.
        { exact (nat_trans n Hn m H2 k L1). }
        rewrite <- (IHn k L2).
        prove Inj1 k :e Inj1 n.
        exact (Inj1I2 n k L2).
    + assume H2: m = n.
      rewrite H2.
      prove n :e Inj1 n.
      apply (nat_inv n Hn).
      * assume H3: n = 0.
        rewrite H3 at 1.
        prove 0 :e Inj1 n.
        exact (Inj1I1 n).
      * assume H3: exists k, nat_p k /\ n = ordsucc k.
        apply (exandE set nat_p (fun k => n = ordsucc k) H3).
        let k.
        assume H4: nat_p k.
        assume H5: n = ordsucc k.
        rewrite H5 at 1.
        prove ordsucc k :e Inj1 n.
        claim L1: k :e n.
        {
          rewrite H5.
	  exact (ordsuccI2 k).
        }
        rewrite <- (IHn k L1).
        prove Inj1 k :e Inj1 n.
        exact (Inj1I2 n k L1).
}
let n.
assume Hn: nat_p n.
prove 1 :+: n = ordsucc n.
rewrite Inj1_setsum_1L.
prove Inj1 n = ordsucc n.
exact (L n Hn).
Qed.

Theorem setsum_0_0 : 0 :+: 0 = 0.
rewrite (Inj0_setsum_0L 0).
prove Inj0 0 = 0.
exact Inj0_0.
Qed.

Theorem setsum_1_0_1 : 1 :+: 0 = 1.
exact (nat_setsum1_ordsucc 0 nat_0).
Qed.

Theorem setsum_1_1_2 : 1 :+: 1 = 2.
exact (nat_setsum1_ordsucc 1 nat_1).
Qed.

Theorem setsum_mon : forall X Y W Z, X c= W -> Y c= Z -> X :+: Y c= W :+: Z.
let X Y W Z.
assume H1: X c= W.
assume H2: Y c= Z.
let u.
assume H3: u :e X :+: Y.
prove u :e W :+: Z.
apply (setsum_Inj_inv X Y u H3).
- assume H4: exists x :e X, u = Inj0 x.
  apply (exandE set (fun x => x :e X) (fun x => u = Inj0 x) H4).
  let x.
  assume H5: x :e X.
  assume H6: u = Inj0 x.
  rewrite H6.
  prove Inj0 x :e W :+: Z.
  apply Inj0_setsum.
  exact (H1 x H5).
- assume H4: exists y :e Y, u = Inj1 y.
  apply (exandE set (fun y => y :e Y) (fun y => u = Inj1 y) H4).
  let y.
  assume H5: y :e Y.
  assume H6: u = Inj1 y.
  rewrite H6.
  prove Inj1 y :e W :+: Z.
  apply Inj1_setsum.
  exact (H2 y H5).
Qed.
