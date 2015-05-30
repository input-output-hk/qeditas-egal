(* Title "Introduction to the Zermelo-Fraenkel Set Operators II" *)
(* Author "Chad E. Brown" *)

(* Salt "WwQk4WMPwu2ssNdv" *)

(** Given two sets y and z, (UPair y z) is {y,z}. **)

Definition UPair : set->set->set :=
fun y z => {if Empty :e X then y else z | X :e Power (Power Empty)}.

Notation SetEnum2 UPair.

(* Treasure "1LsZFq6KAEetFJLPH46ttFGxsHwcBvyktx" *)
Theorem UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.
let x y z.
assume H1: x :e {y,z}.
apply (ReplE (Power (Power Empty)) (fun X => if Empty :e X then y else z) x H1).
let X.
assume H2: X :e Power (Power Empty) /\ x = if Empty :e X then y else z.
claim L1: x = if Empty :e X then y else z.
{ exact (andER (X :e Power (Power Empty)) (x = if Empty :e X then y else z) H2). }
apply (If_or set (Empty :e X) y z).
- assume H3: (if Empty :e X then y else z) = y.
  apply orIL.
  prove x = y.
  rewrite <- H3. exact L1.
- assume H3: (if Empty :e X then y else z) = z.
  apply orIR.
  prove x = z.
  rewrite <- H3. exact L1.
Qed.

(* Treasure "17xapMwRp5RbbsGKh44hq1BBuMP7eMAAMQ" *)
Theorem UPairI1 : forall y z:set, y :e {y,z}.
let y z.
prove y :e {y,z}.
rewrite <- (If_1 set (Empty :e Power Empty) y z (Empty_In_Power Empty)) at 1.
prove (if Empty :e Power Empty then y else z) :e {y,z}.
prove (if Empty :e Power Empty then y else z) :e {if Empty :e X then y else z | X :e Power (Power Empty)}.
apply (ReplI (Power (Power Empty)) (fun X : set => if (Empty :e X) then y else z) (Power Empty)).
prove Power Empty :e Power (Power Empty).
exact (Self_In_Power (Power Empty)).
Qed.

(* Treasure "1MxAH2go6xbySB1u5dRZTYLDD81UMXn15a" *)
Theorem UPairI2 : forall y z:set, z :e {y,z}.
let y z.
prove z :e {y,z}.
rewrite <- (If_0 set (Empty :e Empty) y z (EmptyE Empty)) at 1.
prove (if Empty :e Empty then y else z) :e {y,z}.
prove (if Empty :e Empty then y else z) :e {if Empty :e X then y else z | X :e Power (Power Empty)}.
apply (ReplI (Power (Power Empty)) (fun X : set => if (Empty :e X) then y else z) Empty).
prove Empty :e Power (Power Empty).
exact (Empty_In_Power (Power Empty)).
Qed.

(* Treasure "1N3JVqEbi5u5nUcaFrjxJJLUpT6mTHZQ36" *)
Lemma UPair_com_Subq : forall x y:set, {x,y} c= {y,x}.
let x y z.
assume H1: z :e {x,y}.
prove z :e {y,x}.
apply (UPairE z x y H1 (z :e {y,x})).
- assume H2: z = x.
  rewrite H2.
  prove x :e {y,x}.
  exact (UPairI2 y x).
- assume H2: z = y.
  rewrite H2.
  prove y :e {y,x}.
  exact (UPairI1 y x).
Qed.

(* Treasure "12H3nffLmfBmaETk7yoMuNHb7gbFVi7FNX" *)
Theorem UPair_com : forall x y:set, {x,y} = {y,x}.
exact (fun x y : set => set_ext (UPair x y) (UPair y x) (UPair_com_Subq x y) (UPair_com_Subq y x)).
Qed.

Definition Sing : set -> set := fun x => {x,x}.
Notation SetEnum1 Sing.

(* Treasure "19cy1hw2e2PKn2ahAoPkaK2JAVsWmFutj4" *)
Theorem SingI : forall x:set, x :e {x}. 
exact (fun x : set => UPairI1 x x).
Qed.

(* Treasure "1LfBR62qGfMJCSfSaJsxUHBbGXaxaPzFWD" *)
Theorem SingE : forall x y:set, y :e {x} -> y = x. 
exact (fun x y H => UPairE y x x H (y = x) (fun H => H) (fun H => H)).
Qed.

Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.

(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

(* Treasure "1JHuPppgfdCXt3AWnZCMc4Jx958iq9zeWH" *)
Theorem binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.
let X Y z.
assume H1: z :e X.
prove z :e X :\/: Y.
prove z :e Union {X,Y}.
apply (UnionI {X,Y} z X).
- prove z :e X. exact H1.
- prove X :e {X,Y}. exact (UPairI1 X Y).
Qed.

(* Treasure "1KtkqZHR5fDvwaeRJPdDAc1RptXuf3gQiH" *)
Theorem binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.
let X Y z.
assume H1: z :e Y.
prove z :e X :\/: Y.
prove z :e Union {X,Y}.
apply (UnionI {X,Y} z Y).
- prove z :e Y. exact H1.
- prove Y :e {X,Y}. exact (UPairI2 X Y).
Qed.

(* Treasure "19RyogaDJMBv64GDTCh8R8F2PW3nu54XuY" *)
Theorem binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.
let X Y z.
assume H1: z :e X :\/: Y.
prove z :e X \/ z :e Y.
apply (UnionE2 {X,Y} z H1).
let Z.
assume H2: z :e Z.
assume H3: Z :e {X,Y}.
apply (UPairE Z X Y H3).
- assume H4: Z = X.
  apply orIL.
  prove z :e X.
  rewrite <- H4.
  prove z :e Z.
  exact H2.
- assume H4: Z = Y.
  apply orIR.
  prove z :e Y.
  rewrite <- H4.
  prove z :e Z.
  exact H2.
Qed.

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.

Notation SetEnum Empty Sing UPair SetAdjoin.

(* Treasure "1HkrrPVrjvpWJZCXgqWbx2utZqMJptNWpG" *)
Theorem Power_0_Sing_0 : Power Empty = {Empty}.
apply set_ext.
- let X.
  assume H1: X :e Power Empty.
  prove X :e {Empty}.
  claim L1: X = Empty.
  {
    apply Empty_Subq_eq.
    exact (PowerE Empty X H1).
  }
  rewrite L1.
  prove Empty :e {Empty}.
  exact (SingI Empty).
- let X.
  assume H1: X :e {Empty}.
  prove X :e Power Empty.
  rewrite (SingE Empty X H1).
  prove Empty :e Power Empty.
  exact (Empty_In_Power Empty).
Qed.

(* Treasure "1JdxV3jP8KKpcdmDeZurZnv6ZAeQLHA6C2" *)
Theorem Repl_UPair : forall F:set->set, forall x y:set, {F z|z :e {x,y}} = {F x,F y}.
let F x y. apply set_ext.
- let z. assume H1: z :e {F z|z :e {x,y}}.
  prove z :e {F x,F y}.
  apply (ReplE2 {x,y} F z H1).
  let w.
  assume H2: w :e {x,y}.
  assume H3: z = F w.
  prove z :e {F x,F y}.
  rewrite H3.
  prove F w :e {F x,F y}.
  apply (UPairE w x y H2).
  + assume H4: w = x.
    rewrite H4.
    prove F x :e {F x,F y}.
    exact (UPairI1 (F x) (F y)).
  + assume H4: w = y.
    rewrite H4.
    prove F y :e {F x,F y}.
    exact (UPairI2 (F x) (F y)).
- let z. assume H1: z :e {F x,F y}.
  prove z :e {F z|z :e {x,y}}.
  apply (UPairE z (F x) (F y) H1).
  + assume H2: z = F x.
    rewrite H2.
    prove F x :e {F z|z :e {x,y}}.
    apply ReplI.
    prove x :e {x,y}.
    exact (UPairI1 x y).
  + assume H2: z = F y.
    rewrite H2.
    prove F y :e {F z|z :e {x,y}}.
    apply ReplI.
    prove y :e {x,y}.
    exact (UPairI2 x y).
Qed.

(* Treasure "19TH87oKNCBs5ULNiWyTkrfoFAzgr5kyjH" *)
Theorem Repl_Sing : forall F:set->set, forall x:set, {F z|z :e {x}} = {F x}.
exact (fun (F : set -> set) (x : set) => Repl_UPair F x x).
Qed.

(* Treasure "1AnvsP2DroVLWUMbcbuiYDyxcVzQWcaU1R" *)
Lemma Repl_restr_1 : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} c= {G x|x :e X}.
let X F G.
assume H1: forall x : set, x :e X -> F x = G x.
let z.
assume H2: z :e {F x|x :e X}.
apply (ReplE X F z H2).
let x. assume H3: x :e X /\ z = F x. apply H3.
assume H4: x :e X.
assume H5: z = F x.
prove z :e {G x|x :e X}.
rewrite H5.
prove F x :e {G x|x :e X}.
rewrite (H1 x H4).
prove G x :e {G x|x :e X}.
apply ReplI.
exact H4.
Qed.

(* Treasure "19e4vjBh54XtUkXp6oxTK1VLGcB7N7bXf1" *)
Theorem Repl_restr : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} = {G x|x :e X}.
let X F G.
assume H1: forall x : set, x :e X -> F x = G x.
apply set_ext.
- exact (Repl_restr_1 X F G H1).
- apply (Repl_restr_1 X G F).
  let x. assume H2: x :e X. apply (eq_sym set). exact (H1 x H2).
Qed.

Definition famunion:set->(set->set)->set
:= fun X F => Union {F x|x :e X}.

(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.

(* Treasure "1GyJcord2uX9UrdXbYtnzoxXXbnGE2nH4s" *)
Theorem famunionI:forall X:set, forall F:(set->set), forall x y:set, x :e X -> y :e F x -> y :e \/_ x :e X, F x.
exact (fun X F x y H1 H2 => UnionI (Repl X F) y (F x) H2 (ReplI X F x H1)).
Qed.

(* Treasure "1NUbG5BVsbCCjmRDTYBgCo3gGVJaATvQ48" *)
Theorem famunionE:forall X:set, forall F:(set->set), forall y:set, y :e (\/_ x :e X, F x) -> exists x :e X, y :e F x.
let X F y.
assume H1: y :e (\/_ x :e X, F x).
prove exists x :e X, y :e F x.
apply (UnionE2 {F x|x :e X} y H1).
let Y.
assume H2: y :e Y.
assume H3: Y :e {F x|x :e X}.
apply (ReplE2 X F Y H3).
let x.
assume H4: x :e X.
assume H5: Y = F x.
witness x.
prove x :e X /\ y :e F x.
apply andI.
- exact H4.
- prove y :e F x.
  rewrite <- H5.
  exact H2.
Qed.

(* Treasure "1HYvXdRQcwPHVb4SwfuMkZUqvFMmrmCqdY" *)
Theorem UnionEq_famunionId:forall X:set, Union X = \/_ x :e X, x.
let X. apply set_ext.
- let y. assume H1: y :e Union X. apply (UnionE2 X y H1).
  let x.
  assume H2: y :e x.
  assume H3: x :e X.
  prove y :e \/_ x :e X, x.
  exact (famunionI X (fun x => x) x y H3 H2).
- let y. assume H1: y :e \/_ x :e X, x.
  apply (famunionE X (fun x => x) y H1).
  let x. assume H2: x :e X /\ y :e x. apply H2.
  assume H3: x :e X.
  assume H4: y :e x.
  prove y :e Union X.
  exact (UnionI X y x H4 H3).
Qed.

(* Treasure "198U8nYqdBvE8CLaYiyVNqe4ePKNtvuV5o" *)
Theorem ReplEq_famunion_Sing:forall X:set, forall F:(set->set), {F x|x :e X} = \/_ x :e X, {F x}.
let X F. apply set_ext.
- let y. assume H1: y :e {F x|x :e X}.
  prove y :e \/_ x :e X, {F x}.
  apply (ReplE2 X F y H1).
  let x.
  assume H2: x :e X.
  assume H3: y = F x.
  apply (famunionI X (fun x => {F x}) x y H2).
  prove y :e {F x}.
  rewrite <- H3. exact (SingI y).
- let y. assume H1: y :e \/_ x :e X, {F x}.
  prove y :e {F x|x :e X}.
  apply (famunionE X (fun x => {F x}) y H1).
  let x. assume H2: x :e X /\ y :e {F x}. apply H2.
  assume H3: x :e X.
  assume H4: y :e {F x}.
  claim L1: y = F x.
  { exact (SingE (F x) y H4). }
  rewrite L1.
  prove F x :e {F x|x :e X}.
  exact (ReplI X F x H3).
Qed.
