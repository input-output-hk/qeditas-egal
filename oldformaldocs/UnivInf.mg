(* Title "Universes and Infinity" *)
(* Author "Chad E. Brown" *)

(* Salt "3GET5N85aHveg5ZgU" *)

Definition TransSet : set->prop := fun U:set => forall X:set, X :e U -> X c= U.

Definition Union_closed : set->prop := fun U:set => forall X:set, X :e U -> Union X :e U.
Definition Power_closed : set->prop := fun U:set => forall X:set, X :e U -> Power X :e U.
Definition Repl_closed : set->prop := fun U:set => forall X:set, X :e U -> forall F:set->set,
   (forall x:set, x :e X -> F x :e U) -> {F x|x :e X} :e U.
Definition ZF_closed : set->prop := fun U:set =>
   Union_closed U
/\ Power_closed U
/\ Repl_closed U.

(* Treasure "1DsJZkAjGZGjggQWve8pFsN28wVg3j5mDu" *)
Theorem ZF_closed_I : forall U,
 Union_closed U ->
 Power_closed U ->
 Repl_closed U ->
 ZF_closed U.
exact (fun U H1 H2 H3 => and3I (Union_closed U) (Power_closed U) (Repl_closed U) H1 H2 H3).
Qed.

(* Treasure "1PyQmhMNwCZNZwjX84YXABmgABM4bFvSiM" *)
Theorem ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.
exact (fun U C p v => C p (fun C H3 => C p (fun H1 H2 => v H1 H2 H3))).
Qed.

(* Treasure "12zcSHLyVnDdy3n3LLcZvzZeNY1ZXBrCfo" *)
Theorem ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.
exact (fun U C => ZF_closed_E U C (forall X :e U, Union X :e U) (fun H _ _ => H)).
Qed.

(* Treasure "1Mp9aDNdXyAskcNuQM5xpmaM2DEnWxWsG5" *)
Theorem ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.
exact (fun U C => ZF_closed_E U C (forall X :e U, Power X :e U) (fun _ H _ => H)).
Qed.

(* Treasure "18eW7WFW3SASnf18fYKpoiEiQwtQFrccwN" *)
Theorem ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.
exact (fun U C => ZF_closed_E U C (forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U) (fun _ _ H => H)).
Qed.

(* Treasure "18YRAAuJQF8idQh4s24tdgEwbVevTj6htU" *)
Theorem ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.
let U.
assume C: ZF_closed U.
let x.
assume Hx: x :e U.
let y.
assume Hy: y :e U.
prove {x,y} :e U.
claim L1: {if x :e X then x else y|X :e Power (Power x)} = {x,y}.
{
  apply set_ext.
  - prove {if x :e X then x else y|X :e Power (Power x)} c= {x,y}.
    let z.
    assume Hz: z :e {if x :e X then x else y|X :e Power (Power x)}.
    prove z :e {x,y}.
    apply (ReplE2 (Power (Power x)) (fun X => if x :e X then x else y) z Hz).
    let X. assume _.
    prove z = (if x :e X then x else y) -> z :e {x,y}.
    apply (classic (x :e X)).
    + assume H2: x :e X.
      rewrite (If_1 set (x :e X) x y H2).
      prove (z = x -> z :e {x,y}).
      assume H3: z = x.
      rewrite H3.
      exact (UPairI1 x y).
    + assume H2: x /:e X.
      rewrite (If_0 set (x :e X) x y H2).
      prove (z = y -> z :e {x,y}).
      assume H3: z = y.
      rewrite H3.
      exact (UPairI2 x y).
  - prove {x,y} c= {if x :e X then x else y|X :e Power (Power x)}.
    let z.
    assume Hz : z :e {x,y}.
    prove z :e {if x :e X then x else y|X :e Power (Power x)}.
    claim L1a: (if x :e (Power x) then x else y) :e {if x :e X then x else y|X :e Power (Power x)}.
    {
      apply (ReplI (Power (Power x)) (fun X => if x :e X then x else y) (Power x)).
      prove Power x :e Power (Power x).
      exact (Self_In_Power (Power x)).
    }
    claim L1b: (if x :e Empty then x else y) :e {if x :e X then x else y|X :e Power (Power x)}.
    {
      apply (ReplI (Power (Power x)) (fun X => if x :e X then x else y) Empty).
      prove Empty :e Power (Power x).
      exact (Empty_In_Power (Power x)).
    }
    apply (UPairE z x y Hz).
    + assume H1: z = x.
      rewrite H1.
      prove x :e {if x :e X then x else y|X :e Power (Power x)}.
      rewrite <- (If_1 set (x :e (Power x)) x y (Self_In_Power x)) at 1.
      exact L1a.
    + assume H1: z = y.
      rewrite H1.
      prove y :e {if x :e X then x else y|X :e Power (Power x)}.
      rewrite <- (If_0 set (x :e Empty) x y (EmptyE x)) at 1.
      exact L1b.
}
prove {x,y} :e U.
rewrite <- L1.
prove {if x :e X then x else y|X :e Power (Power x)} :e U.
claim L2: Power (Power x) :e U.
{
  exact (ZF_Power_closed U C (Power x) (ZF_Power_closed U C x Hx)).
}
claim L3: forall X :e Power (Power x), (if x :e X then x else y) :e U.
{
  let X. assume _.
  prove (if x :e X then x else y) :e U.
  apply (classic (x :e X)).
  - assume H1: x :e X.
    rewrite (If_1 set (x :e X) x y H1).
    prove x :e U.
    exact Hx.
  - assume H1: x /:e X.
    rewrite (If_0 set (x :e X) x y H1).
    prove y :e U.
    exact Hy.
}
exact (ZF_Repl_closed U C (Power (Power x)) L2 (fun X => if x :e X then x else y) L3).
Qed.

(* Treasure "1FGwGgAxu6ZYw7Bzd89uXDAAyuddAArDat" *)
Theorem ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.
exact (fun U C x H => ZF_UPair_closed U C x H x H).
Qed.

(* Treasure "19Cwn4VLwH6xKGjicNXrJgcnqLKpNzdgK1" *)
Theorem ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.
exact (fun U C X HX Y HY => ZF_Union_closed U C {X,Y} (ZF_UPair_closed U C X HX Y HY)). 
Qed.

(* Treasure "1Aeuo28gzUEmXogq3X1vWU3ZrF9F7AJu9j" *)
Theorem ZF_ordsucc_closed : forall U, ZF_closed U ->
  forall x :e U, ordsucc x :e U.
exact (fun U C x H => ZF_binunion_closed U C x H {x} (ZF_Sing_closed U C x H)).
Qed.

Parameter UnivOf : set->set.

Axiom UnivOf_In : forall N:set, N :e UnivOf N.

Axiom UnivOf_TransSet : forall N:set, TransSet (UnivOf N).

Axiom UnivOf_ZF_closed : forall N:set, ZF_closed (UnivOf N).

Axiom UnivOf_Min : forall N U:set, N :e U
  -> TransSet U
  -> ZF_closed U
  -> UnivOf N c= U.

Definition InfiniteSet : set->prop := fun X:set =>
exists f:set->set, (forall x :e X, f x :e X) /\ (exists z :e X, forall x :e X, f x <> z) /\ (forall x y :e X, f x = f y -> x = y).

Definition FiniteSet : set->prop := fun X:set => ~InfiniteSet X.

(* Treasure "1JUy3T5RBcd7EqyeH1bVk6AS3YZ5hMWHL2" *)
Theorem UnivOfEmptyInfinite : InfiniteSet (UnivOf Empty).
prove exists f:set->set, (forall x :e UnivOf Empty, f x :e UnivOf Empty) /\ (exists z :e UnivOf Empty, forall x :e UnivOf Empty, f x <> z) /\ (forall x y :e UnivOf Empty, f x = f y -> x = y).
witness ordsucc.
apply and3I.
- prove forall x :e UnivOf Empty, ordsucc x :e UnivOf Empty.
  let x.
  assume Hx: x :e UnivOf Empty.
  prove ordsucc x :e UnivOf Empty.
  exact (ZF_ordsucc_closed (UnivOf Empty) (UnivOf_ZF_closed Empty) x Hx).
- prove exists z :e UnivOf Empty, forall x :e UnivOf Empty, ordsucc x <> z.
  witness 0.
  prove 0 :e UnivOf Empty /\ forall x :e UnivOf Empty, ordsucc x <> 0.
  apply andI.
  + exact (UnivOf_In Empty).
  + let x. assume _.
    exact (neq_ordsucc_0 x).
- prove forall x y :e UnivOf Empty, ordsucc x = ordsucc y -> x = y.
  let x. assume _.
  let y. assume _.
  exact (ordsucc_inj x y).
Qed.

(* Treasure "1DVxAvJT2LnPiY11njJ7744cpGVkgHBKRZ" *)
Theorem nat_p_UnivOf_Empty : forall n:set, nat_p n -> n :e UnivOf Empty.
apply nat_ind.
- prove 0 :e UnivOf Empty.
  exact (UnivOf_In Empty).
- let n.
  assume Hn: nat_p n.
  assume IHn: n :e UnivOf Empty.
  prove ordsucc n :e UnivOf Empty.
  exact (ZF_ordsucc_closed (UnivOf Empty) (UnivOf_ZF_closed Empty) n IHn).
Qed.

(* Unicode omega "3c9" *)
Definition omega : set := {n :e UnivOf Empty|nat_p n}.

(* Treasure "1McazTdmkVE9tJzASWquhSyy2vWskdUS2B" *)
Theorem omega_nat_p : forall n :e omega, nat_p n.
exact (fun n H => SepE2 (UnivOf Empty) nat_p n H).
Qed.

(* Treasure "192B8XjoorT55zN5HuNfcq8SoQsnS23TqT" *)
Theorem nat_p_omega : forall n:set, nat_p n -> n :e omega.
let n.
assume H: nat_p n.
prove n :e {n :e UnivOf Empty|nat_p n}.
apply SepI.
- prove n :e UnivOf Empty. exact (nat_p_UnivOf_Empty n H).
- prove nat_p n. exact H.
Qed.

Definition ZF_Model : set->prop := fun U:set => ZF_closed U /\ TransSet U /\ omega :e U.

(* Treasure "1LAwVndmsJw3uCjTka4xwRcMhwM3Fg3Bby" *)
Theorem ZF_Model_UnivOf_omega : ZF_Model (UnivOf omega).
prove ZF_closed (UnivOf omega) /\ TransSet (UnivOf omega) /\ omega :e (UnivOf omega).
apply and3I.
- exact (UnivOf_ZF_closed omega).
- exact (UnivOf_TransSet omega).
- exact (UnivOf_In omega).
Qed.
