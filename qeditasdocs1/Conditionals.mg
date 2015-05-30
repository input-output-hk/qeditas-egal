(* Title "Conditionals" *)
(* Author "Chad E. Brown" *)

(* Salt "2pYk6Gx8qDthfS2n2" *)

Require "32E351B48813DC92366909C91BB7FF3F4FFBF5BC". (** for Qeditas **)

Section IfA.

Variable A:SType.

Definition If : prop->A->A->A := (fun p x y => some z:A, p /\ z = x \/ ~p /\ z = y).

Notation IfThenElse If.

Lemma If_correct : forall p:prop, forall x y:A,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.
let p x y.
apply (classic p).
- assume H1: p.
  claim L1: p /\ x = x \/ ~p /\ x = y.
  {
    apply orIL. apply andI.
    - exact H1.
    - exact (eqI A x).
  }
  exact (EpsR A (fun z : A => p /\ z = x \/ ~ p /\ z = y) x L1).
- assume H1: ~p.
  claim L1: p /\ y = x \/ ~p /\ y = y.
  {
    apply orIR. apply andI.
    - exact H1.
    - exact (eqI A y).
  }
  exact (EpsR A (fun z : A => p /\ z = x \/ ~ p /\ z = y) y L1).
Qed.

Theorem If_0 : forall p:prop, forall x y:A,
~ p -> (if p then x else y) = y.
let p x y.
assume H1: ~p.
apply (If_correct p x y).
- assume H2: p /\ (if p then x else y) = x.
  exact (H1 (andEL p ((if p then x else y) = x) H2) ((if p then x else y) = y)).
- assume H2: ~p /\ (if p then x else y) = y.
  exact (andER (~p) ((if p then x else y) = y) H2).
Qed.

Theorem If_1 : forall p:prop, forall x y:A,
p -> (if p then x else y) = x.
let p x y.
assume H1: p.
apply (If_correct p x y).
- assume H2: p /\ (if p then x else y) = x.
  exact (andER p ((if p then x else y) = x) H2).
- assume H2: ~p /\ (if p then x else y) = y.
  exact (andEL (~p) ((if p then x else y) = y) H2 H1 ((if p then x else y) = x)).
Qed.

Theorem If_or : forall p:prop, forall x y:A, (if p then x else y) = x \/ (if p then x else y) = y.
let p x y.
apply (classic p).
- assume H1: p. apply orIL. exact (If_1 p x y H1).
- assume H1: ~p. apply orIR. exact (If_0 p x y H1).
Qed.

Example If_eta : forall p:prop, forall x:A, (if p then x else x) = x.
let p x.
apply (classic p).
- assume H1: p. exact (If_1 p x x H1).
- assume H1: ~p. exact (If_0 p x x H1).
Qed.

End IfA.

Example If_True : forall p:prop, if p then p else ~p.
let p.
apply (classic p).
- assume H1: p. rewrite (If_1 prop p p (~p) H1). exact H1.
- assume H1: ~p. rewrite (If_0 prop p p (~p) H1). exact H1.
Qed.

Example If_False : forall p:prop, ~if p then ~p else p.
let p.
apply (classic p).
- assume H1: p. rewrite (If_1 prop p (~p) p H1). exact (dnegI p H1).
- assume H1: ~p. rewrite (If_0 prop p (~p) p H1). exact H1.
Qed.

Example If_not_eq : forall p:prop, (~p) = if p then False else True.
let p. apply prop_ext2.
- assume H1: ~ p.
  prove if p then False else True.
  rewrite (If_0 prop p False True H1).
  prove True.
  exact TrueI.
- assume H1: if p then False else True.
  assume H2: p.
  claim L1: ~if p then False else True.
  { rewrite (If_1 prop p False True H2). exact (fun H => H). }
  exact (L1 H1).
Qed.

Example If_imp_eq : forall p q:prop, (p -> q) = if p then q else True.
let p q.
apply (classic p).
- assume H1: p.
  rewrite (If_1 prop p q True H1).
  prove (p -> q) = q.
  apply prop_ext2.
  + assume H2: p -> q.
    exact (H2 H1).
  + assume H2: q.
    exact (fun _ => H2).
- assume H1: ~p.
  rewrite (If_0 prop p q True H1).
  prove (p -> q) = True.
  apply prop_ext2.
  + assume _. exact TrueI.
  + assume _. assume H2: p. exact (H1 H2 q).
Qed.

Example If_and_eq : forall p q:prop, (p /\ q) = if p then q else False.
let p q.
apply (classic p).
- assume H1: p.
  rewrite (If_1 prop p q False H1).
  prove (p /\ q) = q.
  apply prop_ext2.
  + assume H2: p /\ q. exact (andER p q H2).
  + assume H2: q. exact (andI p q H1 H2).
- assume H1: ~p.
  rewrite (If_0 prop p q False H1).
  prove (p /\ q) = False.
  apply prop_ext2.
  + assume H2: p /\ q. exact (H1 (andEL p q H2)).
  + assume H2: False. exact (H2 (p /\ q)).
Qed.

Example If_or_eq : forall p q:prop, (p \/ q) = if p then True else q.
let p q.
apply (classic p).
- assume H1: p.
  rewrite (If_1 prop p True q H1).
  prove (p \/ q) = True.
  apply prop_ext2.
  + assume _. exact TrueI.
  + assume _. prove p \/ q. apply orIL. exact H1.
- assume H1: ~p.
  rewrite (If_0 prop p True q H1).
  prove (p \/ q) = q.
  apply prop_ext2.
  + assume H2: p \/ q.
    prove q.
    apply H2.
    * assume H3: p. exact (H1 H3 q).
    * assume H3: q. exact H3.
  + assume H2: q.
    prove p \/ q.
    apply orIR.
    exact H2.
Qed.
