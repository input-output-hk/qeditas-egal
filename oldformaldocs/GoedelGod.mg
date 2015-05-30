(***
 This is a port of parts of the Coq file GoedelGod.v.
 The Coq file was written by Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller.
 The port was by Chad E. Brown.
 ***)

Variable R:set->set->prop.

Let box := box_ R.
Let dia := dia_ R.
Let Valid := Valid_ R.

Hypothesis Rper: per set R.

Lemma Rsym : forall w u, R w u -> R u w.
exact (per_sym set R Rper).
Qed.

Lemma Rref2 : forall w u, R w u -> R u u.
exact (per_ref2 set R Rper).
Qed.

Variable Positive : (set->set->prop) -> set->prop.

Hypothesis Axiom1a : Valid (mforall p:set->set->prop, Positive (fun x => :~: p x) :->: :~: Positive p).
Hypothesis Axiom1b : Valid (mforall p:set->set->prop, :~: Positive p :->: Positive (fun x => :~: p x)).

Hypothesis Axiom2 : Valid (mforall p q:set->set->prop, Positive p :/\: box (mforall x, p x :->: q x) :->: Positive q).

Theorem Thm1 : Valid (mforall p:set->set->prop, Positive p :->: dia (mexists x, p x)).
let w.
assume Hw: R w w.
let p.
assume H1: Positive p w.
apply NNPP.
assume H2: ~ dia (mexists x, p x) w.
claim C: Positive (fun x => :~: p x) w.
{
  apply Axiom2 w Hw p (fun x => :~: p x).
  prove Positive p w /\ box (mforall x, p x :->: :~: p x) w.
  apply andI.
  - exact H1.
  - prove box (mforall x, p x :->: :~: p x) w.
    let u.
    assume H3: R w u.
    let x.
    assume H4: p x u.
    assume _.
    apply H2.
    prove exists u, R w u /\ exists x, p x u.
    witness u.
    apply andI.
    - exact H3.
    - witness x.
      exact H4.
}
exact Axiom1a w Hw p C H1.
Qed.

Definition G : set->set->prop := fun x => mforall p:set->set->prop, Positive p :->: p x.

Hypothesis Axiom3 : Valid (Positive G).

Theorem Cor1 : Valid (dia (mexists x, G x)).
let w.
assume Hw: R w w.
apply Thm1 w Hw.
apply Axiom3 w Hw.
Qed.

Hypothesis Axiom4 : Valid (mforall p:set->set->prop, Positive p :->: box (Positive p)).

Definition Essence : (set->set->prop) -> set->set->prop := fun p x => p x :/\: mforall q:set->set->prop, q x :->: box (mforall y, p y :->: q y).
Infix ess 69 := Essence.

Theorem Thm2 : Valid (mforall x, G x :->: G ess x).
let w.
assume Hw: R w w.
let x.
assume H1: G x w.
prove G x w /\ (mforall q:set->set->prop, q x :->: box (mforall y, G y :->: q y)) w.
apply andI.
- exact H1.
- let q.
  assume H2: q x w.
  let u.
  assume H3: R w u.
  claim C: Positive q u.
  {
    apply NNPP.
    assume H4: ~ Positive q u.
    claim C2: Positive (fun x => :~: q x) u.
    { exact Axiom1b u (Rref2 w u H3) q H4. }
    claim C3: box (Positive (fun x => :~: q x)) u.
    { exact Axiom4 u (Rref2 w u H3) (fun x => :~: q x) C2. }
    claim C4: Positive (fun x => :~: q x) w.
    { exact C3 w (Rsym w u H3). }
    exact H1 (fun x => :~: q x) C4 H2.
  }
  let y.
  assume H5: G y u.
  prove q y u.
  exact H5 q C.
Qed.

Definition NE : set->set->prop := fun x => mforall p:set->set->prop, p ess x :->: box (mexists y, p y).

Hypothesis Axiom5 : Valid (Positive NE).

Lemma Lem1 : Valid ((mexists x, G x) :->: box (mexists x, G x)).
let w.
assume Hw: R w w.
assume H1: exists x, G x w.
apply H1.
let x.
assume H2: G x w.
claim C1: (G ess x) w.
{ exact Thm2 w Hw x H2. }
claim C2: NE x w.
{
  claim C3: Positive NE w.
  { exact Axiom5 w Hw. }
  exact H2 NE C3.
}
prove box (mexists x, G x) w.
exact C2 G C1.
Qed.

Theorem Thm3: Valid (box (mexists x, G x)).
let w.
assume Hw: R w w.
prove box (mexists x, G x) w.
apply dia_box_to_box R Rper w Hw (mexists x, G x).
prove dia (box (mexists x, G x)) w.
claim C1: dia (mexists x, G x) w.
{
  exact Cor1 w Hw.
}
apply exandE set (R w) (mexists x, G x) C1.
let u.
assume H1: R w u.
assume H2: (mexists x, G x) u.
prove exists u, R w u /\ box (mexists x, G x) u.
witness u.
apply andI.
- exact H1.
- prove box (mexists x, G x) u.
  exact Lem1 u (Rref2 w u H1) H2.
Qed.

Theorem Cor2 : Valid (mexists x, G x).
let w.
assume Hw: R w w.
exact Thm3 w Hw w Hw.
Qed.
