(***
 This is a port of parts of the Coq file Modal.v.
 The Coq file was written by Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller.
 The port was by Chad E. Brown.
 ***)

Definition meq : set->set->(set->prop) := fun x y w => x = y.
Infix :=: 510 := meq.

Definition mnot : (set->prop) -> (set->prop) := fun p w => ~ p w.
Prefix :~: 700 := mnot.

Definition mand : (set->prop) -> (set->prop) -> (set->prop) := fun p q w => p w /\ q w.
Infix :/\: 780 left := mand.

Definition mor : (set->prop) -> (set->prop) -> (set->prop) := fun p q w => p w \/ q w.
Infix :\/: 785 left := mor.

Definition mimplies : (set->prop) -> (set->prop) -> (set->prop) := fun p q w => p w -> q w.
Infix :->: 810 right := mimplies.

Section ModalOps.

Variable R : set -> set -> prop.

Definition box_ : (set->prop) -> set->prop := fun p w => forall u, R w u -> p u.
Definition dia_ : (set->prop) -> set->prop := fun p w => exists u, R w u /\ p u.

(***
 Instead of assuming a domain of R and that R is reflexive on that domain, we only consider worlds where R w w.
 We are interested in the case where R is a per and so R w w follows from R u w (or R w u).
 Hence we will only be considering w where R w w.
 ***)
Definition Valid_ : (set->prop) -> prop := fun p => forall w, R w w -> p w.

End ModalOps.

Section ModalQuants.
Variable A : SType.
Definition ModalAll : (A->set->prop) -> set->prop := fun p w => forall x:A, p x w.
Definition ModalEx : (A->set->prop) -> set->prop := fun p w => exists x:A, p x w.
End ModalQuants.
Binder+ mforall , := ModalAll.
Binder+ mexists , := ModalEx.

Section ModalThms.

Variable R:set->set->prop.

Theorem mp_dia : Valid_ R (mforall p q:set->prop, dia_ R p :->: box_ R (p :->: q) :->: dia_ R q).
let w.
assume Hw: R w w.
let p q.
assume H1: dia_ R p w.
assume H2: box_ R (p :->: q) w.
apply exandE set (R w) p H1.
let u.
assume H3: R w u.
assume H4: p u.
prove exists u, R w u /\ q u.
witness u.
prove R w u /\ q u.
apply andI.
- exact H3.
- exact H2 u H3 H4.
Qed.

Theorem not_dia_box_not : Valid_ R (mforall p:set->prop, :~: dia_ R p :->: box_ R (:~: p)).
let w.
assume Hw: R w w.
let p.
assume H1: ~ dia_ R p w.
let u.
assume H2: R w u.
assume H3: p u.
apply H1.
prove exists u, R w u /\ p u.
witness u.
apply andI (R w u) (p u) H2 H3.
Qed.

Theorem K: Valid_ R (mforall p q:set->prop, box_ R (p :->: q) :->: box_ R p :->: box_ R q).
let w.
assume Hw: R w w.
let p q.
assume H1: box_ R (p :->: q) w.
assume H2: box_ R p w.
let u.
assume H3: R w u.
prove q u.
apply H1 u H3.
prove p u.
exact H2 u H3.
Qed.

Theorem T: Valid_ R (mforall p:set->prop, box_ R p :->: p).
let w.
assume Hw: R w w.
let p.
assume H1: box_ R p w.
prove p w.
exact H1 w Hw.
Qed.

Hypothesis Rper : per set R.

Theorem dia_box_to_box : Valid_ R (mforall p:set->prop, dia_ R (box_ R p) :->: box_ R p).
let w.
assume Hw: R w w.
let p.
assume H1: dia_ R (box_ R p) w.
apply exandE set (R w) (box_ R p) H1.
let u.
assume H2: R w u.
assume H3: box_ R p u.
let v.
assume H4: R w v.
claim L: R u v.
{ exact per_stra1 set R Rper u w v H2 H4. }
prove p v.
exact H3 v L.
Qed.

End ModalThms.