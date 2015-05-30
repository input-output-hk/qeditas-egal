(***
 This is a port of parts of the Coq file GoedelGod.v.
 The Coq file was written by Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller.
 The port was by Chad E. Brown.
 ***)

(** Preamble **)
(***
 This is a preamble file for Goedel's proof of the existence of God.
 Significant parts of the file are ported from the Coq file Modal.v.
 The Coq file was written by Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller.
 The port was by Chad E. Brown.
 ***)

Definition False : prop := forall P : prop , P.
(* Unicode False "22A5" *)

Definition True : prop := forall P : prop , P -> P.
(* Unicode True "22A4" *)
Axiom TrueI : True.

Definition not : prop -> prop := fun A : prop => A -> False.
Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
Infix /\ 780 left  := and.
Axiom andI : forall A B : prop , A -> B -> A /\ B.
Axiom andEL : forall A B : prop , A /\ B -> A.
Axiom andER : forall A B : prop , A /\ B -> B.

Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
Infix \/ 785 left  := or.
Axiom orIL : forall A B : prop , A -> A \/ B.
Axiom orIR : forall A B : prop , B -> A \/ B.
Axiom orE : forall A B C : prop , (A -> C) -> (B -> C) -> A \/ B -> C.

Definition iff : prop -> prop -> prop := fun A B : prop => (A -> B) /\ (B -> A).
Infix <-> 795 := iff.

Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
Definition neq : A -> A -> prop := fun x y => ~ eq x y.
End Poly1_eq.
Infix = 502 := eq.
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

Axiom classic : forall P : prop , P \/ ~ P.
Axiom NNPP : forall p : prop , ~ ~ p -> p.

Section RelnPoly1.
Variable A:SType.
Definition symmetric : (A->A->prop)->prop := fun R => forall x y:A, R x y -> R y x.
Definition transitive : (A->A->prop)->prop := fun R => forall x y z:A, R x y -> R y z -> R x z.
Definition per : (A->A->prop)->prop := fun R => symmetric R /\ transitive R.
Axiom per_sym : forall R : A -> A -> prop , per R -> symmetric R.
Axiom per_tra : forall R : A -> A -> prop , per R -> transitive R.
Axiom per_stra1 : forall R : A -> A -> prop , per R -> forall x y z : A , R y x -> R y z -> R x z.
Axiom per_stra2 : forall R : A -> A -> prop , per R -> forall x y z : A , R x y -> R z y -> R x z.
Axiom per_stra3 : forall R : A -> A -> prop , per R -> forall x y z : A , R y x -> R z y -> R x z.
Axiom per_ref1 : forall R : A -> A -> prop , per R -> forall x y : A , R x y -> R x x.
Axiom per_ref2 : forall R : A -> A -> prop , per R -> forall x y : A , R x y -> R y y.
End RelnPoly1.

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

Axiom mp_dia : Valid_ R (mforall p q:set->prop, dia_ R p :->: box_ R (p :->: q) :->: dia_ R q).
Axiom not_dia_box_not : Valid_ R (mforall p:set->prop, :~: dia_ R p :->: box_ R (:~: p)).
Axiom K: Valid_ R (mforall p q:set->prop, box_ R (p :->: q) :->: box_ R p :->: box_ R q).
Axiom T: Valid_ R (mforall p:set->prop, box_ R p :->: p).

Hypothesis Rper : per set R.

Axiom dia_box_to_box : Valid_ R (mforall p:set->prop, dia_ R (box_ R p) :->: box_ R p).

End ModalThms.

(** Main Body **)

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
