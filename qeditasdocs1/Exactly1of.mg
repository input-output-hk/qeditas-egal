(* Title "Exactly 1 of 2 or 3" *)
(* Author "Chad E. Brown" *)

(* Salt "2JCgFSwTWUd4YsNAm" *)

Require "7D7B5AED82DCF99283FF6C71430B459ABC2A21E4". (** for Qeditas **)

Definition exactly1of2 : prop->prop->prop := fun A B:prop =>
A /\ ~B \/ ~A /\ B.

Theorem exactly1of2_I1 : forall A B:prop, A -> ~B -> exactly1of2 A B.
let A B.
assume HA: A.
assume HB: ~B.
prove A /\ ~B \/ ~A /\ B.
apply orIL.
prove A /\ ~B.
exact (andI A (~B) HA HB).
Qed.

Theorem exactly1of2_I2 : forall A B:prop, ~A -> B -> exactly1of2 A B.
let A B.
assume HA: ~A.
assume HB: B.
prove A /\ ~B \/ ~A /\ B.
apply orIR.
prove ~A /\ B.
exact (andI (~A) B HA HB).
Qed.

Theorem exactly1of2_impI1 : forall A B:prop, (A -> ~B) -> (~A -> B) -> exactly1of2 A B.
let A B.
assume H1: A -> ~B.
assume H2: ~A -> B.
apply (classic A).
- assume H3: A. exact (exactly1of2_I1 A B H3 (H1 H3)).
- assume H3: ~A. exact (exactly1of2_I2 A B H3 (H2 H3)).
Qed.

Theorem exactly1of2_impI2 : forall A B:prop, (B -> ~A) -> (~B -> A) -> exactly1of2 A B.
let A B.
assume H1: B -> ~A.
assume H2: ~B -> A.
apply (classic B).
- assume H3: B. exact (exactly1of2_I2 A B (H1 H3) H3).
- assume H3: ~B. exact (exactly1of2_I1 A B (H2 H3) H3).
Qed.

Theorem exactly1of2_E : forall A B:prop, exactly1of2 A B ->
forall p:prop,
(A -> ~B -> p) ->
(~A -> B -> p) ->
p.
let A B.
assume H1: exactly1of2 A B.
let p.
assume H2 : A -> ~B -> p.
assume H3 : ~A -> B -> p.
apply (H1 p).
- exact (fun H4 : A /\ ~B => H4 p H2).
- exact (fun H4 : ~A /\ B => H4 p H3).
Qed.

Theorem exactly1of2_or : forall A B:prop, exactly1of2 A B -> A \/ B.
let A B.
assume H1: exactly1of2 A B.
apply (exactly1of2_E A B H1 (A \/ B)).
- exact (fun (HA : A) (_ : ~B) => orIL A B HA).
- exact (fun (_ : ~A) (HB : B) => orIR A B HB).
Qed.

Theorem exactly1of2_impn12 : forall A B:prop, exactly1of2 A B -> A -> ~B.
let A B.
assume H1: exactly1of2 A B.
apply (exactly1of2_E A B H1 (A -> ~B)).
- exact (fun (_ : A) (HB : ~B) (_ : A) => HB).
- exact (fun (HA' : ~A) (_ : B) (HA : A) => HA' HA (~B)).
Qed.

Theorem exactly1of2_impn21 : forall A B:prop, exactly1of2 A B -> B -> ~A.
let A B.
assume H1: exactly1of2 A B.
apply (exactly1of2_E A B H1 (B -> ~A)).
- exact (fun (_ : A) (HB' : ~B) (HB : B) => HB' HB (~A)).
- exact (fun (HA : ~A) (_ _ : B) => HA).
Qed.

Theorem exactly1of2_nimp12 : forall A B:prop, exactly1of2 A B -> ~A -> B.
let A B.
assume H1: exactly1of2 A B.
apply (exactly1of2_E A B H1 (~A -> B)).
- exact (fun (HA : A) (_ : ~B) (HA' : ~A) => HA' HA B).
- exact (fun (_ : ~A) (HB : B) (_ : ~A) => HB).
Qed.

Theorem exactly1of2_nimp21 : forall A B:prop, exactly1of2 A B -> ~B -> A.
let A B.
assume H1: exactly1of2 A B.
apply (exactly1of2_E A B H1 (~B -> A)).
- exact (fun (HA : A) (_ _ : ~B) => HA).
- exact (fun (_ : ~A) (HB : B) (HB' : ~B) => HB' HB A).
Qed.

Definition exactly1of3 : prop->prop->prop->prop := fun A B C:prop =>
exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.

Theorem exactly1of3_I1 : forall A B C:prop, A -> ~B -> ~C -> exactly1of3 A B C.
let A B C.
assume HA: A.
assume HB: ~B.
assume HC: ~C.
prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
apply orIL.
prove exactly1of2 A B /\ ~C.
exact (andI (exactly1of2 A B) (~C) (exactly1of2_I1 A B HA HB) HC).
Qed.

Theorem exactly1of3_I2 : forall A B C:prop, ~A -> B -> ~C -> exactly1of3 A B C.
let A B C.
assume HA: ~A.
assume HB: B.
assume HC: ~C.
prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
apply orIL.
prove exactly1of2 A B /\ ~C.
exact (andI (exactly1of2 A B) (~C) (exactly1of2_I2 A B HA HB) HC).
Qed.

Theorem exactly1of3_I3 : forall A B C:prop, ~A -> ~B -> C -> exactly1of3 A B C.
let A B C.
assume HA: ~A.
assume HB: ~B.
assume HC: C.
prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
apply orIR.
prove ~A /\ ~B /\ C.
exact (and3I (~A) (~B) C HA HB HC).
Qed.

Theorem exactly1of3_impI1 : forall A B C:prop, (A -> ~B) -> (A -> ~C) -> (B -> ~C) -> (~A -> B \/ C) -> exactly1of3 A B C.
let A B C.
assume H1: A -> ~B.
assume H2: A -> ~C.
assume H3: B -> ~C.
assume H4: ~A -> B \/ C.
prove exactly1of3 A B C.
apply (classic C).
- assume H5: C.
  prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
  apply orIR.
  apply and3I.
  + exact (fun H6 => H2 H6 H5).
  + exact (fun H6 => H3 H6 H5).
  + exact H5.
- assume H5: ~C.
  prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
  apply orIL.
  apply andI.
  + apply exactly1of2_impI1.
    * exact H1.
    * exact (fun H6 => H4 H6 B (fun H => H) (fun H => H5 H B)).
  + exact H5.
Qed.

Theorem exactly1of3_impI2 : forall A B C:prop, (B -> ~A) -> (B -> ~C) -> (A -> ~C) -> (~B -> A \/ C) -> exactly1of3 A B C.
let A B C.
assume H1: B -> ~A.
assume H2: B -> ~C.
assume H3: A -> ~C.
assume H4: ~B -> A \/ C.
prove exactly1of3 A B C.
apply (classic C).
- assume H5: C.
  prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
  apply orIR.
  apply and3I.
  + exact (fun H6 => H3 H6 H5).
  + exact (fun H6 => H2 H6 H5).
  + exact H5.
- assume H5: ~C.
  prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
  apply orIL.
  apply andI.
  + apply exactly1of2_impI2.
    * exact H1.
    * exact (fun H6 => H4 H6 A (fun H => H) (fun H => H5 H A)).
  + exact H5.
Qed.

Theorem exactly1of3_impI3 : forall A B C:prop, (C -> ~A) -> (C -> ~B) -> (A -> ~B) -> (~A -> B) -> exactly1of3 A B C.
let A B C.
assume H1: C -> ~A.
assume H2: C -> ~B.
assume H3: A -> ~B.
assume H4: ~A -> B.
prove exactly1of3 A B C.
apply (classic C).
- assume H5: C.
  prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
  apply orIR.
  apply and3I.
  + exact (fun H6 => H1 H5 H6).
  + exact (fun H6 => H2 H5 H6).
  + exact H5.
- assume H5: ~C.
  prove exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.
  apply orIL.
  apply andI.
  + apply exactly1of2_impI1.
    * exact H3.
    * exact H4.
  + exact H5.
Qed.

Theorem exactly1of3_E : forall A B C:prop, exactly1of3 A B C ->
forall p:prop,
(A -> ~B -> ~C -> p) ->
(~A -> B -> ~C -> p) ->
(~A -> ~B -> C -> p) ->
p.
let A B C.
assume H1: exactly1of3 A B C.
let p.
assume H2 : A -> ~B -> ~C -> p.
assume H3 : ~A -> B -> ~C -> p.
assume H4 : ~A -> ~B -> C -> p.
apply (H1 p).
- assume H5: exactly1of2 A B /\ ~C.
  apply (H5 p).
  assume H6: exactly1of2 A B.
  assume H7: ~C.
  apply (exactly1of2_E A B H6 p).
  + assume H8: A.
    assume H9: ~B.
    exact (H2 H8 H9 H7).
  + assume H8: ~A.
    assume H9: B.
    exact (H3 H8 H9 H7).
- assume H5 : ~A /\ ~B /\ C.
  prove p.
  apply (and3E (~A) (~B) C H5).
  prove ~A -> ~B -> C -> p.
  exact H4.
Qed.

Theorem exactly1of3_or : forall A B C:prop, exactly1of3 A B C -> A \/ B \/ C.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (A \/ B \/ C)).
- exact (fun (HA : A) (_ : ~B) (_ : ~C) => or3I1 A B C HA).
- exact (fun (_ : ~A) (HB : B) (_ : ~C) => or3I2 A B C HB).
- exact (fun (_ : ~A) (_ : ~B) (HC : C) => or3I3 A B C HC).
Qed.

Theorem exactly1of3_impn12 : forall A B C:prop, exactly1of3 A B C -> A -> ~B.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (A -> ~B)).
- exact (fun (_ : A) (HB : ~B) (_ : ~C) (_ : A) => HB).
- exact (fun (HA' : ~A) (_ : B) (_ : ~C) (HA : A) => HA' HA (~B)).
- exact (fun (HA' : ~A) (_ : ~B) (_ : C) (HA : A) => HA' HA (~B)).
Qed.

Theorem exactly1of3_impn13 : forall A B C:prop, exactly1of3 A B C -> A -> ~C.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (A -> ~C)).
- exact (fun (_ : A) (_ : ~B) (HC : ~C) (_ : A) => HC).
- exact (fun (HA' : ~A) (_ : B) (_ : ~C) (HA : A) => HA' HA (~C)).
- exact (fun (HA' : ~A) (_ : ~B) (_ : C) (HA : A) => HA' HA (~C)).
Qed.

Theorem exactly1of3_impn21 : forall A B C:prop, exactly1of3 A B C -> B -> ~A.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (B -> ~A)).
- exact (fun (_ : A) (HB' : ~B) (_ : ~C) (HB : B) => HB' HB (~A)).
- exact (fun (HA : ~A) (_ : B) (_ : ~C) (_ : B) => HA).
- exact (fun (_ : ~A) (HB' : ~B) (_ : C) (HB : B) => HB' HB (~A)).
Qed.

Theorem exactly1of3_impn23 : forall A B C:prop, exactly1of3 A B C -> B -> ~C.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (B -> ~C)).
- exact (fun (_ : A) (HB' : ~B) (_ : ~C) (HB : B) => HB' HB (~C)).
- exact (fun (_ : ~A) (_ : B) (HC : ~C) (_ : B) => HC).
- exact (fun (_ : ~A) (HB' : ~B) (_ : C) (HB : B) => HB' HB (~C)).
Qed.

Theorem exactly1of3_impn31 : forall A B C:prop, exactly1of3 A B C -> C -> ~A.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (C -> ~A)).
- exact (fun (_ : A) (_ : ~B) (HC' : ~C) (HC : C) => HC' HC (~A)).
- exact (fun (_ : ~A) (_ : B) (HC' : ~C) (HC : C) => HC' HC (~A)).
- exact (fun (HA : ~A) (_ : ~B) (_ _ : C) => HA).
Qed.

Theorem exactly1of3_impn32 : forall A B C:prop, exactly1of3 A B C -> C -> ~B.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (C -> ~B)).
- exact (fun (_ : A) (_ : ~B) (HC' : ~C) (HC : C) => HC' HC (~B)).
- exact (fun (_ : ~A) (_ : B) (HC' : ~C) (HC : C) => HC' HC (~B)).
- exact (fun (_ : ~A) (HB : ~B) (_ _ : C) => HB).
Qed.

Theorem exactly1of3_nimp1 : forall A B C:prop, exactly1of3 A B C -> ~A -> B \/ C.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (~A -> B \/ C)).
- exact (fun (HA : A) (_ : ~B) (_ : ~C) (HA' : ~A) => HA' HA (B \/ C)).
- exact (fun (_ : ~A) (HB : B) (_ : ~C) (_ : ~A) => orIL B C HB).
- exact (fun (_ : ~A) (_ : ~B) (HC : C) (_ : ~A) => orIR B C HC).
Qed.

Theorem exactly1of3_nimp2 : forall A B C:prop, exactly1of3 A B C -> ~B -> A \/ C.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (~B -> A \/ C)).
- exact (fun (HA : A) (_ : ~B) (_ : ~C) (_ : ~B) => orIL A C HA).
- exact (fun (_ : ~A) (HB : B) (_ : ~C) (HB' : ~B) => HB' HB (A \/ C)).
- exact (fun (_ : ~A) (_ : ~B) (HC : C) (_ : ~B) => orIR A C HC).
Qed.

Theorem exactly1of3_nimp3 : forall A B C:prop, exactly1of3 A B C -> ~C -> A \/ B.
let A B C.
assume H1 : exactly1of3 A B C.
apply (exactly1of3_E A B C H1 (~C -> A \/ B)).
- exact (fun (HA : A) (_ : ~B) (_ _ : ~C) => orIL A B HA).
- exact (fun (_ : ~A) (HB : B) (_ _ : ~C) => orIR A B HB).
- exact (fun (_ : ~A) (_ : ~B) (HC : C) (HC' : ~C) => HC' HC (A \/ B)).
Qed.
