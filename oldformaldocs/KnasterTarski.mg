(* Title "Knaster-Tarski Fixed Points" *)
(* Author "Chad E. Brown" *)

(* Salt "rV9oQDrt79Whisxz" *)

(*** Chad E Brown ***)
(*** Aug 2010 - June 2011 - September 2011 (-nois version) - March 2013 ***)

(*** Definitions of logical constants. ***)

Section Poly1_fpdef.
Variable A:SType.

Variable F:((A->prop)->A->prop).
Hypothesis Fmon:forall p q:A->prop, p c= q -> F p c= F q.

Definition lfp : A->prop :=
fun z => forall p:A -> prop, F p c= p -> p z.

Definition gfp : A->prop :=
fun z => exists p:A -> prop, p c= F p /\ p z.

Section lfp.

Let Y := lfp.

Theorem lfp_t : 
(F Y = Y) /\ forall X:A -> prop, F X = X -> Y c= X.
claim L1 : F Y c= Y.
{
  prove forall z:A, F Y z -> forall p:A->prop, F p c= p -> p z.
  let z.
  assume H1: F Y z.
  let p.
  assume H2: F p c= p.
  apply H2.
  prove F p z.
  apply (Fmon Y p).
  - prove Y c= p. let u. assume H3: Y u. exact (H3 p H2).
  - prove F Y z. exact H1.
}
apply andI.
- prove (F Y = Y). apply (pred_ext A).
  + prove F Y c= Y. exact L1.
  + prove Y c= F Y. let z. assume H1: Y z.
    apply (H1 (F Y)).
    prove F (F Y) c= F Y.
    exact (Fmon (F Y) Y L1).
- prove forall X : A -> prop, F X = X -> Y c= X.
  let X. assume H1: F X = X. let z. assume H2: Y z.
  claim L2 : F X c= X.
  {
    rewrite H1. exact (fun z H2 => H2).
  }
  prove X z.
  exact (H2 X L2).
Qed.  

End lfp.

Section gfp.

Let Y := gfp.

(* Treasure "1DxLDe8euaxWv3umTCZMsTr3NSEcWqfMX1" *)
Theorem gfp_t :
(F Y = Y) /\ forall X:A -> prop, F X = X -> X c= Y.
claim L1 : Y c= F Y.
{
  let z. assume H1: exists p:A->prop, p c= F p /\ p z.
  prove F Y z.
  apply (exandE (A->prop) (fun p => p c= F p) (fun p => p z) H1).
  let p.
  assume H2: p c= F p.
  assume H3: p z.
  apply (Fmon p Y).
  - prove p c= Y. let u. assume H4: p u.
    prove exists q:A->prop, q c= F q /\ q u.
    witness p. exact (andI (p c= F p) (p u) H2 H4).
  - prove F p z. exact (H2 z H3).
}
apply andI.
- prove (F Y = Y). apply (pred_ext A).
  + prove F Y c= Y. let z. assume H1: F Y z.
    prove Y z.
    prove exists p:A->prop, p c= F p /\ p z.
    witness (F Y).
    prove (F Y c= F (F Y) /\ F Y z).
    apply andI.
    * exact (Fmon Y (F Y) L1).
    * exact H1.
  + prove Y c= F Y. exact L1.
- prove forall X : A -> prop, F X = X -> X c= Y.
  let X. assume H1: F X = X. let z. assume H2: X z.
  claim L2 : X c= F X.
  {
    rewrite H1. exact (fun z H2 => H2).
  }
  prove Y z.
  prove exists p:A->prop, p c= F p /\ p z.
  witness X.
  prove X c= F X /\ X z.
  apply andI.
  + exact L2.
  + exact H2.
Qed.

End gfp.

(* Treasure "19hfp2388cvQuWAmnTKbVJ5t66SY95FedW" *)
Theorem lfpe_t : exists Y:A->prop, (F Y = Y) /\ forall X:A -> prop, F X = X -> Y c= X.
witness lfp. exact lfp_t.
Qed.

(* Treasure "1KfmuxvW2AMJwWFLZiybUmdd8LCpgsrc8W" *)
Theorem gfpe_t : exists Y:A->prop, (F Y = Y) /\ forall X:A -> prop, F X = X -> X c= Y.
witness gfp. exact gfp_t.
Qed.

(* Treasure "1HpaT1SojLnMySjUWoJTuLYbWuWAJJN2g5" *)
Theorem fpe_t : exists Y:A->prop, (F Y = Y).
witness lfp. exact (andEL (F lfp = lfp) (forall X:A -> prop, F X = X -> lfp c= X) lfp_t).
Qed.

End Poly1_fpdef.

Section Poly2_fpdef.
Variable A B:SType.

Variable F : (A->B->prop) -> (A->B->prop).
Hypothesis Fmon:forall R S:A->B->prop, R c= S -> F R c= F S.

Definition lfp2 : A->B->prop :=
  fun z1 z2 => forall p:A->B->prop, F p c= p -> p z1 z2.

Definition gfp2 : A->B->prop :=
  fun z1 z2 => exists p:A->B->prop, p c= F p /\ p z1 z2.

Section lfp2.

Let Y := lfp2.

(* Treasure "18EmCRuXQQo9NRgaxoDeu9hWoNBRDXVyT8" *)
Theorem lfp2_t : 
(F Y = Y) /\ forall X:A->B->prop, F X = X -> Y c= X.
claim L1 : F Y c= Y.
{
  prove forall (z:A) (z':B), F Y z z' -> forall p:A->B->prop, F p c= p -> p z z'.
  let z z'. assume H1. let p. assume H2.
  apply H2.
  prove F p z z'.
  apply (Fmon Y p).
  - let u u'. assume H3: Y u u'. exact (H3 p H2).
  - exact H1.
}
apply andI.
- prove (F Y = Y). apply (reln_ext A B).
  + prove F Y c= Y. exact L1.
  + prove Y c= F Y. let z z'. assume H1: Y z z'. exact (H1 (F Y) (Fmon (F Y) Y L1)).
- prove forall X:A->B->prop, F X = X -> Y c= X.
  let X. assume H1: F X = X. let z z'. assume H2: Y z z'.
  claim L2 : F X c= X.
  {
    rewrite H1. exact (fun z z' H2 => H2).
  }
  prove X z z'.
  exact (H2 X L2).
Qed.

End lfp2.

Section gfp2.

Let Y := gfp2.

(* Treasure "138ap6K7ZwtJZACSsN3RRPHa6tmW2Hahm2" *)
Theorem gfp2_t : (F Y = Y) /\ forall X:A->B->prop, F X = X -> X c= Y.
claim L1 : Y c= F Y.
{
  let z z'. assume H1: exists p:A->B->prop, p c= F p /\ p z z'.
  prove F Y z z'.
  apply (exandE (A->B->prop) (fun p => p c= F p) (fun p => p z z') H1).
  let p. 
  assume H2: p c= F p.
  assume H3: p z z'.
  apply (Fmon p Y).
  - prove p c= Y. let u u'. assume H4: p u u'.
    prove exists q:A->B->prop, q c= F q /\ q u u'.
    witness p. exact (andI (p c= F p) (p u u') H2 H4).
  - prove F p z z'. exact (H2 z z' H3).
}
apply andI.
- prove (F Y = Y). apply (reln_ext A B).
  + prove F Y c= Y. let z z'. assume H1: F Y z z'.
    prove Y z z'.
    prove exists p:A->B->prop, p c= F p /\ p z z'.
    witness (F Y).
    prove (F Y c= F (F Y) /\ F Y z z').
    apply andI.
    * exact (Fmon Y (F Y) L1).
    * exact H1.
  + prove Y c= F Y. exact L1.
- prove forall X:A->B->prop, F X = X -> X c= Y.
  let X. assume H1: F X = X. let z z'. assume H2: X z z'.
  claim L2 : X c= F X.
  {
    rewrite H1. exact (fun z z' H2 => H2).
  }
  prove Y z z'.
  prove exists p:A->B->prop, p c= F p /\ p z z'.
  witness X.
  prove X c= F X /\ X z z'.
  apply andI.
  + exact L2.
  + exact H2.
Qed.

End gfp2.

(* Treasure "15BhWjtU6Wt3XEkkumRACRNesVbich3aCD" *)
Theorem lfp2e_t :
exists Y:A->B->prop, (F Y = Y) /\ forall X:A->B->prop, F X = X -> Y c= X.
witness lfp2. exact lfp2_t.
Qed.

(* Treasure "1E8XHix7shPE2UQPXu5xC1Kgoa4MRmkYA1" *)
Theorem gfp2e_t :
exists Y:A->B->prop, (F Y = Y) /\ forall X:A->B->prop, F X = X -> X c= Y.
witness gfp2. exact gfp2_t.
Qed.

(* Treasure "1CGgmdxF4AAkoEgUVYsVU2P3W6EdgEG3rn" *)
Theorem fp2 :
exists Y:A->B->prop, (F Y = Y).
witness lfp2. exact (andEL (F lfp2 = lfp2) (forall X:A->B->prop, F X = X -> lfp2 c= X) lfp2_t).
Qed.

End Poly2_fpdef.

Section Poly1_trans_clos.

Variable A:SType.

Variable R:A->A->prop.

(*** Transitive Closure ***)
Definition trans_clos : A->A->prop :=
 lfp2 A A (fun (Q:A->A->prop) (x z:A) => R x z \/ exists y:A, Q x y /\ Q y z).

Let F : (A->A->prop)->A->A->prop := (fun Q:A->A->prop => fun (x z:A) => R x z \/ exists y:A, Q x y /\ Q y z).

(* Treasure "1MfN9X3fr3v8rvGg9m5rrs5vK8UYLvkWuE" *)
Theorem trans_clos_monotone :
 forall Q1 Q2:A->A->prop, Q1 c= Q2 -> F Q1 c= F Q2.
let Q1 Q2:A->A->prop.
assume H1 : forall x z : A, Q1 x z -> Q2 x z.
let x z:A.
assume H2 : (R x z \/ exists y:A, Q1 x y /\ Q1 y z).
prove (R x z \/ exists y:A, Q2 x y /\ Q2 y z).
apply H2.
- assume H3: R x z. apply orIL. exact H3.
- assume H3: exists y:A, Q1 x y /\ Q1 y z.
  apply H3.
  let y:A. assume H4: Q1 x y /\ Q1 y z.
  apply H4.
  assume H5: Q1 x y. assume H6: Q1 y z.
  apply orIR.
  witness y.
  apply andI.
  + exact (H1 x y H5).
  + exact (H1 y z H6).
Qed.

(* Treasure "16oaWDAdXdXwufWooheRFFLAQvvYxaNN3Y" *)
Theorem trans_clos_sub : R c= trans_clos.
claim L1: F trans_clos = trans_clos.
{ exact (andEL (F trans_clos = trans_clos) (forall X:A->A->prop, F X = X -> trans_clos c= X) (lfp2_t A A F trans_clos_monotone)). }
rewrite <- L1.
prove R c= F trans_clos.
let x z:A. assume H1: R x z.
prove R x z \/ exists y:A, trans_clos x y /\ trans_clos y z.
apply orIL.
exact H1.
Qed.

(* Treasure "1JzoaQ9ujPdqM7p9BibgjmrkTia5V9nJRN" *)
Theorem trans_clos_trans : transitive A trans_clos.
claim L1: F trans_clos = trans_clos.
{ exact (andEL (F trans_clos = trans_clos) (forall X:A->A->prop, F X = X -> trans_clos c= X) (lfp2_t A A F trans_clos_monotone)). }
let x y z:A. assume H1: trans_clos x y. assume H2: trans_clos y z.
rewrite <- L1.
prove F trans_clos x z.
prove R x z \/ exists y:A, trans_clos x y /\ trans_clos y z.
apply orIR.
witness y. apply andI.
- exact H1.
- exact H2.
Qed.

(* Treasure "1D1uCNPMsRgpHy5T8Kb9RR1TH1g4aZ5Acx" *)
Theorem trans_clos_ind : forall Q:A->A->prop,
 R c= Q
 ->
 transitive A Q
 ->
 forall x z:A, trans_clos x z -> Q x z.
let Q.
assume H1: R c= Q.
assume H2: transitive A Q.
claim L1 : F Q c= Q.
{ let x z.
  assume H3: R x z \/ exists y:A, Q x y /\ Q y z.
  prove Q x z.
  apply H3.
  - assume H4: R x z.
    exact (H1 x z H4).
  - assume H4: exists y:A, Q x y /\ Q y z.
    apply (H4 (Q x z)). let y. assume H5. apply H5. assume H6 H7.
    exact (H2 x y z H6 H7).
}
let x z.
assume H3: forall p:A->A->prop, F p c= p -> p x z.
prove Q x z.
exact (H3 Q L1).
Qed.

(* Treasure "1Jf61wQN44wuUm5ANHcQLqHYMeDgJeGbSB" *)
Theorem trans_clos_ind_r : forall P:A->prop,
 (forall x y:A, P x -> R x y -> P y)
 ->
 forall x y:A, trans_clos x y -> (forall y:A, R x y -> P y) -> P y.
let P.
assume H1 : forall x y : A, P x -> R x y -> P y.
prove (forall x y:A, trans_clos x y -> (fun x y : A => (forall y : A, R x y -> P y) -> P y) x y).
apply (trans_clos_ind (fun x y : A => (forall y : A, R x y -> P y) -> P y)).
- let x y. assume H2: R x y.
  prove ((forall y : A, R x y -> P y) -> P y).
  assume H3: forall y : A, R x y -> P y.
  prove P y.
  exact (H3 y H2).
- let x y z. 
  assume H2: (forall w:A, R x w -> P w) -> P y.
  assume H3: (forall w:A, R y w -> P w) -> P z.
  prove (forall w:A, R x w -> P w) -> P z.
  assume H4: forall w:A, R x w -> P w.
  claim L1: P y.
  { exact (H2 H4). }
  prove P z.
  apply H3.
  prove forall w:A, R y w -> P w.
  let w.
  assume H5: R y w.
  prove P w.
  exact (H1 y w L1 H5).
Qed.

(* Treasure "1DFbUURULnVi8KMsjZSk1MnmxnkuDcA1YH" *)
Theorem trans_clos_ind_l : forall P:A->prop,
 (forall x y:A, P y -> R x y -> P x)
 ->
 forall x y:A, trans_clos x y -> (forall x:A, R x y -> P x) ->  P x.
let P.
assume H1 : forall x y : A, P y -> R x y -> P x.
prove forall x y:A, trans_clos x y -> (fun x y:A => (forall x:A, R x y -> P x) ->  P x) x y.
apply (trans_clos_ind (fun x y:A => (forall x : A, R x y -> P x) -> P x)).
- let x y:A.
  assume H2: R x y.
  prove (forall x : A, R x y -> P x) -> P x.
  exact (fun H3 => H3 x H2).
- let x y z.
  assume H2: (forall w : A, R w y -> P w) -> P x.
  assume H3: (forall w : A, R w z -> P w) -> P y.
  prove (forall w : A, R w z -> P w) -> P x.
  assume H4: forall w : A, R w z -> P w.
  claim L1: P y.
  { exact (H3 H4). }
  prove P x.
  apply H2.
  prove forall w : A, R w y -> P w.
  let w.
  assume H5: R w y.
  prove P w.
  exact (H1 w y L1 H5).
Qed.

(* Treasure "122t9fgLwT6wET2syBUhy2AgHz2cmCexhv" *)
Theorem trans_clos_inv_r : forall x y:A,
  trans_clos x y -> R x y \/ exists w:A, trans_clos x w /\ R w y.
let x:A.
set P := fun y:A => R x y \/ exists w:A, trans_clos x w /\ R w y.
prove forall y:A, trans_clos x y -> P y.
claim L1: forall y z : A, P y -> R y z -> P z.
{
  let y z.
  assume H2: R x y \/ exists w:A, trans_clos x w /\ R w y.
  assume H3: R y z.
  prove R x z \/ exists w:A, trans_clos x w /\ R w z.
  apply H2.
  - assume H4: R x y.
    apply orIR.
    witness y.
    apply andI.
    + prove trans_clos x y. exact (trans_clos_sub x y H4).
    + exact H3.
  - assume H4: exists w:A, trans_clos x w /\ R w y.
    apply H4. let w. assume H5. apply H5.
    assume H6: trans_clos x w.
    assume H7: R w y.
    apply orIR.
    prove exists w:A, trans_clos x w /\ R w z.
    witness y.
    apply andI.
    + prove trans_clos x y.
      apply (trans_clos_trans x w y).
      * prove trans_clos x w. exact H6.
      * prove trans_clos w y. exact (trans_clos_sub w y H7).
    + exact H3.
}
claim L2: forall y:A, R x y -> P y.
{
  let y:A.
  assume H1: R x y.
  prove R x y \/ exists w:A, trans_clos x w /\ R w y.
  apply orIL.
  exact H1.
}
exact (fun (y:A) (H:trans_clos x y) => trans_clos_ind_r P L1 x y H L2).
Qed.

(* Treasure "1Nhk63Bstkof2Vzvnam2ngKNAbondUmvY5" *)
Theorem trans_clos_inv_l : forall x y:A,
  trans_clos x y -> R x y \/ exists z:A, R x z /\ trans_clos z y.
claim L: forall y x:A, trans_clos x y -> R x y \/ exists z:A, R x z /\ trans_clos z y.
{ 
  let y:A.
  set P := fun x:A => R x y \/ exists w:A, R x w /\ trans_clos w y.
  prove forall x:A, trans_clos x y -> P x.
  claim L1: forall x v : A, P v -> R x v -> P x.
  {
    let x v.
    assume H2: R v y \/ exists w:A, R v w /\ trans_clos w y.
    assume H3: R x v.
    prove R x y \/ exists w:A, R x w /\ trans_clos w y.
    apply H2.
    - assume H4: R v y.
      apply orIR.
      witness v.
      apply andI.
      + exact H3.
      + prove trans_clos v y. exact (trans_clos_sub v y H4).
    - assume H4: exists w:A, R v w /\ trans_clos w y.
      apply H4. let w. assume H5. apply H5.
      assume H6: R v w.
      assume H7: trans_clos w y.
      apply orIR.
      prove exists w:A, R x w /\ trans_clos w y.
      witness v.
      apply andI.
      + exact H3.
      + prove trans_clos v y.
        apply (trans_clos_trans v w y).
        * prove trans_clos v w. exact (trans_clos_sub v w H6).
        * prove trans_clos w y. exact H7.
  }
  claim L2: forall x:A, R x y -> P x.
  {
    let x:A.
    assume H1: R x y.
    prove R x y \/ exists w:A, R x w /\ trans_clos w y.
    apply orIL.
    exact H1.
  }
  exact (fun (x:A) (H:trans_clos x y) => trans_clos_ind_l P L1 x y H L2).
}
exact (fun x y : A => L y x).
Qed.

End Poly1_trans_clos.
