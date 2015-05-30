(*** 
 This file contains some solutions to the problems in CategoryProblems.mg.
 There are still 9 remaining unsolved problems with a total of 0.74 bitcoins
 at addresses (allegedly) corresponding to proofs. The unsolved ones are the
 ones with "Admitted" as a proof.

 Here is how to check the file.

egal -polyexpand -ind IndexMar2014 -I CategoryPreamble.mgs CategoryPartialSolns.mg
 ***)

Section MetaCat.

Variable A B: SType.

Variable Obj: A -> prop.
Variable Hom: A -> A -> B -> prop.
Variable id: A -> B.
Variable comp: A -> A -> A -> B -> B -> B.

Definition idT : prop := forall X:A, Obj X -> Hom X X (id X).
Definition compT : prop :=
 forall X Y Z:A, forall f g:B,
 Obj X -> Obj Y -> Obj Z ->
 Hom X Y f -> Hom Y Z g ->
 Hom X Z (comp X Y Z g f).

Definition idL : prop :=
 forall X Y:A, forall f:B,
 Obj X -> Obj Y -> Hom X Y f -> comp X X Y f (id X) = f.

Definition idR : prop :=
 forall X Y:A, forall f:B,
 Obj X -> Obj Y -> Hom X Y f -> comp X Y Y (id Y) f = f.

Definition compAssoc : prop :=
 forall X Y Z W:A, forall f g h:B,
 Obj X -> Obj Y -> Obj Z -> Obj W ->
 Hom X Y f -> Hom Y Z g -> Hom Z W h ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition MetaCat : prop := (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.

(* Treasure "1B4ULbcbLKGiSV9drWEXLPrV3qSpN8YsYL" *)
Lemma MetaCatI : idT -> compT -> idL -> idR -> compAssoc -> MetaCat.
assume H1 H2 H3 H4 H5.
prove (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.
apply and3I.
- prove idT /\ compT. apply andI.
  + exact H1.
  + exact H2.
- prove idL /\ idR. apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

(*** A proof of MetaCatE is below as MetaCatE_notkey,
 but it's not the proof that gives the private key. ***)

(* Treasure "1L97cJbYVZvU3w2E1DFriRWbP6rQwfwSkH" *)
Lemma MetaCatE : MetaCat -> forall p:prop, (idT -> compT -> idL -> idR -> compAssoc -> p) -> p.
Admitted.

Lemma MetaCatE_notkey : MetaCat -> forall p:prop, (idT -> compT -> idL -> idR -> compAssoc -> p) -> p.
assume Ha: (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.
apply Ha.
assume H1234 H5.
apply H1234.
assume H12 H34.
apply H12.
assume H1 H2.
apply H34.
assume H3 H4.
let p. assume Hb. apply Hb.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

End MetaCat.

Section STypeMetaCat.

Variable A: SType.

Definition SType_Obj : (A->prop)->prop := fun _ => True.
Definition SType_func_eq : (A->prop)->(A->prop)->(A->A)->(A->A)->prop :=
fun X Y f g => forall x:A, X x -> Y (f x) /\ f x = g x.

(*** A proof of SType_func_per is below as SType_func_per_notkey,
 but it's not the proof that gives the key to the address. ***)

(* Treasure "1P4UWfN6cBNSQCAdPgjQTKFXRK8Wgjtt4b" *)
Lemma SType_func_per : forall X Y:A->prop, per (A->A) (SType_func_eq X Y).
Admitted.

Lemma SType_func_per_notkey : forall X Y:A->prop, per (A->A) (SType_func_eq X Y).
let X Y.
prove symmetric (A->A) (SType_func_eq X Y) /\ transitive (A->A) (SType_func_eq X Y).
apply andI.
- let f g.
  assume H1.
(***  assume H1: forall x:A, X x -> Y (f x) /\ f x = g x. ***)
  prove forall x:A, X x -> Y (g x) /\ g x = f x.
  let x. assume Hx. apply (H1 x Hx). assume H1L H1R.
  prove Y (g x) /\ g x = f x.
  apply andI.
  + rewrite <- H1R. exact H1L.
  + exact eq_sym A (f x) (g x) H1R.
- let f g h.
  assume H1 H2.
(***
  assume H1: forall x:A, X x -> Y (f x) /\ f x = g x.
  assume H2: forall x:A, X x -> Y (g x) /\ g x = h x.
 ***)
  prove forall x:A, X x -> Y (f x) /\ f x = h x.
  let x. assume Hx.
  apply (H1 x Hx). assume H1L H1R.
  apply (H2 x Hx). assume H2L H2R.
  apply andI.
  + exact H1L.
  + rewrite H1R.
    exact H2R.
Qed.

Definition c : (A->prop)->(A->prop)->(A->A)->(A->A) := fun X Y => canonical_elt (A->A) (SType_func_eq X Y).

Definition SType_Hom : (A->prop)->(A->prop)->(A->A)->prop :=
 fun X Y => quotient (A->A) (SType_func_eq X Y).

(* Treasure "12aajzYrYTPDKiTqg3gQrau8EFfpcJU6of" *)
Lemma SType_f_eq : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> SType_func_eq X Y f f.
let X Y f. assume H1. let x. assume Hx. apply andI.
- exact H1 x Hx.
- apply eqI A.
Qed.


(* Treasure "199JaEjzmqEdhZRNuuYAtMr4fvETTMD6X5" *)
Lemma SType_c_eq : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> forall x:A, X x -> c X Y f x = f x.
Admitted.

(*** Here is a proof that doesn't give the private key. ***)
Lemma SType_c_eq_notkey : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> forall x:A, X x -> c X Y f x = f x.
let X Y f.
assume H1: forall x:A, X x -> Y (f x).
claim Lp: per (A->A) (SType_func_eq X Y).
{ exact SType_func_per X Y. }
apply Lp.
assume Ls: symmetric (A->A) (SType_func_eq X Y).
assume Lt: transitive (A->A) (SType_func_eq X Y).
claim Lf: SType_func_eq X Y f f.
{ exact SType_f_eq X Y f H1. }
claim L1: SType_func_eq X Y f (canonical_elt (A->A) (SType_func_eq X Y) f).
{ exact canonical_elt_rel (A->A) (SType_func_eq X Y) f Lf. }
claim L2: SType_func_eq X Y (canonical_elt (A->A) (SType_func_eq X Y) f) f.
{ apply Ls. exact L1. }
let x. assume Hx. apply (L2 x Hx).
assume H2: Y (canonical_elt (A->A) (SType_func_eq X Y) f x).
assume H3: canonical_elt (A->A) (SType_func_eq X Y) f x = f x.
exact H3.
Qed.

(* Treasure "1Cf1gdFUYW9z2JhCbYaMVBwNdM2FDcyNuV" *)
Lemma SType_Hom_c : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> SType_Hom X Y (c X Y f).
Admitted.

(*** Here is a proof that doesn't give the private key. ***)
Lemma SType_Hom_c_notkey : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> SType_Hom X Y (c X Y f).
let X Y f.
assume H1: forall x:A, X x -> Y (f x).
claim Lp: per (A->A) (SType_func_eq X Y).
{ exact SType_func_per X Y. }
claim Lf: SType_func_eq X Y f f.
{ exact SType_f_eq X Y f H1. }
prove quotient (A->A) (SType_func_eq X Y) (canonical_elt (A->A) (SType_func_eq X Y) f).
prove (SType_func_eq X Y) (canonical_elt (A->A) (SType_func_eq X Y) f) (canonical_elt (A->A) (SType_func_eq X Y) f)
   /\ (canonical_elt (A->A) (SType_func_eq X Y) f) = (canonical_elt (A->A) (SType_func_eq X Y) (canonical_elt (A->A) (SType_func_eq X Y) f)).
apply andI.
- prove SType_func_eq X Y (c X Y f) (c X Y f).
  let x. assume Hx.
  rewrite SType_c_eq X Y f H1 x Hx.
  apply andI.
  + prove Y (f x).
    exact H1 x Hx.
  + prove f x = f x.
    apply eqI A.
- prove (canonical_elt (A->A) (SType_func_eq X Y) f) = (canonical_elt (A->A) (SType_func_eq X Y) (canonical_elt (A->A) (SType_func_eq X Y) f)).
  apply canonical_elt_idem (A->A) (SType_func_eq X Y).
  + exact Lp.
  + exact Lf.
Qed.

Definition SType_id : (A->prop)->(A->A) := fun X => c X X (fun x:A => x).

Definition SType_comp : (A->prop)->(A->prop)->(A->prop)->(A->A)->(A->A)->(A->A) := fun X Y Z g f => c X Z (fun x => g (f x)).

(* Treasure "15GsD2fDMAMjZaUXR5KM4arwbMbMWtm6Nu" *)
Theorem SType_MetaCat : MetaCat (A->prop) (A->A) SType_Obj SType_Hom SType_id SType_comp.
Admitted.

(*** Here is a proof that doesn't give the private key. ***)
Theorem SType_MetaCat_notkey : MetaCat (A->prop) (A->A) SType_Obj SType_Hom SType_id SType_comp.
apply MetaCatI (A->prop) (A->A).
- prove forall X:A->prop, True -> quotient (A->A) (SType_func_eq X X) (c X X (fun x:A => x)).
  let X. assume _.
  prove quotient (A->A) (SType_func_eq X X) (c X X (fun x:A => x)).
  prove SType_func_eq X X (c X X (fun x:A => x)) (c X X (fun x:A => x)) /\ (c X X (fun x:A => x)) = canonical_elt (A->A) (SType_func_eq X X) (c X X (fun x:A => x)).
  apply andI.
  + apply SType_f_eq.
    prove forall x:A, X x -> X (c X X (fun x:A => x) x).
    let x. assume Hx. rewrite SType_c_eq X X (fun x:A => x) (fun x Hx => Hx) x Hx.
    exact Hx.
  + prove canonical_elt (A->A) (SType_func_eq X X) (fun x => x) = canonical_elt (A->A) (SType_func_eq X X) (canonical_elt (A->A) (SType_func_eq X X) (fun x => x)).
    apply canonical_elt_idem (A->A) (SType_func_eq X X) (SType_func_per X X) (fun x => x).
    prove SType_func_eq X X (fun x => x) (fun x => x).
    exact SType_f_eq X X (fun x => x) (fun x Hx => Hx).
- prove forall X Y Z:A->prop, forall f g:A->A, True -> True -> True
         -> quotient (A->A) (SType_func_eq X Y) f
         -> quotient (A->A) (SType_func_eq Y Z) g
         -> quotient (A->A) (SType_func_eq X Z) (c X Z (fun x => g (f x))).
  let X Y Z f g. assume _ _ _ Hf Hg.
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  claim Lf: forall x:A, X x -> Y (f x).
  { let x. assume Hx. apply (Hf1 x Hx). assume H1 _. exact H1. }
  claim Lg: forall y:A, Y y -> Z (g y).
  { let y. assume Hy. apply (Hg1 y Hy). assume H1 _. exact H1. }
  prove SType_func_eq X Z (c X Z (fun x => g (f x))) (c X Z (fun x => g (f x)))
     /\ c X Z (fun x => g (f x)) = canonical_elt (A->A) (SType_func_eq X Z) (c X Z (fun x => g (f x))).
  apply andI.
  + let x. assume Hx.
    prove Z (c X Z (fun x => g (f x)) x) /\ (c X Z (fun x => g (f x)) x) = (c X Z (fun x => g (f x)) x).
    apply andI.
    * prove Z (c X Z (fun x => g (f x)) x).
      rewrite SType_c_eq X Z (fun x:A => g (f x)) (fun x Hx => Lg (f x) (Lf x Hx)) x Hx.
      prove Z (g (f x)).
      exact Lg (f x) (Lf x Hx).
    * apply eqI A.
  + apply canonical_elt_idem (A->A) (SType_func_eq X Z) (SType_func_per X Z) (fun x => g (f x)).
    prove SType_func_eq X Z (fun x => g (f x)) (fun x => g (f x)).
    exact SType_f_eq X Z (fun x => g (f x)) (fun x Hx => Lg (f x) (Lf x Hx)).
- let X Y f. assume _ _.
  assume Hf: quotient (A->A) (SType_func_eq X Y) f.
  apply Hf.
  assume Hf1: SType_func_eq X Y f f.
  assume Hf2: f = canonical_elt (A->A) (SType_func_eq X Y) f.
  prove SType_comp X X Y f (SType_id X) = f.
  prove c X Y (fun x => f (c X X (fun x => x) x)) = f.
  rewrite Hf2 at 2.
  prove canonical_elt (A->A) (SType_func_eq X Y) (fun x => f (c X X (fun x => x) x)) = canonical_elt (A->A) (SType_func_eq X Y) f.
  apply canonical_elt_eq (A->A) (SType_func_eq X Y) (SType_func_per X Y).
  prove SType_func_eq X Y (fun x => f (c X X (fun x => x) x)) f.
  apply SType_func_per X Y. assume Hs _. apply Hs.
  prove SType_func_eq X Y f (fun x => f (c X X (fun x => x) x)).
  let x. assume Hx.
  apply andI.
  + apply Hf1 x Hx. assume H1 _. exact H1.
  + prove f x = f (c X X (fun x => x) x).
    rewrite SType_c_eq X X (fun x:A => x) (fun x Hx => Hx) x Hx.
    apply eqI A.
- let X Y f. assume _ _.
  assume Hf: quotient (A->A) (SType_func_eq X Y) f.
  apply Hf.
  assume Hf1: SType_func_eq X Y f f.
  assume Hf2: f = canonical_elt (A->A) (SType_func_eq X Y) f.
  prove SType_comp X Y Y (SType_id Y) f = f.
  prove c X Y (fun x => c Y Y (fun y => y) (f x)) = f.
  rewrite Hf2 at 2.
  prove canonical_elt (A->A) (SType_func_eq X Y) (fun x => c Y Y (fun y => y) (f x)) = canonical_elt (A->A) (SType_func_eq X Y) f.
  apply canonical_elt_eq (A->A) (SType_func_eq X Y) (SType_func_per X Y).
  prove SType_func_eq X Y (fun x => c Y Y (fun y => y) (f x)) f.
  apply SType_func_per X Y. assume Hs _. apply Hs.
  prove SType_func_eq X Y f (fun x => c Y Y (fun y => y) (f x)).
  let x. assume Hx.
  claim Lfx: Y (f x).
  { apply Hf1 x Hx. assume H1 _. exact H1. }
  apply andI.
  + exact Lfx.
  + prove f x = c Y Y (fun y => y) (f x).
    rewrite SType_c_eq Y Y (fun y:A => y) (fun y Hy => Hy) (f x) Lfx.
    apply eqI A.
- let X Y Z W f g h. assume _ _ _ _.
  assume Hf: quotient (A->A) (SType_func_eq X Y) f.
  assume Hg: quotient (A->A) (SType_func_eq Y Z) g.
  assume Hh: quotient (A->A) (SType_func_eq Z W) h.
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  apply Hh. assume Hh1 Hh2.
  claim Lf: forall x:A, X x -> Y (f x).
  { let x. assume Hx. apply Hf1 x Hx. assume H1 _. exact H1. }
  claim Lg: forall y:A, Y y -> Z (g y).
  { let y. assume Hy. apply Hg1 y Hy. assume H1 _. exact H1. }
  claim Lh: forall z:A, Z z -> W (h z).
  { let z. assume Hz. apply Hh1 z Hz. assume H1 _. exact H1. }
  prove SType_comp X Y W (SType_comp Y Z W h g) f = SType_comp X Z W h (SType_comp X Y Z g f).
  prove c X W (fun x => c Y W (fun y => h (g y)) (f x)) = c X W (fun x => h (c X Z (fun x => g (f x)) x)).
  prove canonical_elt (A->A) (SType_func_eq X W) (fun x => c Y W (fun y => h (g y)) (f x)) = canonical_elt (A->A) (SType_func_eq X W) (fun x => h (c X Z (fun x => g (f x)) x)).
  apply canonical_elt_eq (A->A) (SType_func_eq X W) (SType_func_per X W).
  prove SType_func_eq X W (fun x => c Y W (fun y => h (g y)) (f x)) (fun x => h (c X Z (fun x => g (f x)) x)).
  let x. assume Hx.
  rewrite SType_c_eq Y W (fun y:A => h (g y)) (fun y Hy => Lh (g y) (Lg y Hy)) (f x) (Lf x Hx).
  apply andI.
  + prove W (h (g (f x))).
    exact (Lh (g (f x)) (Lg (f x) (Lf x Hx))).
  + prove h (g (f x)) = h (c X Z (fun x => g (f x)) x).
    rewrite SType_c_eq X Z (fun x:A => g (f x)) (fun x Hx => Lg (f x) (Lf x Hx)) x Hx.
    prove h (g (f x)) = h (g (f x)).
    apply eqI A.
Qed.

End STypeMetaCat.

Section LocallySmallCat.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition idT' : prop := forall X:set, Obj X -> id X :e Hom X X.
Definition compT' : prop :=
 forall X Y Z:set, forall f g:set,
 Obj X -> Obj Y -> Obj Z ->
 f :e Hom X Y -> g :e Hom Y Z ->
 comp X Y Z g f :e Hom X Z.

Definition idL' : prop :=
 forall X Y:set, forall f:set,
 Obj X -> Obj Y -> f :e Hom X Y -> comp X X Y f (id X) = f.

Definition idR' : prop :=
 forall X Y:set, forall f:set,
 Obj X -> Obj Y -> f :e Hom X Y -> comp X Y Y (id Y) f = f.

Definition compAssoc' : prop :=
 forall X Y Z W:set, forall f g h:set,
 Obj X -> Obj Y -> Obj Z -> Obj W ->
 f :e Hom X Y -> g :e Hom Y Z -> h :e Hom Z W ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition LocallySmallCat : prop := (idT' /\ compT') /\ (idL' /\ idR') /\ compAssoc'.

(* Treasure "1Q3qozuue6B65jZtnNXbzTSEXHCsCSE1Bd" *)
Lemma LocallySmallCatI : idT' -> compT' -> idL' -> idR' -> compAssoc' -> LocallySmallCat.
assume H1 H2 H3 H4 H5.
prove (idT' /\ compT') /\ (idL' /\ idR') /\ compAssoc'.
apply and3I.
- prove idT' /\ compT'. apply andI.
  + exact H1.
  + exact H2.
- prove idL' /\ idR'. apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

(* Treasure "17RWR2NJYxxK6xtPYFAeGee9aghPoWymM" *)
Lemma LocallySmallCatE : LocallySmallCat -> forall p:prop, (idT' -> compT' -> idL' -> idR' -> compAssoc' -> p) -> p.
Admitted.

(*** Here is a proof that doesn't give the private key. ***)
Lemma LocallySmallCatE_notkey : LocallySmallCat -> forall p:prop, (idT' -> compT' -> idL' -> idR' -> compAssoc' -> p) -> p.
assume Ha: (idT' /\ compT') /\ (idL' /\ idR') /\ compAssoc'.
apply Ha.
assume H1234 H5.
apply H1234.
assume H12 H34.
apply H12.
assume H1 H2.
apply H34.
assume H3 H4.
let p. assume Hb. apply Hb.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

(* Treasure "1N9yMCBW5mTW6iCZEubL6Bozb4fgFD3JmV" *)
Theorem LocallySmallCat_MetaCat : LocallySmallCat -> MetaCat set set Obj (fun X Y f => f :e Hom X Y) id comp.
assume Ha. apply LocallySmallCatE Ha.
assume H1 H2 H3 H4 H5.
apply MetaCatI set set.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

End LocallySmallCat.

Section SetLocallySmallCat.

(* Treasure "15J6XWAok73Ak1KGdRgLEsSiWAiueywMx7" *)
Theorem Set_LocallySmallCat : LocallySmallCat (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)).
Admitted.

(*** Here is a proof that does not give the private key. ***)
Theorem Set_LocallySmallCat_notkey : LocallySmallCat (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)).
apply LocallySmallCatI.
- let X. assume _.
  prove (fun x :e X => x) :e X :^: X.
  prove (fun x :e X => x) :e Pi_ x :e X, X.
  apply lam_Pi.
  let x. assume Hx. exact Hx.
- let X Y Z. let f g. assume _ _ _.
  assume Hf: f :e Pi_ x :e X, Y.
  assume Hg: g :e Pi_ y :e Y, Z.
  prove (fun x :e X => g (f x)) :e Z :^: X.
  prove (fun x :e X => g (f x)) :e Pi_ x :e X, Z.
  apply lam_Pi.
  prove forall x :e X, g (f x) :e Z.
  let x. assume Hx. prove g (f x) :e Z.
  exact ap_Pi Y (fun _ => Z) g (f x) Hg (ap_Pi X (fun _ => Y) f x Hf Hx).
- let X Y f. assume _ _.
  assume Hf: f :e Pi_ x :e X, Y.
  prove (fun x :e X => f ((fun x :e X => x) x)) = f.
  claim Lf: (fun x :e X => f ((fun x :e X => x) x)) :e Pi_ x :e X, Y.
  { apply lam_Pi.
    let x. assume Hx.
    prove f ((fun x :e X => x) x) :e Y.
    rewrite beta X (fun x => x) x Hx.
    prove f x :e Y.
    exact ap_Pi X (fun _ => Y) f x Hf Hx.
  }
  apply Pi_ext X (fun _ => Y) (fun x :e X => f ((fun x :e X => x) x)) Lf f Hf.
  let x. assume Hx.
  prove (fun x :e X => f ((fun x :e X => x) x)) x = f x.
  rewrite beta X (fun x => f ((fun x :e X => x) x)) x Hx.
  prove f ((fun x :e X => x) x) = f x.
  rewrite beta X (fun x => x) x Hx.
  prove f x = f x.
  apply eqI set.
- let X Y f. assume _ _.
  assume Hf: f :e Pi_ x :e X, Y.
  prove (fun x :e X => (fun y :e Y => y) (f x)) = f.
  claim Lf: (fun x :e X => (fun y :e Y => y) (f x)) :e Pi_ x :e X, Y.
  { apply lam_Pi.
    let x. assume Hx.
    prove (fun y :e Y => y) (f x) :e Y.
    rewrite beta Y (fun y => y) (f x) (ap_Pi X (fun _ => Y) f x Hf Hx).
    prove f x :e Y.
    exact ap_Pi X (fun _ => Y) f x Hf Hx.
  }
  apply Pi_ext X (fun _ => Y) (fun x :e X => ((fun y :e Y => y) (f x))) Lf f Hf.
  let x. assume Hx.
  prove (fun x :e X => ((fun y :e Y => y) (f x))) x = f x.
  rewrite beta X (fun x => (fun y :e Y => y) (f x)) x Hx.
  prove (fun y :e Y => y) (f x) = f x.
  apply beta Y (fun y => y) (f x).
  exact ap_Pi X (fun _ => Y) f x Hf Hx.  
- let X Y Z W f g h. assume _ _ _ _.
  assume Hf: f :e Pi_ x :e X, Y.
  assume Hg: g :e Pi_ y :e Y, Z.
  assume Hh: h :e Pi_ z :e Z, W.
  prove (fun x :e X => ((fun y :e Y => h (g y)) (f x))) = (fun x :e X => h ((fun x :e X => g (f x)) x)).
  claim L1: (fun x :e X => ((fun y :e Y => h (g y)) (f x))) :e Pi_ x :e X, W.
  { apply lam_Pi.
    let x. assume Hx.
    prove ((fun y :e Y => h (g y)) (f x)) :e W.
    rewrite beta Y (fun y => h (g y)) (f x) (ap_Pi X (fun _ => Y) f x Hf Hx).
    prove h (g (f x)) :e W.
    apply ap_Pi Z (fun _ => W) h (g (f x)) Hh.
    apply ap_Pi Y (fun _ => Z) g (f x) Hg.
    exact ap_Pi X (fun _ => Y) f x Hf Hx.
  }
  claim L2: (fun x :e X => h ((fun x :e X => g (f x)) x)) :e Pi_ x :e X, W.
  { apply lam_Pi.
    prove forall x :e X, h ((fun x :e X => g (f x)) x) :e W.
    let x. assume Hx.
    prove h ((fun x :e X => g (f x)) x) :e W.
    rewrite beta X (fun x => g (f x)) x Hx.
    prove h (g (f x)) :e W.
    apply ap_Pi Z (fun _ => W) h (g (f x)) Hh.
    apply ap_Pi Y (fun _ => Z) g (f x) Hg.
    exact ap_Pi X (fun _ => Y) f x Hf Hx.
  }
  apply Pi_ext X (fun _ => W) (fun x :e X => ((fun y :e Y => h (g y)) (f x))) L1 (fun x :e X => h ((fun x :e X => g (f x)) x)) L2.
  let x. assume Hx.
  prove (fun x :e X => (fun y :e Y => h (g y)) (f x)) x = (fun x :e X => h ((fun x :e X => g (f x)) x)) x.
  rewrite beta X (fun x => h ((fun x :e X => g (f x)) x)) x Hx.
  rewrite beta X (fun x => (fun y :e Y => h (g y)) (f x)) x Hx.
  prove (fun y :e Y => h (g y)) (f x) = h ((fun x :e X => g (f x)) x).
  rewrite beta X (fun x => g (f x)) x Hx.
  prove (fun y :e Y => h (g y)) (f x) = h (g (f x)).
  exact beta Y (fun y => h (g y)) (f x) (ap_Pi X (fun _ => Y) f x Hf Hx).
Qed.

End SetLocallySmallCat.

Section SmallCat.

Variable Obj: set.
Variable Hom: set -> set -> set.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition idT'' : prop := forall X:set, X :e Obj -> id X :e Hom X X.
Definition compT'' : prop :=
 forall X Y Z:set, forall f g:set,
 X :e Obj -> Y :e Obj -> Z :e Obj ->
 f :e Hom X Y -> g :e Hom Y Z ->
 comp X Y Z g f :e Hom X Z.

Definition idL'' : prop :=
 forall X Y:set, forall f:set,
 X :e Obj -> Y :e Obj -> f :e Hom X Y -> comp X X Y f (id X) = f.

Definition idR'' : prop :=
 forall X Y:set, forall f:set,
 X :e Obj -> Y :e Obj -> f :e Hom X Y -> comp X Y Y (id Y) f = f.

Definition compAssoc'' : prop :=
 forall X Y Z W:set, forall f g h:set,
 X :e Obj -> Y :e Obj -> Z :e Obj -> W :e Obj ->
 f :e Hom X Y -> g :e Hom Y Z -> h :e Hom Z W ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition SmallCat : prop := (idT'' /\ compT'') /\ (idL'' /\ idR'') /\ compAssoc''.

(* Treasure "16kVBUdQLkBZ6ctzmxKBGzfs9tr2uJQB8V" *)
Lemma SmallCatI : idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> SmallCat.
assume H1 H2 H3 H4 H5.
prove (idT'' /\ compT'') /\ (idL'' /\ idR'') /\ compAssoc''.
apply and3I.
- prove idT'' /\ compT''. apply andI.
  + exact H1.
  + exact H2.
- prove idL'' /\ idR''. apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

(* Treasure "1DjRZz8325st73S6BdyVvNp8iu1fM7mHB8" *)
Lemma SmallCatE : SmallCat -> forall p:prop, (idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> p) -> p.
Admitted.

(*** Here is a proof that does not give the private key. ***)
Lemma SmallCatE_notkey : SmallCat -> forall p:prop, (idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> p) -> p.
assume Ha: (idT'' /\ compT'') /\ (idL'' /\ idR'') /\ compAssoc''.
apply Ha.
assume H1234 H5.
apply H1234.
assume H12 H34.
apply H12.
assume H1 H2.
apply H34.
assume H3 H4.
let p. assume Hb. apply Hb.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

(* Treasure "1NZkTJwx7iL5he4iQci5GPS6f8npwMDBVa" *)
Theorem SmallCat_LocallySmallCat : SmallCat -> LocallySmallCat (fun X => X :e Obj) Hom id comp.
assume H. apply (SmallCatE H). assume H1 H2 H3 H4 H5. apply LocallySmallCatI.
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

(*** Here is a simpler proof of SmallCat_LocallySmallCat that doesn't give the private key. ***)
Theorem SmallCat_LocallySmallCat_notkey : SmallCat -> LocallySmallCat (fun X => X :e Obj) Hom id comp.
assume H. exact H.
Qed.

(* Treasure "15vMioHL4FGywmyamKocqPsipQdTEwLtsi" *)
Theorem SmallCat_MetaCat : SmallCat -> MetaCat set set (fun X => X :e Obj) (fun X Y f => f :e Hom X Y) id comp.
assume H. apply (SmallCatE H). assume H1 H2 H3 H4 H5. apply (MetaCatI set set).
- exact H1.
- exact H2.
- exact H3.
- exact H4.
- exact H5.
Qed.

(*** Here are two simpler proofs of SmallCat_MetaCat that do not give the private key. ***)
Theorem SmallCat_MetaCat_notkey1 : SmallCat -> MetaCat set set (fun X => X :e Obj) (fun X Y f => f :e Hom X Y) id comp.
assume H. exact H.
Qed.

Theorem SmallCat_MetaCat_notkey2 : SmallCat -> MetaCat set set (fun X => X :e Obj) (fun X Y f => f :e Hom X Y) id comp.
assume H. apply LocallySmallCat_MetaCat. apply SmallCat_LocallySmallCat. exact H.
Qed.

Definition SmallCatAsObject : set := 
(Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)).

End SmallCat.

Definition SmallCatAsObjectP : set -> prop :=
fun C =>
tuple_p 4 C /\ SmallCat (C 0) (fun X Y => C 1 X Y) (fun X => C 2 X) (fun X Y Z g f => C 3 X Y Z g f).

(* Treasure "18fPyPW5m8n435XNVQdkpHb2gziugdx3Cb" *)
Lemma nat_3 : nat_p 3.
exact (nat_ordsucc 2 nat_2).
Qed.

(* Treasure "1MoHG2bJ7FJz1ctpbE4SXFK2Qd9sdDW74b" *)
Lemma In_0_3 : 0 :e 3.
exact (nat_0_in_ordsucc 2 nat_2).
Qed.

(* Treasure "12WLFquAg6Vf8nHj3k7fSVe7Qg3WDepMg9" *)
Lemma In_1_3 : 1 :e 3.
exact (nat_ordsucc_in_ordsucc 2 nat_2 0 In_0_2).
Qed.

(* Treasure "1D2rTKPp3Xek7TajjqKFrJPTyRgribssjD" *)
Lemma In_2_3 : 2 :e 3.
exact (nat_ordsucc_in_ordsucc 2 nat_2 1 In_1_2).
Qed.

(* Treasure "13nQZfbPF2EjMLkxHcD5GEfrNgJ8588nsu" *)
Lemma In_0_4 : 0 :e 4.
exact (nat_0_in_ordsucc 3 nat_3).
Qed.

(* Treasure "1Q1rKj9JR3ymRtkHxSpZWSmKKAtQd4a7Ng" *)
Lemma In_1_4 : 1 :e 4.
exact (nat_ordsucc_in_ordsucc 3 nat_3 0 In_0_3).
Qed.

(* Treasure "1MqLTGydfUM6KVjscjm4UmAX3eFU43tZnW" *)
Lemma In_2_4 : 2 :e 4.
exact (nat_ordsucc_in_ordsucc 3 nat_3 1 In_1_3).
Qed.

(* Treasure "1Q1WgPiPFeF5gYiUkX55du7q3QmJxZAJ7" *)
Lemma In_3_4 : 3 :e 4.
exact (nat_ordsucc_in_ordsucc 3 nat_3 2 In_2_3).
Qed.

(* Treasure "196992JbyK5BC9rZzpQLhZi1YNR8WCybqL" *)
Lemma neq_3_0 : 3 <> 0.
exact (neq_ordsucc_0 2).
Qed.

(* Treasure "1CcAS3MKko66XWRALwkM4RmyaQ3VtECiod" *)
Lemma neq_3_1 : 3 <> 1.
apply ordsucc_inj_contra.
exact neq_2_0.
Qed.

(* Treasure "13EkX2kV7c5SRPsS5FckF5EmEbgZP1yD3p" *)
Lemma neq_3_2 : 3 <> 2.
apply ordsucc_inj_contra.
exact neq_2_1.
Qed.

Section Tuple4.

Variable x y z w:set.

(* Treasure "1GSrZjdjXH2rL8oT11Lj5phVmM7CkUmZmM" *)
Lemma tuple_4_0_eq : (x,y,z,w) 0 = x.
prove (fun i :e 4 => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 0 = x.
rewrite beta 4 (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 0 In_0_4.
prove (if 0 = 0 then x else if 0 = 1 then y else if 0 = 2 then z else w) = x.
apply If_1 set.
apply eqI set.
Qed.

(* Treasure "18Yojrn7P3urPLp7Ht83dBvk2H4Du9uATY" *)
Lemma tuple_4_1_eq : (x,y,z,w) 1 = y.
prove (fun i :e 4 => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 1 = y.
rewrite beta 4 (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 1 In_1_4.
prove (if 1 = 0 then x else if 1 = 1 then y else if 1 = 2 then z else w) = y.
rewrite If_0 set.
- prove (if 1 = 1 then y else if 1 = 2 then z else w) = y.
  apply If_1 set.
  apply eqI set.
- prove 1 <> 0.
  exact neq_1_0.
Qed.

(* Treasure "12Jw1ZzB2eKUewWVGeknvwTRXexcntapBg" *)
Lemma tuple_4_2_eq : (x,y,z,w) 2 = z.
prove (fun i :e 4 => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 2 = z.
rewrite beta 4 (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 2 In_2_4.
prove (if 2 = 0 then x else if 2 = 1 then y else if 2 = 2 then z else w) = z.
rewrite If_0 set.
- prove (if 2 = 1 then y else if 2 = 2 then z else w) = z.
  rewrite If_0 set.
  + apply If_1 set.
    apply eqI set.
  + prove 2 <> 1.
    exact neq_2_1.
- prove 2 <> 0.
  exact neq_2_0.
Qed.

(* Treasure "1Q1hRDAf8GMGroUGm4gNrpUokPHL6tb3Vm" *)
Lemma tuple_4_3_eq : (x,y,z,w) 3 = w.
prove (fun i :e 4 => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 3 = w.
rewrite beta 4 (fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else w) 3 In_3_4.
prove (if 3 = 0 then x else if 3 = 1 then y else if 3 = 2 then z else w) = w.
rewrite If_0 set.
- prove (if 3 = 1 then y else if 3 = 2 then z else w) = w.
  rewrite If_0 set.
  + apply If_0 set.
    prove 3 <> 2.
    exact neq_3_2.
  + prove 3 <> 1.
    exact neq_3_1.
- prove 3 <> 0.
  exact neq_3_0.
Qed.

End Tuple4.

Section betas.

Variable X:set.
Variable Y:set->set.

(* Treasure "17yu4oHpf9jozkuvBHkSTD6Bg4W78uHSxx" *)
Lemma beta2 : forall f:set->set->set, forall x :e X, forall y :e Y x, (fun x :e X => fun y :e Y x => f x y) x y = f x y.
let f x. assume Hx. let y. assume Hy.
rewrite beta X (fun x => fun y :e Y x => f x y) x Hx.
prove (fun y :e Y x => f x y) y = f x y.
apply beta (Y x) (fun y => f x y) y Hy.
Qed.

Variable Z:set->set->set.

(* Treasure "18XGahhthDHaSP4k6jmzpyiK3BC172v23V" *)
Lemma beta3 : forall f:set->set->set->set, forall x :e X, forall y :e Y x, forall z :e Z x y, (fun x :e X => fun y :e Y x => fun z :e Z x y => f x y z) x y z = f x y z.
let f x. assume Hx. let y. assume Hy. let z. assume Hz.
rewrite beta2 (fun x y => fun z :e Z x y => f x y z) x Hx y Hy.
prove (fun z :e Z x y => f x y z) z = f x y z.
apply beta (Z x y) (f x y) z Hz.
Qed.

(***
let f x. assume Hx. let y. assume Hy. let z. assume Hz.
rewrite beta X (fun x => fun y :e Y x => fun z :e Z x y => f x y z) x Hx.
prove (fun y :e Y x => fun z :e Z x y => f x y z) y z = f x y z.
rewrite beta (Y x) (fun y => fun z :e Z x y => f x y z) y Hy.
prove (fun z :e Z x y => f x y z) z = f x y z.
apply beta (Z x y) (f x y) z Hz.
Qed.
***)

Variable W:set->set->set->set.

(* Treasure "13wxt5NYpPh8AWjL2tQDWEoRwuRzvAn84B" *)
Lemma beta4 : forall f:set->set->set->set->set, forall x :e X, forall y :e Y x, forall z :e Z x y, forall w :e W x y z, (fun x :e X => fun y :e Y x => fun z :e Z x y => fun w :e W x y z => f x y z w) x y z w = f x y z w.
let f x. assume Hx. let y. assume Hy. let z. assume Hz. let w. assume Hw.
rewrite beta3 (fun x y z => fun w :e W x y z => f x y z w) x Hx y Hy z Hz.
prove (fun w :e W x y z => f x y z w) w = f x y z w.
apply beta (W x y z) (f x y z) w Hw.
Qed.

(***
let f x. assume Hx. let y. assume Hy. let z. assume Hz. let w. assume Hw.
rewrite beta X (fun x => fun y :e Y x => fun z :e Z x y => fun w :e W x y z => f x y z w) x Hx.
prove (fun y :e Y x => fun z :e Z x y => fun w :e W x y z => f x y z w) y z w = f x y z w.
rewrite beta (Y x) (fun y => fun z :e Z x y => fun w :e W x y z => f x y z w) y Hy.
prove (fun z :e Z x y => fun w :e W x y z => f x y z w) z w = f x y z w.
rewrite beta (Z x y) (fun z => fun w :e W x y z => f x y z w) z Hz.
prove (fun w :e W x y z => f x y z w) w = f x y z w.
apply beta (W x y z) (f x y z) w Hw.
Qed.
***)

Variable U:set->set->set->set->set.

(* Treasure "19tNXYL16QHdW5drVYP6NtpjW5diH1CU7g" *)
Lemma beta5 : forall f:set->set->set->set->set->set, forall x :e X, forall y :e Y x, forall z :e Z x y, forall w :e W x y z, forall u :e U x y z w, (fun x :e X => fun y :e Y x => fun z :e Z x y => fun w :e W x y z => fun u :e U x y z w => f x y z w u) x y z w u = f x y z w u.
let f x. assume Hx. let y. assume Hy. let z. assume Hz. let w. assume Hw. let u. assume Hu.
rewrite beta4 (fun x y z w => fun u :e U x y z w => f x y z w u) x Hx y Hy z Hz w Hw.
prove (fun u :e U x y z w => f x y z w u) u = f x y z w u.
apply beta (U x y z w) (f x y z w) u Hu.
Qed.

End betas.

(***
 A proof that does not give the private key is given below as SmallCatAsObject_1_notkey.
 ***)

(* Treasure "1JW6ruek8KUuNZaanEhgQB8rAcSGcb26WC" *)
Theorem SmallCatAsObject_1 :
forall (Obj:set) (Hom:set -> set -> set) (id:set->set) (comp:set->set->set->set->set->set),
SmallCat Obj Hom id comp ->
SmallCatAsObject Obj Hom id comp 0 = Obj
/\
(forall X Y :e Obj, SmallCatAsObject Obj Hom id comp 1 X Y = Hom X Y)
/\
(forall X :e Obj,SmallCatAsObject Obj Hom id comp 2 X = id X)
/\
(forall (X Y Z :e Obj) (g :e Hom Y Z) (f :e Hom X Y), SmallCatAsObject Obj Hom id comp 3 X Y Z g f = comp X Y Z g f)
/\
SmallCatAsObjectP (SmallCatAsObject Obj Hom id comp).
Admitted.

Theorem SmallCatAsObject_1_notkey :
forall (Obj:set) (Hom:set -> set -> set) (id:set->set) (comp:set->set->set->set->set->set),
SmallCat Obj Hom id comp ->
SmallCatAsObject Obj Hom id comp 0 = Obj
/\
(forall X Y :e Obj, SmallCatAsObject Obj Hom id comp 1 X Y = Hom X Y)
/\
(forall X :e Obj,SmallCatAsObject Obj Hom id comp 2 X = id X)
/\
(forall (X Y Z :e Obj) (g :e Hom Y Z) (f :e Hom X Y), SmallCatAsObject Obj Hom id comp 3 X Y Z g f = comp X Y Z g f)
/\
SmallCatAsObjectP (SmallCatAsObject Obj Hom id comp).
let Obj Hom id comp. assume H.
claim L0: SmallCatAsObject Obj Hom id comp 0 = Obj.
{ prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 0 = Obj.
  apply tuple_4_0_eq.
}
claim L1: forall X Y :e Obj, SmallCatAsObject Obj Hom id comp 1 X Y = Hom X Y.
{ let X. assume HX. let Y. assume HY.
  prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 1 X Y = Hom X Y.
  rewrite tuple_4_1_eq.
  prove (fun X :e Obj => fun Y :e Obj => Hom X Y) X Y = Hom X Y.
  exact beta2 Obj (fun _ => Obj) Hom X HX Y HY.
}
claim L2: forall X :e Obj,SmallCatAsObject Obj Hom id comp 2 X = id X.
{ let X. assume HX.
  prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 2 X = id X.
  rewrite tuple_4_2_eq.
  prove (fun X :e Obj => id X) X = id X.
  exact beta Obj id X HX.
}
claim L3: forall (X Y Z :e Obj) (g :e Hom Y Z) (f :e Hom X Y), SmallCatAsObject Obj Hom id comp 3 X Y Z g f = comp X Y Z g f.
{ let X. assume HX. let Y. assume HY. let Z. assume HZ. let g. assume Hg. let f. assume Hf.
  prove (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)) 3 X Y Z g f = comp X Y Z g f.
  rewrite tuple_4_3_eq.
  prove (fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f) X Y Z g f = comp X Y Z g f.
  exact beta5 Obj (fun _ => Obj) (fun _ _ => Obj) (fun _ Y Z => Hom Y Z) (fun X Y _ _ => Hom X Y) comp X HX Y HY Z HZ g Hg f Hf.
}
apply and5I.
- exact L0.
- exact L1.
- exact L2.
- exact L3.
- prove tuple_p 4 (SmallCatAsObject Obj Hom id comp)
     /\ SmallCat (SmallCatAsObject Obj Hom id comp 0)
                 (fun X Y => SmallCatAsObject Obj Hom id comp 1 X Y)
                 (fun X => SmallCatAsObject Obj Hom id comp 2 X)
                 (fun X Y Z g f => SmallCatAsObject Obj Hom id comp 3 X Y Z g f).
  apply andI.
  + prove tuple_p 4 (Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)).
    apply tuple_p_4_tuple.
  + apply SmallCatE Obj Hom id comp H.
    assume H1 H2 H3 H4 H5.
    rewrite L0.
    apply SmallCatI.
    * prove forall X :e Obj, SmallCatAsObject Obj Hom id comp 2 X :e SmallCatAsObject Obj Hom id comp 1 X X.
      let X. assume HX.
      rewrite L1 X HX X HX. rewrite L2 X HX. exact H1 X HX.
    * prove forall X Y Z f g, X :e Obj -> Y :e Obj -> Z :e Obj -> f :e SmallCatAsObject Obj Hom id comp 1 X Y -> g :e SmallCatAsObject Obj Hom id comp 1 Y Z -> SmallCatAsObject Obj Hom id comp 3 X Y Z g f :e SmallCatAsObject Obj Hom id comp 1 X Z.
      let X Y Z f g. assume HX HY HZ. rewrite L1 X HX Y HY. rewrite L1 Y HY Z HZ.
      assume Hf: f :e Hom X Y.
      assume Hg: g :e Hom Y Z.
      prove SmallCatAsObject Obj Hom id comp 3 X Y Z g f :e SmallCatAsObject Obj Hom id comp 1 X Z.
      rewrite L3 X HX Y HY Z HZ g Hg f Hf.
      rewrite L1 X HX Z HZ.
      exact H2 X Y Z f g HX HY HZ Hf Hg.
    * prove forall X Y f, X :e Obj -> Y :e Obj -> f :e SmallCatAsObject Obj Hom id comp 1 X Y -> SmallCatAsObject Obj Hom id comp 3 X X Y f (SmallCatAsObject Obj Hom id comp 2 X) = f.
      let X Y f. assume HX HY. rewrite L1 X HX Y HY.
      assume Hf: f :e Hom X Y.
      prove SmallCatAsObject Obj Hom id comp 3 X X Y f (SmallCatAsObject Obj Hom id comp 2 X) = f.
      rewrite L2 X HX.
      prove SmallCatAsObject Obj Hom id comp 3 X X Y f (id X) = f.
      rewrite L3 X HX X HX Y HY f Hf (id X) (H1 X HX).
      prove comp X X Y f (id X) = f.
      exact H3 X Y f HX HY Hf.
    * prove forall X Y f, X :e Obj -> Y :e Obj -> f :e SmallCatAsObject Obj Hom id comp 1 X Y -> SmallCatAsObject Obj Hom id comp 3 X Y Y (SmallCatAsObject Obj Hom id comp 2 Y) f = f.
      let X Y f. assume HX HY. rewrite L1 X HX Y HY.
      assume Hf: f :e Hom X Y.
      prove SmallCatAsObject Obj Hom id comp 3 X Y Y (SmallCatAsObject Obj Hom id comp 2 Y) f = f.
      rewrite L2 Y HY.
      prove SmallCatAsObject Obj Hom id comp 3 X Y Y (id Y) f = f.
      rewrite L3 X HX Y HY Y HY (id Y) (H1 Y HY) f Hf.
      prove comp X Y Y (id Y) f = f.
      exact H4 X Y f HX HY Hf.
    * prove forall X Y Z W f g h, X :e Obj -> Y :e Obj -> Z :e Obj -> W :e Obj -> f :e SmallCatAsObject Obj Hom id comp 1 X Y -> g :e SmallCatAsObject Obj Hom id comp 1 Y Z -> h :e SmallCatAsObject Obj Hom id comp 1 Z W -> SmallCatAsObject Obj Hom id comp 3 X Y W (SmallCatAsObject Obj Hom id comp 3 Y Z W h g) f = SmallCatAsObject Obj Hom id comp 3 X Z W h (SmallCatAsObject Obj Hom id comp 3 X Y Z g f).
      let X Y Z W f g h. assume HX HY HZ HW.
      rewrite L1 X HX Y HY.
      rewrite L1 Y HY Z HZ.
      rewrite L1 Z HZ W HW.
      assume Hf: f :e Hom X Y.
      assume Hg: g :e Hom Y Z.
      assume Hh: h :e Hom Z W.
      rewrite L3 X HX Y HY Z HZ g Hg f Hf.
      rewrite L3 Y HY Z HZ W HW h Hh g Hg.
      prove SmallCatAsObject Obj Hom id comp 3 X Y W (comp Y Z W h g) f = SmallCatAsObject Obj Hom id comp 3 X Z W h (comp X Y Z g f).
      rewrite L3 X HX Y HY W HW (comp Y Z W h g) (H2 Y Z W g h HY HZ HW Hg Hh) f Hf.
      prove comp X Y W (comp Y Z W h g) f = SmallCatAsObject Obj Hom id comp 3 X Z W h (comp X Y Z g f).
      rewrite L3 X HX Z HZ W HW h Hh (comp X Y Z g f) (H2 X Y Z f g HX HY HZ Hf Hg).
      exact H5 X Y Z W f g h HX HY HZ HW Hf Hg Hh.
Qed.
