(* Title "Introductory Category Theory (Proofs as Exercises)" *)
(* Author "Chad E. Brown" *)

Require "7844A7A5CEF64A8BD7CD22F33421F34967DB6CB2". (** for Qeditas **)

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

Lemma MetaCatI : idT -> compT -> idL -> idR -> compAssoc -> MetaCat.
Admitted.

Lemma MetaCatE : MetaCat -> forall p:prop, (idT -> compT -> idL -> idR -> compAssoc -> p) -> p.
Admitted.

End MetaCat.

Section STypeMetaCat.

Variable A: SType.

Definition SType_Obj : (A->prop)->prop := fun _ => True.
Definition SType_func_eq : (A->prop)->(A->prop)->(A->A)->(A->A)->prop :=
fun X Y f g => forall x:A, X x -> Y (f x) /\ f x = g x.

Lemma SType_func_per : forall X Y:A->prop, per (A->A) (SType_func_eq X Y).
Admitted.

Definition c : (A->prop)->(A->prop)->(A->A)->(A->A) := fun X Y => canonical_elt (A->A) (SType_func_eq X Y).

Definition SType_Hom : (A->prop)->(A->prop)->(A->A)->prop :=
 fun X Y => quotient (A->A) (SType_func_eq X Y).

Lemma SType_f_eq : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> SType_func_eq X Y f f.
Admitted.

Lemma SType_c_eq : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> forall x:A, X x -> c X Y f x = f x.
Admitted.

Lemma SType_Hom_c : forall X Y:A->prop, forall f:A->A, (forall x:A, X x -> Y (f x)) -> SType_Hom X Y (c X Y f).
Admitted.

Definition SType_id : (A->prop)->(A->A) := fun X => c X X (fun x:A => x).

Definition SType_comp : (A->prop)->(A->prop)->(A->prop)->(A->A)->(A->A)->(A->A) := fun X Y Z g f => c X Z (fun x => g (f x)).

Theorem SType_MetaCat : MetaCat (A->prop) (A->A) SType_Obj SType_Hom SType_id SType_comp.
Admitted.

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

Lemma LocallySmallCatI : idT' -> compT' -> idL' -> idR' -> compAssoc' -> LocallySmallCat.
Admitted.

Lemma LocallySmallCatE : LocallySmallCat -> forall p:prop, (idT' -> compT' -> idL' -> idR' -> compAssoc' -> p) -> p.
Admitted.

Theorem LocallySmallCat_MetaCat : LocallySmallCat -> MetaCat set set Obj (fun X Y f => f :e Hom X Y) id comp.
Admitted.

End LocallySmallCat.

Section SetLocallySmallCat.

Theorem Set_LocallySmallCat : LocallySmallCat (fun _ => True) (fun X Y => Y :^: X) (fun X => fun x :e X => x) (fun X Y Z g f => fun x :e X => g (f x)).
Admitted.

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

Lemma SmallCatI : idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> SmallCat.
Admitted.

Lemma SmallCatE : SmallCat -> forall p:prop, (idT'' -> compT'' -> idL'' -> idR'' -> compAssoc'' -> p) -> p.
Admitted.

Theorem SmallCat_LocallySmallCat : SmallCat -> LocallySmallCat (fun X => X :e Obj) Hom id comp.
Admitted.

Theorem SmallCat_MetaCat : SmallCat -> MetaCat set set (fun X => X :e Obj) (fun X Y f => f :e Hom X Y) id comp.
Admitted.

Definition SmallCatAsObject : set := 
(Obj,(fun X :e Obj => fun Y :e Obj => Hom X Y),(fun X :e Obj => id X),(fun X :e Obj => fun Y :e Obj => fun Z :e Obj => fun g :e Hom Y Z => fun f :e Hom X Y => comp X Y Z g f)).

End SmallCat.

Definition SmallCatAsObjectP : set -> prop :=
fun C =>
tuple_p 4 C /\ SmallCat (C 0) (fun X Y => C 1 X Y) (fun X => C 2 X) (fun X Y Z g f => C 3 X Y Z g f).

Lemma nat_3 : nat_p 3.
Admitted.

Lemma In_0_3 : 0 :e 3.
Admitted.

Lemma In_1_3 : 1 :e 3.
Admitted.

Lemma In_2_3 : 2 :e 3.
Admitted.

Lemma In_0_4 : 0 :e 4.
Admitted.

Lemma In_1_4 : 1 :e 4.
Admitted.

Lemma In_2_4 : 2 :e 4.
Admitted.

Lemma In_3_4 : 3 :e 4.
Admitted.

Lemma neq_3_0 : 3 <> 0.
Admitted.

Lemma neq_3_1 : 3 <> 1.
Admitted.

Lemma neq_3_2 : 3 <> 2.
Admitted.

Section Tuple4.

Variable x y z w:set.

Lemma tuple_4_0_eq : (x,y,z,w) 0 = x.
Admitted.

Lemma tuple_4_1_eq : (x,y,z,w) 1 = y.
Admitted.

Lemma tuple_4_2_eq : (x,y,z,w) 2 = z.
Admitted.

Lemma tuple_4_3_eq : (x,y,z,w) 3 = w.
Admitted.

End Tuple4.

Section betas.

Variable X:set.
Variable Y:set->set.

Lemma beta2 : forall f:set->set->set, forall x :e X, forall y :e Y x, (fun x :e X => fun y :e Y x => f x y) x y = f x y.
Admitted.

Variable Z:set->set->set.

Lemma beta3 : forall f:set->set->set->set, forall x :e X, forall y :e Y x, forall z :e Z x y, (fun x :e X => fun y :e Y x => fun z :e Z x y => f x y z) x y z = f x y z.
Admitted.

Variable W:set->set->set->set.

Lemma beta4 : forall f:set->set->set->set->set, forall x :e X, forall y :e Y x, forall z :e Z x y, forall w :e W x y z, (fun x :e X => fun y :e Y x => fun z :e Z x y => fun w :e W x y z => f x y z w) x y z w = f x y z w.
Admitted.

Variable U:set->set->set->set->set.

Lemma beta5 : forall f:set->set->set->set->set->set, forall x :e X, forall y :e Y x, forall z :e Z x y, forall w :e W x y z, forall u :e U x y z w, (fun x :e X => fun y :e Y x => fun z :e Z x y => fun w :e W x y z => fun u :e U x y z w => f x y z w u) x y z w u = f x y z w u.
Admitted.

End betas.

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
