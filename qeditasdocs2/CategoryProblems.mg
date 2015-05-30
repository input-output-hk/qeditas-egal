(* Title "Introductory Category Theory (Proofs as Exercises)" *)
(* Author "Chad E. Brown" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
(* Unicode True "22A4" *)
Definition True : prop := forall P : prop , P -> P.
Axiom TrueI : True.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
Axiom andI : forall A B : prop , A -> B -> A /\ B.
Axiom and3I : forall P1 P2 P3 : prop, P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
Axiom and3E : forall P1 P2 P3: prop, P1 /\ P2 /\ P3 -> (forall p : prop , (P1 -> P2 -> P3 -> p) -> p).
Axiom and5I : forall P1 P2 P3 P4 P5: prop, P1 -> P2 -> P3 -> P4 -> P5 -> P1 /\ P2 /\ P3 /\ P4 /\ P5.
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
Definition neq : A -> A -> prop := fun x y => ~ eq x y.
End Poly1_eq.
Infix = 502 := eq.
(* Unicode <> "2260" *)
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
(* Unicode exists "2203" *)
Binder+ exists , := ex.
Section Poly1_exthms.
Variable A : SType.
Axiom exI : forall P : A -> prop , forall x : A , P x -> exists x : A , P x.
Axiom exandE : forall P Q : A -> prop , (exists x : A , P x /\ Q x) -> forall p : prop , (forall x : A , P x -> Q x -> p) -> p.
End Poly1_exthms.
Axiom prop_ext2 : forall A B : prop , (A -> B) -> (B -> A) -> A = B.
Section FE.
Variable A B : SType.
Axiom func_ext : forall f g : A -> B , (forall x : A , f x = g x) -> f = g.
End FE.
Section PE.
Variable A : SType.
Axiom pred_ext : forall P Q : A -> prop , P c= Q -> Q c= P -> P = Q.
End PE.
Section RE.
Variable A B : SType.
Axiom reln_ext : forall R S : A -> B -> prop , R c= S -> S c= R -> R = S.
End RE.
Section RelnPoly1.
Variable A : SType.
Definition symmetric : (A -> A -> prop) -> prop := fun R => forall x y : A , R x y -> R y x.
Definition transitive : (A -> A -> prop) -> prop := fun R => forall x y z : A , R x y -> R y z -> R x z.
Definition per : (A -> A -> prop) -> prop := fun R => symmetric R /\ transitive R.
Axiom per_tra : forall R : A -> A -> prop , per R -> transitive R.
Axiom per_stra1 : forall R : A -> A -> prop , per R -> forall x y z : A , R y x -> R y z -> R x z.
Axiom per_ref1 : forall R : A -> A -> prop , per R -> forall x y : A , R x y -> R x x.
End RelnPoly1.
Section Choice.
Variable A : SType.
Parameter Eps : (A -> prop) -> A.
Axiom EpsR : forall P : A -> prop , forall x : A , P x -> P (Eps P).
End Choice.
Binder some , := Eps.
Section Poly1_Quotient.
Variable A:SType.
Definition canonical_elt : (A->A->prop)->A->A := fun R:A->A->prop => fun x:A => some y:A, R x y.
Axiom canonical_elt_rel : forall R:A->A->prop, forall x:A, R x x -> R x (canonical_elt R x).
Axiom canonical_elt_eq : forall R:A->A->prop, per A R -> forall x y:A, R x y -> canonical_elt R x = canonical_elt R y.
Axiom canonical_elt_idem : forall R:A->A->prop, per A R -> forall x:A, R x x -> canonical_elt R x = canonical_elt R (canonical_elt R x).
Definition quotient : (A->A->prop)->A->prop := fun R:A->A->prop => fun x:A => R x x /\ x = canonical_elt R x.
Axiom quotient_prop1 : forall R:A->A->prop, forall x:A, quotient R x -> R x x.
Axiom quotient_prop2 : forall R:A->A->prop, per A R -> forall x y:A, quotient R x -> quotient R y -> R x y -> x = y.
End Poly1_Quotient.
Section IfA.
Variable A : SType.
Definition If : prop -> A -> A -> A := (fun p x y => some z : A , p /\ z = x \/ ~ p /\ z = y).
Notation IfThenElse If.
Axiom If_0 : forall p : prop , forall x y : A , ~ p -> (if p then x else y) = y.
Axiom If_1 : forall p : prop , forall x y : A , p -> (if p then x else y) = x.
Axiom If_or : forall p : prop , forall x y : A , (if p then x else y) = x \/ (if p then x else y) = y.
End IfA.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Binder+ exists , := ex ; and.
(* Unicode Empty "2205" *)
Parameter Empty : set.
(* Parameter ordsucc MJAVHZ4UTjfNkP94R1Y274wA1jSL4zvYwwczio73KbaM1Zkf *)
Parameter ordsucc : set -> set.
Notation Nat Empty ordsucc.
Axiom ordsuccI1 : forall x:set, x c= ordsucc x.
Axiom ordsuccI2 : forall x:set, x :e ordsucc x.
Axiom neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
Axiom ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.
Axiom In_0_1 : 0 :e 1.
Axiom In_1_2 : 1 :e 2.
Axiom In_0_2 : 0 :e 2.
Axiom neq_1_0 : 1 <> 0.
Axiom neq_2_0 : 2 <> 0.
Axiom neq_2_1 : 2 <> 1.
(* Parameter nat_p MM7h5JJFu4ht2QGew1BmqmUSYMFFNC39uHR7ZMS73v8B48QF *)
Parameter nat_p : set -> prop.
Axiom nat_0 : nat_p 0.
Axiom nat_ordsucc : forall n : set , nat_p n -> nat_p (ordsucc n).
Axiom nat_1 : nat_p 1.
Axiom nat_2 : nat_p 2.
Axiom nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
Axiom nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
(* Parameter pair MJmS5j2rXbcGEf2zSu7NM7dNRSPAF7wSkRVV2u9AJZfT9Gnm *)
Parameter pair : set -> set -> set.
(* Parameter lam MHMjeodfKZVQDpM5vx4QZCQf3j9mMxhzXxFc99Ytj6RVM875 *)
Parameter lam : set -> (set -> set) -> set.
(* Parameter ap MM1qkKFb3qq2N7sjykoBL5C4syLZdvJigsqUdjvVtQsMZvpS *)
Parameter ap : set -> set -> set.
Notation SetImplicitOp ap.
Notation SetLam lam.
Axiom lamE : forall X : set , forall F : set -> set , forall z : set , z :e (fun x :e X => F x) -> exists x :e X , exists y :e F x , z = pair x y.
Axiom apI : forall f x y , pair x y :e f -> y :e f x.
Axiom apE : forall f x y , y :e f x -> pair x y :e f.
Axiom beta : forall X : set , forall F : set -> set , forall x : set , x :e X -> (fun x :e X => F x) x = F x.
Axiom beta0 : forall X : set , forall F : set -> set , forall x : set , x /:e X -> (fun x :e X => F x) x = 0.
(* Parameter tuple_p MMTwYHqF5iPe31EPR5ua9SmTp84WXctay7MN8WiWvPubpZsi *)
Parameter tuple_p : set->set->prop.
Axiom tuple_p_4_tuple : forall x y z w:set, tuple_p 4 (x,y,z,w).
(* Parameter Pi MKdsnz5mdMV9kTZfLqNEh5ck5akiwWgJFQ4Nv3gQ2gsvsSW3 *)
Parameter Pi : set -> (set -> set) -> set.
(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.
Axiom lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set, (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
Axiom ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.
Axiom Pi_ext : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x = g x) -> f = g.
Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.
(* Superscript :^: *)
Infix :^: 430 left := setexp.


(** Main Body **)

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
