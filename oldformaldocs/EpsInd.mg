(* Title "Epsilon Induction and Recursion" *)
(* Author "Chad E. Brown" *)

(* Salt "Qq1NZYja5FAbneLf" *)

Axiom In_ind : forall P:set->prop, (forall X:set, (forall x:set, x :e X -> P x) -> P X) -> forall X:set, P X.

(* Treasure "17rERvaEEtqDHMGyCeadvZ6QdEm9jMNzu9" *)
Theorem In_irref : forall x, x /:e x.
apply In_ind.
prove (forall X:set, (forall x:set, x :e X -> x /:e x) -> X /:e X).
let X.
assume IH: forall x : set, x :e X -> x /:e x.
assume H: X :e X.
prove False.
exact (IH X H H).
Qed.

(* Treasure "1P6aDY1LRV7SmESmjNnQFXPPAYPmNUpdPx" *)
Theorem In_no2cycle : forall x y, x :e y -> y /:e x.
apply In_ind.
let x.
assume IH: forall z, z :e x -> forall y, z :e y -> y /:e z.
let y.
assume H1: x :e y.
assume H2: y :e x.
exact (IH y H2 x H2 H1).
Qed.

(* Treasure "1H6u2twi6i5QmSzJWvZbHKskY3Yhu16Z99" *)
Theorem Regularity : forall X x:set, x :e X -> exists Y:set, Y :e X /\ ~exists z:set, z :e X /\ z :e Y.
let X x.
assume H1: x :e X.
apply NNPP.
assume H2: ~exists Y:set, Y :e X /\ ~exists z:set, z :e X /\ z :e Y.
claim L1: forall x, x /:e X.
{
  apply In_ind.
  let Y.
  assume IH: forall y, y :e Y -> y /:e X.
  assume H4: Y :e X.
  apply H2.
  witness Y.
  apply andI.
  - exact H4.
  - assume H5: exists z, z :e X /\ z :e Y.
    apply (exandE set (fun z => z :e X) (fun z => z :e Y) H5).
    let z.
    assume H6: z :e X.
    assume H7: z :e Y.
    exact (IH z H7 H6).
}
exact (L1 x H1).
Qed.

(*** epsilon recursion ***)
Section EpsilonRec.
Variable F:set -> (set -> set) -> set.

Definition In_rec_G : set -> set -> prop :=
fun X Y =>
forall R:set->set->prop,
(forall X:set, forall f:set->set, (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.

Definition In_rec : set -> set := fun X => some Y:set, In_rec_G X Y.

(* Treasure "1KnoNrfwP3YvqKXmm4zUBEXrB7ov9gimgK" *)
Theorem In_rec_G_c : forall X:set, forall f:set->set, (forall x :e X, In_rec_G x (f x)) -> In_rec_G X (F X f).
let X:set.
let f:set->set.
assume H1: forall x :e X, In_rec_G x (f x).
prove In_rec_G X (F X f).
let R:set->set->prop.
assume H2: forall X:set, forall f:set->set, (forall x :e X, R x (f x)) -> R X (F X f).
prove R X (F X f).
apply (H2 X f).
prove forall x :e X, R x (f x).
let x:set.
assume H3: x :e X.
prove R x (f x).
exact (H1 x H3 R H2).
Qed.

(* Treasure "1LLpq56MHpnwcy6wLJQRqXrEVddMZABNXG" *)
Theorem In_rec_G_inv : forall X Y:set, In_rec_G X Y -> exists f:set->set, (forall x :e X, In_rec_G x (f x)) /\ Y = F X f.
let X Y.
assume H1: In_rec_G X Y.
set R := (fun X Y:set => exists f:set->set, (forall x :e X, In_rec_G x (f x)) /\ Y = F X f).
apply (H1 R).
prove forall Z:set, forall g:set->set, (forall z :e Z, R z (g z)) -> R Z (F Z g).
let Z g.
assume IH: forall z :e Z, exists f:set->set, (forall x :e z, In_rec_G x (f x)) /\ g z = F z f.
prove exists f:set->set, (forall x :e Z, In_rec_G x (f x)) /\ F Z g = F Z f.
witness g. apply andI.
- let z.
  assume H2: z :e Z.
  apply (exandE (set->set) (fun f => forall x :e z, In_rec_G x (f x)) (fun f => g z = F z f) (IH z H2)).
  let f:set->set.
  assume H3: forall x :e z, In_rec_G x (f x).
  assume H4: g z = F z f.
  prove In_rec_G z (g z).
  rewrite H4.
  prove In_rec_G z (F z f).
  exact (In_rec_G_c z f H3).
- apply (eqI set).
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

(* Treasure "1Ks5TKX5LYFaPquFZB8MRX9crdXSpsYVCm" *)
Theorem In_rec_G_f : forall X Y Z:set, In_rec_G X Y -> In_rec_G X Z -> Y = Z.
apply In_ind.
let X.
assume IH: forall x :e X, forall y z:set, In_rec_G x y -> In_rec_G x z -> y = z.
let Y Z.
assume H1: In_rec_G X Y.
assume H2: In_rec_G X Z.
prove Y = Z.
claim L1: exists f:set->set, (forall x :e X, In_rec_G x (f x)) /\ Y = F X f.
{ exact (In_rec_G_inv X Y H1). }
claim L2: exists f:set->set, (forall x :e X, In_rec_G x (f x)) /\ Z = F X f.
{ exact (In_rec_G_inv X Z H2). }
apply (exandE (set->set) (fun f => forall x :e X, In_rec_G x (f x)) (fun f => Y = F X f) L1).
let g.
assume H3: forall x :e X, In_rec_G x (g x).
assume H4: Y = F X g.
apply (exandE (set->set) (fun f => forall x :e X, In_rec_G x (f x)) (fun f => Z = F X f) L2).
let h.
assume H5: forall x :e X, In_rec_G x (h x).
assume H6: Z = F X h.
prove Y = Z.
rewrite H4.
rewrite H6.
prove F X g = F X h.
apply Fr.
prove forall x :e X, g x = h x.
let x.
assume H7: x :e X.
exact (IH x H7 (g x) (h x) (H3 x H7) (H5 x H7)).
Qed.

(* Treasure "13WKC7qjVNSoBm7TLirmuHmX7SabtXbSLU" *)
Theorem In_rec_G_In_rec : forall X:set, In_rec_G X (In_rec X).
apply In_ind.
let X.
assume IH: forall x :e X, In_rec_G x (In_rec x).
prove In_rec_G X (In_rec X).
prove In_rec_G X (some Y:set, In_rec_G X Y).
apply (EpsR set (In_rec_G X) (F X In_rec)).
prove In_rec_G X (F X In_rec).
exact (In_rec_G_c X In_rec IH).
Qed.

(* Treasure "17hMHufHxE6xKuepcHmttXAGs7NvRmZvbd" *)
Theorem In_rec_G_In_rec_d : forall X:set, In_rec_G X (F X In_rec).
let X R.
assume H1: forall X:set, forall f:set->set, (forall x :e X, R x (f x)) -> R X (F X f).
apply (H1 X In_rec).
let x. assume _.
exact (In_rec_G_In_rec x R H1).
Qed.

(* Treasure "1BmLmqRXkaQo6UbkSBWvpmU6WMDxtgr1D7" *)
Theorem In_rec_eq : forall X:set, In_rec X = F X In_rec.
exact (fun X : set => In_rec_G_f X (In_rec X) (F X In_rec) (In_rec_G_In_rec X) (In_rec_G_In_rec_d X)).
Qed.

End EpsilonRec.
