(* Title "Epsilon Induction and Recursion" *)
(* Author "Chad E. Brown" *)

(* Salt "Qq1NZYja5FAbneLf" *)

Axiom In_ind : forall P:set->prop, (forall X:set, (forall x:set, x :e X -> P x) -> P X) -> forall X:set, P X.

(* Treasure "17rERvaEEtqDHMGyCeadvZ6QdEm9jMNzu9" *)
Theorem In_irref : forall x, x /:e x.
Admitted.

(* Treasure "1P6aDY1LRV7SmESmjNnQFXPPAYPmNUpdPx" *)
Theorem In_no2cycle : forall x y, x :e y -> y /:e x.
Admitted.

(* Treasure "1H6u2twi6i5QmSzJWvZbHKskY3Yhu16Z99" *)
Theorem Regularity : forall X x:set, x :e X -> exists Y:set, Y :e X /\ ~exists z:set, z :e X /\ z :e Y.
Admitted.

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
Admitted.

(* Treasure "1LLpq56MHpnwcy6wLJQRqXrEVddMZABNXG" *)
Theorem In_rec_G_inv : forall X Y:set, In_rec_G X Y -> exists f:set->set, (forall x :e X, In_rec_G x (f x)) /\ Y = F X f.
Admitted.

Hypothesis Fr:forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

(* Treasure "1Ks5TKX5LYFaPquFZB8MRX9crdXSpsYVCm" *)
Theorem In_rec_G_f : forall X Y Z:set, In_rec_G X Y -> In_rec_G X Z -> Y = Z.
Admitted.

(* Treasure "13WKC7qjVNSoBm7TLirmuHmX7SabtXbSLU" *)
Theorem In_rec_G_In_rec : forall X:set, In_rec_G X (In_rec X).
Admitted.

(* Treasure "17hMHufHxE6xKuepcHmttXAGs7NvRmZvbd" *)
Theorem In_rec_G_In_rec_d : forall X:set, In_rec_G X (F X In_rec).
Admitted.

(* Treasure "1BmLmqRXkaQo6UbkSBWvpmU6WMDxtgr1D7" *)
Theorem In_rec_eq : forall X:set, In_rec X = F X In_rec.
Admitted.

End EpsilonRec.
