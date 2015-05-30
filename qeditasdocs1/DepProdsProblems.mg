(* Title "Dependent Products and Simple Exponents of Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "XWpA6PLSwUwWCTkM" *)

Definition Pi : set -> (set -> set) -> set := fun X Y => {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Theorem PiI : forall X:set, forall Y:set->set, forall f:set,
    (forall u :e f, pair_p u /\ u 0 :e X) -> (forall x :e X, f x :e Y x) -> f :e Pi_ x :e X, Y x.
Admitted.

Theorem PiE : forall X:set, forall Y:set->set, forall f:set,
  f :e (Pi_ x :e X, Y x) -> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).
Admitted.

Theorem PiEq : forall X:set, forall Y:set->set, forall f:set,
    f :e Pi X Y <-> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).
Admitted.

Theorem lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
Admitted.

Theorem ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.
Admitted.

Lemma Pi_ext_Subq : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x c= g x) -> f c= g.
Admitted.

Theorem Pi_ext : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x = g x) -> f = g.
Admitted.

Theorem Pi_eta : forall X:set, forall Y:set -> set, forall f:set, f :e (Pi_ x :e X, Y x) -> (fun x :e X => f x) = f.
Admitted.

Theorem Pi_Power_1 : forall X:set, forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Pi_ x :e X, Y x) :e Power 1.
Admitted.

Theorem Pi_0_dom_mon : forall X Y:set, forall A:set->set, X c= Y -> (forall y :e Y, y /:e X -> 0 :e A y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, A y.
Admitted.

Theorem Pi_cod_mon : forall X:set, forall A B:set->set, (forall x :e X, A x c= B x) -> (Pi_ x :e X, A x) c= Pi_ x :e X, B x.
Admitted.

Theorem Pi_0_mon : forall X Y:set, forall A B:set->set,
 (forall x :e X, A x c= B x) -> X c= Y -> (forall y :e Y, y /:e X -> 0 :e B y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, B y.
Admitted.

Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

Theorem setexp_2_eq : forall X:set, X :*: X = X :^: 2.
Admitted.

Theorem setexp_0_dom_mon : forall A:set, 0 :e A -> forall X Y:set, X c= Y -> A :^: X c= A :^: Y.
Admitted.

Theorem setexp_0_mon : forall X Y A B:set, 0 :e B -> A c= B -> X c= Y -> A :^: X c= B :^: Y.
Admitted.

Theorem nat_in_setexp_mon : forall A:set, 0 :e A -> forall n, nat_p n -> forall m :e n, A :^: m c= A :^: n.
Admitted.
