(* Title "Dependent Products and Simple Exponents of Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "XWpA6PLSwUwWCTkM" *)

Definition Pi : set -> (set -> set) -> set := fun X Y => {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

(* Treasure "1CyFLj9GKzyX5m4ZBNNJjRmVJoAniWGxxg" *)
Theorem PiI : forall X:set, forall Y:set->set, forall f:set,
    (forall u :e f, pair_p u /\ u 0 :e X) -> (forall x :e X, f x :e Y x) -> f :e Pi_ x :e X, Y x.
Admitted.

(* Treasure "1MWVW1LWpmaezYiuHND1MwP4GfsRtQYFS3" *)
Theorem PiE : forall X:set, forall Y:set->set, forall f:set,
  f :e (Pi_ x :e X, Y x) -> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).
Admitted.

(* Treasure "16GG3US1cu3JCZQX598CDn5kB1hgxtCGRj" *)
Theorem PiEq : forall X:set, forall Y:set->set, forall f:set,
    f :e Pi X Y <-> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).
Admitted.

(* Treasure "15smqbgD2gjsgq8oykTDFzhDKcgFaV77th" *)
Theorem lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
Admitted.

(* Treasure "1BbQREWDNwbQCN4GPFyUifXfRqKZn7kJFq" *)
Theorem ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.
Admitted.

(* Treasure "185KM6BhBNtqoCBKFBZyVhNwtjVXNUaaro" *)
Lemma Pi_ext_Subq : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x c= g x) -> f c= g.
Admitted.

(* Treasure "1JMpnur9pDsmXjtm9Qv1ab6Dg5GaFV6UXU" *)
Theorem Pi_ext : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x = g x) -> f = g.
Admitted.

(* Treasure "1GdtKh8FRQgvg5wPh5JkfWUVHJdKCkokjj" *)
Theorem Pi_eta : forall X:set, forall Y:set -> set, forall f:set, f :e (Pi_ x :e X, Y x) -> (fun x :e X => f x) = f.
Admitted.

(* Treasure "15YJSz1VXP9uNqrpsYv3rVbaFKRW6Gk4TF" *)
Theorem Pi_Power_1 : forall X:set, forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Pi_ x :e X, Y x) :e Power 1.
Admitted.

(* Treasure "1AuBPUwRzLCGV8TMZyRFiqbcXhAyGYXKVN" *)
Theorem Pi_0_dom_mon : forall X Y:set, forall A:set->set, X c= Y -> (forall y :e Y, y /:e X -> 0 :e A y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, A y.
Admitted.

(* Treasure "1H7DJB5fLajknRMWJ8ALFT3MRwVFFbL1jE" *)
Theorem Pi_cod_mon : forall X:set, forall A B:set->set, (forall x :e X, A x c= B x) -> (Pi_ x :e X, A x) c= Pi_ x :e X, B x.
Admitted.

(* Treasure "13MnagyDLem6kzxiz9pcfu7iwJ9QK3wExE" *)
Theorem Pi_0_mon : forall X Y:set, forall A B:set->set,
 (forall x :e X, A x c= B x) -> X c= Y -> (forall y :e Y, y /:e X -> 0 :e B y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, B y.
Admitted.

Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

(* Treasure "13t4yswZYreuT8mKX7tVwGnWJGe3HjuN8b" *)
Theorem setexp_2_eq : forall X:set, X :*: X = X :^: 2.
Admitted.

(* Treasure "1CXQUfrxo5kk5mCad1Cx1waFaJXrTGDLcY" *)
Theorem setexp_0_dom_mon : forall A:set, 0 :e A -> forall X Y:set, X c= Y -> A :^: X c= A :^: Y.
Admitted.

(* Treasure "135GGUm7uHEMa1PNey1rDWBzMH8Qv6UruA" *)
Theorem setexp_0_mon : forall X Y A B:set, 0 :e B -> A c= B -> X c= Y -> A :^: X c= B :^: Y.
Admitted.

(* Treasure "1739JriiCvRubArJrH2Ev2hDSJWuZ5Ejrv" *)
Theorem nat_in_setexp_mon : forall A:set, 0 :e A -> forall n, nat_p n -> forall m :e n, A :^: m c= A :^: n.
Admitted.
