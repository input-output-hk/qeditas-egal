(* Title "Quotients" *)
(* Author "Chad E. Brown" *)

(* Salt "2GxJfmdu1bwYzhNYg" *)

Section QuotientsPoly1.

Variable A:SType.

Definition canonical_elt : (A->A->prop)->A->A := fun R:A->A->prop => fun x:A => some y:A, R x y.

(* Treasure "19YiGHyyqB1tw9LUmWdp2NATD3Q28ZaWzD" *)
Theorem canonical_elt_rel : forall R:A->A->prop, forall x:A, R x x -> R x (canonical_elt R x).
exact (fun R x H => EpsR A (R x) x H).
Qed.

(* Treasure "1BQT8hfMVpgthxGNvQd9igsb2NwbTbDUkH" *)
Theorem canonical_elt_eq : forall R:A->A->prop, per A R -> forall x y:A, R x y -> canonical_elt R x = canonical_elt R y.
let R.
assume H1: per A R.
let x y.
assume H2: R x y.
claim E: R x = R y.
{
  apply (pred_ext A).
  - let z. assume H3: R x z. prove R y z. exact (per_stra1 A R H1 y x z H2 H3).
  - let z. assume H3: R y z. prove R x z. exact (per_tra A R H1 x y z H2 H3).
}
prove (some z:A, R x z) = (some z:A, R y z).
rewrite <- E.
apply (eqI A).
Qed.

(* Treasure "1PB8DKmASftrzSvcvJBogwpAehT29ocxEg" *)
Theorem canonical_elt_idem : forall R:A->A->prop, per A R -> forall x:A, R x x -> canonical_elt R x = canonical_elt R (canonical_elt R x).
let R.
assume H1: per A R.
let x.
assume H2: R x x.
prove canonical_elt R x = canonical_elt R (canonical_elt R x).
apply (canonical_elt_eq R H1 x (canonical_elt R x)).
prove R x (canonical_elt R x).
exact (canonical_elt_rel R x H2).
Qed.

Definition quotient : (A->A->prop)->A->prop := fun R:A->A->prop => fun x:A => R x x /\ x = canonical_elt R x.

(* Treasure "18ijZZ39Axynz6VVivHtWaa1kdRrarhwDk" *)
Theorem quotient_prop1 : forall R:A->A->prop,
 forall x:A, quotient R x -> R x x.
exact (fun R x H => andEL (R x x) (x = canonical_elt R x) H).
Qed.

(* Treasure "18sCZnfBmbtN9eRCgU9STe3fQysLedSwMQ" *)
Theorem quotient_prop2 : forall R:A->A->prop, per A R ->
 forall x y:A, quotient R x -> quotient R y -> R x y -> x = y.
let R.
assume H1: per A R.
let x y.
assume H2: R x x /\ x = canonical_elt R x.
assume H3: R y y /\ y = canonical_elt R y.
assume H4: R x y.
rewrite (andER (R x x) (x = canonical_elt R x) H2).
rewrite (andER (R y y) (y = canonical_elt R y) H3).
exact (canonical_elt_eq R H1 x y H4).
Qed.

Definition canonical_elt_def : (A->A->prop)->(A->A)->A->A := fun R:A->A->prop => fun d:A->A => fun x:A => if (R x (d x)) then (d x) else (canonical_elt R x).

(* Treasure "13ZzNKXj5Sguz1da95FFZzGpqPjyS52nHM" *)
Theorem canonical_elt_def_rel : forall R:A->A->prop, forall d:A->A, forall x:A, R x x -> R x (canonical_elt_def R d x).
let R d x.
assume H1:R x x.
prove R x (if R x (d x) then d x else canonical_elt R x).
apply (If_correct A (R x (d x)) (d x) (canonical_elt R x)).
- assume H2: R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = d x.
  apply H2.
  assume H3: R x (d x).
  assume H4: (if R x (d x) then d x else canonical_elt R x) = d x.
  rewrite H4. exact H3.
- assume H2: ~R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = canonical_elt R x.
  rewrite (andER (~R x (d x)) ((if R x (d x) then d x else canonical_elt R x) = canonical_elt R x) H2).
  prove R x (canonical_elt R x).
  exact (canonical_elt_rel R x H1).
Qed.

(* Treasure "1HdG5LcTh6GYX7W6RGYzqprQQVostCdr3B" *)
Theorem canonical_elt_def_eq :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x y:A, R x y -> canonical_elt_def R d x = canonical_elt_def R d y.
let R.
assume H1: per A R.
let d.
assume H2: forall x y:A, R x y -> d x = d y.
let x y.
assume H3: R x y.
apply (If_correct A (R x (d x)) (d x) (canonical_elt R x)).
- assume Hx1: R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = d x.
  apply Hx1.
  assume Hx2: R x (d x).
  assume Hx3: (if R x (d x) then d x else canonical_elt R x) = d x.
  prove ((if (R x (d x)) then (d x) else (canonical_elt R x)) = canonical_elt_def R d y).
  rewrite Hx3.
  prove (d x = canonical_elt_def R d y).
  prove (d x = (if (R y (d y)) then (d y) else (canonical_elt R y))).
  claim L1: R y (d y).
  {
    rewrite <- (H2 x y H3).
    prove R y (d x).
    exact (per_stra1 A R H1 y x (d x) H3 Hx2).
  }
  rewrite (If_1 A (R y (d y)) (d y) (canonical_elt R y) L1).
  prove d x = d y.
  exact (H2 x y H3).
- assume Hx1: ~R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = canonical_elt R x.
  apply Hx1.
  assume Hx2: ~R x (d x).
  assume Hx3: (if R x (d x) then d x else canonical_elt R x) = canonical_elt R x.
  prove (if (R x (d x)) then (d x) else (canonical_elt R x)) = canonical_elt_def R d y.
  rewrite Hx3.
  prove canonical_elt R x = canonical_elt_def R d y.
  prove canonical_elt R x = if (R y (d y)) then (d y) else (canonical_elt R y).
  claim L1: ~R y (d y).
  {
    rewrite <- (H2 x y H3).
    assume Hy1: R y (d x).
    apply Hx2.
    exact (per_tra A R H1 x y (d x) H3 Hy1).
  }
  rewrite (If_0 A (R y (d y)) (d y) (canonical_elt R y) L1).
  prove canonical_elt R x = canonical_elt R y.
  exact (canonical_elt_eq R H1 x y H3).
Qed.

(* Treasure "1E2K6nwut2U3vkkRcJrWUmdoPVffeHuBbN" *)
Theorem canonical_elt_def_idem :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x:A, R x x -> canonical_elt_def R d x = canonical_elt_def R d (canonical_elt_def R d x).
let R.
assume H1: per A R.
let d.
assume H2: forall x y:A, R x y -> d x = d y.
let x.
assume H3: R x x.
apply (canonical_elt_def_eq R H1 d H2 x (canonical_elt_def R d x)).
prove R x (canonical_elt_def R d x).
apply canonical_elt_def_rel.
exact H3.
Qed.

Definition quotient_def : (A->A->prop)->(A->A)->A->prop := fun R:A->A->prop => fun d:A->A => fun x:A => R x x /\ x = canonical_elt_def R d x.

(* Treasure "189qz5rBsPqq8V77qkJTvXoi5v8UgBxebM" *)
Theorem quotient_def_prop0 :
 forall R:A->A->prop, per A R ->
 forall d:A->A,
 forall x:A, R x (d x) -> x = d x -> quotient_def R d x.
let R.
assume H1: per A R.
let d.
let x.
assume H2: R x (d x).
assume H3: x = d x.
prove R x x /\ x = canonical_elt_def R d x.
apply andI.
- exact (per_ref1 A R H1 x (d x) H2).
- prove x = if (R x (d x)) then (d x) else (canonical_elt R x).
  rewrite (If_1 A (R x (d x)) (d x) (canonical_elt R x) H2).
  prove x = d x.
  exact H3.
Qed.

(* Treasure "18xn7tJtqg96SigoSQ6XWvzvYFnZUVnnfk" *)
Theorem quotient_def_prop1 :
 forall R:A->A->prop,
 forall d:A->A,
 forall x:A, quotient_def R d x -> R x x.
let R d x.
assume H2: R x x /\ x = canonical_elt_def R d x.
prove R x x.
exact (andEL (R x x) (x = canonical_elt_def R d x) H2).
Qed.

(* Treasure "19C1iX5kfJZXiM3cYH5p3E2EstCPXogBgw" *)
Theorem quotient_def_prop2 :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x y:A, quotient_def R d x -> quotient_def R d y -> R x y -> x = y.
let R.
assume H1: per A R.
let d.
assume H2: forall x y:A, R x y -> d x = d y.
let x y.
assume Hx1: R x x /\ x = canonical_elt_def R d x.
assume Hy1: R y y /\ y = canonical_elt_def R d y.
assume H3: R x y.
rewrite (andER (R x x) (x = canonical_elt_def R d x) Hx1).
rewrite (andER (R y y) (y = canonical_elt_def R d y) Hy1).
prove canonical_elt_def R d x = canonical_elt_def R d y.
exact (canonical_elt_def_eq R H1 d H2 x y H3).
Qed.

End QuotientsPoly1.
