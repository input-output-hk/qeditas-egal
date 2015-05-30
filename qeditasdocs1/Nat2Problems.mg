(* Title "Arithmetic on the Natural Numbers" *)
(* Author "Chad E. Brown" *)

(* Salt "2BWsDi2E2j3aMh1yK" *)

Section NatRec.

Variable z:set.
Variable f:set->set->set.
Let F : set->(set->set)->set := fun n g => if Union n :e n then f (Union n) (g (Union n)) else z.

Definition nat_primrec : set->set := In_rec F.

Theorem nat_primrec_r : forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.
Admitted.

Theorem nat_primrec_0 : nat_primrec 0 = z.
Admitted.

Theorem nat_primrec_S : forall n:set, nat_p n -> nat_primrec (ordsucc n) = f n (nat_primrec n).
Admitted.

End NatRec.

Section NatArith.

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.

Infix + 360 right := add_nat.

Theorem add_nat_0R : forall n:set, n + 0 = n.
Admitted.

Theorem add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
Admitted.

Theorem add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).
Admitted.

Theorem add_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n+m)+k = n+(m+k).
Admitted.

Theorem add_nat_0L : forall m:set, nat_p m -> 0+m = m.
Admitted.

Theorem add_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n + m = ordsucc (n+m).
Admitted.

Theorem add_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n + m = m + n.
Admitted.

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.

Infix * 355 right := mul_nat.

Theorem mul_nat_0R : forall n:set, n * 0 = 0.
Admitted.

Theorem mul_nat_SR : forall n m:set, nat_p m -> n * ordsucc m = n + n * m.
Admitted.

Theorem mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).
Admitted.

Theorem mul_nat_0L : forall m:set, nat_p m -> 0 * m = 0.
Admitted.

Theorem mul_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n * m = n * m + m.
Admitted.

Theorem mul_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n * m = m * n.
Admitted.

Theorem mul_add_nat_distrL : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> n * (m + k) = n * m + n * k.
Admitted.

Theorem mul_add_nat_distrR : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n + m) * k = n * k + m * k.
Admitted.

Theorem mul_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n*m)*k = n*(m*k).
Admitted.

Example add_nat_1_1_2 : 1 + 1 = 2.
Admitted.

End NatArith.
