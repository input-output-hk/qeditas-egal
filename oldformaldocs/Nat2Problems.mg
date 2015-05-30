(* Title "Arithmetic on the Natural Numbers" *)
(* Author "Chad E. Brown" *)

(* Salt "2BWsDi2E2j3aMh1yK" *)

Section NatRec.

Variable z:set.
Variable f:set->set->set.
Let F : set->(set->set)->set := fun n g => if Union n :e n then f (Union n) (g (Union n)) else z.

Definition nat_primrec : set->set := In_rec F.

(* Treasure "1BDTQ6pWdmMzK54W44LsdGPanDGAwBqScv" *)
Theorem nat_primrec_r : forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.
Admitted.

(* Treasure "16xLExnuQKgiSWLUsqQsZ4dt1GyYDch6g8" *)
Theorem nat_primrec_0 : nat_primrec 0 = z.
Admitted.

(* Treasure "1JQAuTTtDNYRAqWjU3EHUeYnZqcxco5GSW" *)
Theorem nat_primrec_S : forall n:set, nat_p n -> nat_primrec (ordsucc n) = f n (nat_primrec n).
Admitted.

End NatRec.

Section NatArith.

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.

Infix + 360 right := add_nat.

(* Treasure "16HmVFCq3f88XAWLs57XQdmmonhBwN93nY" *)
Theorem add_nat_0R : forall n:set, n + 0 = n.
Admitted.

(* Treasure "12p8S9qDszxuXdA7qAKybKL9QQfWGV48de" *)
Theorem add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
Admitted.

(* Treasure "1PTpGgU8mp68EG9HJpK8MWjXE1TTFJLQEw" *)
Theorem add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).
Admitted.

(* Treasure "1KQTFmEXJvNHYe8JLdy1GnmY6kvkiEZtch" *)
Theorem add_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n+m)+k = n+(m+k).
Admitted.

(* Treasure "175YG7ZSYyzoJ116PFsTToMZatC7dLz3vk" *)
Theorem add_nat_0L : forall m:set, nat_p m -> 0+m = m.
Admitted.

(* Treasure "16nizVRPBByLDEGx54BKxscfw28fU2HVwJ" *)
Theorem add_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n + m = ordsucc (n+m).
Admitted.

(* Treasure "1oEo4HZN8GTeMNton3Hf9VQxDiMnVEH58" *)
Theorem add_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n + m = m + n.
Admitted.

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.

Infix * 355 right := mul_nat.

(* Treasure "1Nz6koHjrnTqd9mr8xptCYqnqHsPNAEahp" *)
Theorem mul_nat_0R : forall n:set, n * 0 = 0.
Admitted.

(* Treasure "1HY8MvQvraJ1YASXvDF9erppTUrDM5e1w6" *)
Theorem mul_nat_SR : forall n m:set, nat_p m -> n * ordsucc m = n + n * m.
Admitted.

(* Treasure "1ECqg2YJGWzEpD6TRU2kHBK69mZYRscCAz" *)
Theorem mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).
Admitted.

(* Treasure "1MtN3aLBq2TGt7CDeToth4aNH5Ext3yTht" *)
Theorem mul_nat_0L : forall m:set, nat_p m -> 0 * m = 0.
Admitted.

(* Treasure "18xr3Edfxyn6Ms2mx8rperMeDSjNqUdeqb" *)
Theorem mul_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n * m = n * m + m.
Admitted.

(* Treasure "1LVpRo88348f6V3jrsiBaLcr5wA7rV56hC" *)
Theorem mul_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n * m = m * n.
Admitted.

(* Treasure "18rZgojN8BkZciQuEjTee6spNnPWXiEzCu" *)
Theorem mul_add_nat_distrL : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> n * (m + k) = n * m + n * k.
Admitted.

(* Treasure "1DUTD5qvSY1Hz2YAvMws7D3mmA4BcdvBuA" *)
Theorem mul_add_nat_distrR : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n + m) * k = n * k + m * k.
Admitted.

(* Treasure "1A8fw8fJRgijJz9Qcn83L3C3rzdzd2EnGH" *)
Theorem mul_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n*m)*k = n*(m*k).
Admitted.

(* Treasure "1789Q3XRsNGc4aoo5BCLAhptVdo8CrJus2" *)
Example add_nat_1_1_2 : 1 + 1 = 2.
Admitted.

End NatArith.
