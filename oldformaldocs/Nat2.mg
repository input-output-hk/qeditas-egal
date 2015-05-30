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
let X g h.
assume H1: forall x :e X, g x = h x.
prove F X g = F X h.
apply (classic (Union X :e X)).
- assume H2: (Union X :e X).
  prove (if Union X :e X then f (Union X) (g (Union X)) else z) = (if Union X :e X then f (Union X) (h (Union X)) else z).
  rewrite (H1 (Union X) H2).
  prove (if Union X :e X then f (Union X) (h (Union X)) else z) = (if Union X :e X then f (Union X) (h (Union X)) else z).
  apply (eqI set).
- assume H2: (Union X /:e X).
  prove (if Union X :e X then f (Union X) (g (Union X)) else z) = (if Union X :e X then f (Union X) (h (Union X)) else z).
  claim L1: (if Union X :e X then f (Union X) (g (Union X)) else z) = z.
  { exact (If_0 set (Union X :e X) (f (Union X) (g (Union X))) z H2). }
  claim L2: (if Union X :e X then f (Union X) (h (Union X)) else z) = z.
  { exact (If_0 set (Union X :e X) (f (Union X) (h (Union X))) z H2). }
  rewrite L2.
  exact L1.
Qed.

(* Treasure "16xLExnuQKgiSWLUsqQsZ4dt1GyYDch6g8" *)
Theorem nat_primrec_0 : nat_primrec 0 = z.
prove (In_rec F 0 = z).
rewrite (In_rec_eq F nat_primrec_r).
prove F 0 (In_rec F) = z.
prove (if Union 0 :e 0 then f (Union 0) (In_rec F (Union 0)) else z) = z.
exact (If_0 set (Union 0 :e 0) (f (Union 0) (In_rec F (Union 0))) z (EmptyE (Union 0))).
Qed.

(* Treasure "1JQAuTTtDNYRAqWjU3EHUeYnZqcxco5GSW" *)
Theorem nat_primrec_S : forall n:set, nat_p n -> nat_primrec (ordsucc n) = f n (nat_primrec n).
let n.
assume Hn: nat_p n.
prove (In_rec F (ordsucc n) = f n (In_rec F n)).
rewrite (In_rec_eq F nat_primrec_r) at 1.
prove F (ordsucc n) (In_rec F) = f n (In_rec F n).
prove (if Union (ordsucc n) :e ordsucc n then f (Union (ordsucc n)) (In_rec F (Union (ordsucc n))) else z) = f n (In_rec F n).
rewrite (Union_ordsucc_eq n Hn).
prove (if n :e ordsucc n then f n (In_rec F n) else z) = f n (In_rec F n).
exact (If_1 set (n :e ordsucc n) (f n (In_rec F n)) z (ordsuccI2 n)).
Qed.

End NatRec.

Section NatArith.

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.

Infix + 360 right := add_nat.

(* Treasure "16HmVFCq3f88XAWLs57XQdmmonhBwN93nY" *)
Theorem add_nat_0R : forall n:set, n + 0 = n.
exact (fun n => nat_primrec_0 n (fun _ r => ordsucc r)).
Qed.

(* Treasure "12p8S9qDszxuXdA7qAKybKL9QQfWGV48de" *)
Theorem add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
exact (fun n m Hm => nat_primrec_S n (fun _ r => ordsucc r) m Hm).
Qed.

(* Treasure "1PTpGgU8mp68EG9HJpK8MWjXE1TTFJLQEw" *)
Theorem add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).
let n.
assume Hn: nat_p n.
apply nat_ind.
- prove nat_p (n+0).
  rewrite (add_nat_0R n).
  prove nat_p n.
  exact Hn.
- let m.
  assume Hm: nat_p m.
  assume IHm: nat_p (n+m).
  prove nat_p (n + ordsucc m).
  rewrite (add_nat_SR n m Hm).
  prove nat_p (ordsucc (n+m)).
  apply nat_ordsucc.
  prove nat_p (n+m).
  exact IHm.
Qed.

(* Treasure "1KQTFmEXJvNHYe8JLdy1GnmY6kvkiEZtch" *)
Theorem add_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n+m)+k = n+(m+k).
let n. assume Hn: nat_p n.
let m. assume Hm: nat_p m.
apply nat_ind.
- prove (n+m)+0 = n+(m+0).
  rewrite add_nat_0R. rewrite add_nat_0R.
  exact (eqI set (n+m)).
- let k.
  assume Hk: nat_p k.
  assume IHk: (n+m)+k = n+(m+k).
  prove (n + m) + ordsucc k = n + (m + ordsucc k).
  rewrite (add_nat_SR (n+m) k Hk).
  rewrite (add_nat_SR m k Hk).
  prove ordsucc((n+m)+k) = n + ordsucc (m+k).
  rewrite add_nat_SR.
  + prove ordsucc((n+m)+k) = ordsucc(n+(m+k)).
    rewrite IHk.
    exact (eqI set (ordsucc(n+(m+k)))).
  + prove nat_p (m+k).
    exact (add_nat_p m Hm k Hk).
Qed.

(* Treasure "175YG7ZSYyzoJ116PFsTToMZatC7dLz3vk" *)
Theorem add_nat_0L : forall m:set, nat_p m -> 0+m = m.
apply nat_ind.
- prove 0+0 = 0.
  apply add_nat_0R.
- let m.
  assume Hm: nat_p m.
  assume IHm: 0 + m = m.
  prove 0 + ordsucc m = ordsucc m.
  rewrite (add_nat_SR 0 m Hm).
  prove ordsucc (0 + m) = ordsucc m.
  rewrite IHm.
  exact (eqI set (ordsucc m)).
Qed.

(* Treasure "16nizVRPBByLDEGx54BKxscfw28fU2HVwJ" *)
Theorem add_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n + m = ordsucc (n+m).
let n.
assume Hn: nat_p n.
apply nat_ind.
- prove ordsucc n + 0 = ordsucc (n+0).
  rewrite add_nat_0R. rewrite add_nat_0R.
  exact (eqI set (ordsucc n)).
- let m.
  assume Hm: nat_p m.
  assume IHm: ordsucc n + m = ordsucc (n+m).
  prove ordsucc n + ordsucc m = ordsucc (n + ordsucc m).
  rewrite (add_nat_SR (ordsucc n) m Hm).
  prove ordsucc (ordsucc n + m) = ordsucc (n + ordsucc m).
  rewrite (add_nat_SR n m Hm).
  prove ordsucc (ordsucc n + m) = ordsucc (ordsucc (n + m)).
  rewrite IHm.
  exact (eqI set (ordsucc (ordsucc (n+m)))).
Qed.

(* Treasure "1oEo4HZN8GTeMNton3Hf9VQxDiMnVEH58" *)
Theorem add_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n + m = m + n.
let n.
assume Hn: nat_p n.
apply nat_ind.
- prove n + 0 = 0 + n.
  rewrite (add_nat_0L n Hn).
  exact (add_nat_0R n).
- let m.
  assume Hm: nat_p m.
  assume IHm: n+m = m+n.
  prove n + ordsucc m = ordsucc m + n.
  rewrite (add_nat_SL m Hm n Hn).
  prove n + ordsucc m = ordsucc (m + n).
  rewrite <- IHm.
  prove n + ordsucc m = ordsucc (n + m).
  exact (add_nat_SR n m Hm).
Qed.

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.

Infix * 355 right := mul_nat.

(* Treasure "1Nz6koHjrnTqd9mr8xptCYqnqHsPNAEahp" *)
Theorem mul_nat_0R : forall n:set, n * 0 = 0.
exact (fun n => nat_primrec_0 0 (fun _ r => n + r)).
Qed.

(* Treasure "1HY8MvQvraJ1YASXvDF9erppTUrDM5e1w6" *)
Theorem mul_nat_SR : forall n m:set, nat_p m -> n * ordsucc m = n + n * m.
exact (fun n m Hm => nat_primrec_S 0 (fun _ r => n + r) m Hm).
Qed.

(* Treasure "1ECqg2YJGWzEpD6TRU2kHBK69mZYRscCAz" *)
Theorem mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).
let n.
assume Hn: nat_p n.
apply nat_ind.
- prove nat_p (n*0).
  rewrite (mul_nat_0R n).
  prove nat_p 0.
  exact nat_0.
- let m.
  assume Hm: nat_p m.
  assume IHm: nat_p (n*m).
  prove nat_p (n * ordsucc m).
  rewrite (mul_nat_SR n m Hm).
  prove nat_p (n + n*m).
  exact (add_nat_p n Hn (n*m) IHm).
Qed.

(* Treasure "1MtN3aLBq2TGt7CDeToth4aNH5Ext3yTht" *)
Theorem mul_nat_0L : forall m:set, nat_p m -> 0 * m = 0.
apply nat_ind.
- prove 0 * 0 = 0.
  exact (mul_nat_0R 0).
- let m.
  assume Hm: nat_p m.
  assume IHm: 0 * m = 0.
  prove 0 * ordsucc m = 0.
  rewrite (mul_nat_SR 0 m Hm).
  prove 0 + 0 * m = 0.
  rewrite IHm.
  prove 0 + 0 = 0.
  exact (add_nat_0R 0).
Qed.

(* Treasure "18xr3Edfxyn6Ms2mx8rperMeDSjNqUdeqb" *)
Theorem mul_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n * m = n * m + m.
let n.
assume Hn: nat_p n.
apply nat_ind.
- prove ordsucc n * 0 = n * 0 + 0.
  rewrite mul_nat_0R. rewrite mul_nat_0R.
  prove 0 = 0 + 0.
  apply (eq_sym set).
  exact (add_nat_0R 0).
- let m.
  assume Hm: nat_p m.
  assume IHm: ordsucc n * m = n * m + m.
  prove ordsucc n * ordsucc m = n * ordsucc m + ordsucc m.
  rewrite (mul_nat_SR (ordsucc n) m Hm).
  prove ordsucc n + ordsucc n * m = n * ordsucc m + ordsucc m.
  rewrite IHm.
  prove ordsucc n + (n * m + m) = n * ordsucc m + ordsucc m.
  rewrite add_nat_SL.
  + prove ordsucc (n + (n * m + m)) = n * ordsucc m + ordsucc m.
    rewrite (mul_nat_SR n m Hm).
    prove ordsucc (n + (n * m + m)) = (n + n * m) + ordsucc m.
    rewrite (add_nat_SR (n + n * m) m Hm).
    prove ordsucc (n + (n * m + m)) = ordsucc ((n + n * m) + m).
    rewrite add_nat_asso.
    * exact (eqI set (ordsucc (n + (n * m + m)))).
    * exact Hn.
    * exact (mul_nat_p n Hn m Hm).
    * exact Hm.
  + exact Hn.
  + exact (add_nat_p (n*m) (mul_nat_p n Hn m Hm) m Hm).
Qed.

(* Treasure "1LVpRo88348f6V3jrsiBaLcr5wA7rV56hC" *)
Theorem mul_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n * m = m * n.
let n.
assume Hn: nat_p n.
apply nat_ind.
- prove n * 0 = 0 * n.
  rewrite (mul_nat_0L n Hn).
  exact (mul_nat_0R n).
- let m.
  assume Hm: nat_p m.
  assume IHm: n * m = m * n.
  prove n * ordsucc m = ordsucc m * n.
  rewrite (mul_nat_SR n m Hm).
  prove n + n * m = ordsucc m * n.
  rewrite (mul_nat_SL m Hm n Hn).
  prove n + n * m = m * n + n.
  rewrite IHm.
  prove n + m * n = m * n + n.
  exact (add_nat_com n Hn (m*n) (mul_nat_p m Hm n Hn)).
Qed.

(* Treasure "18rZgojN8BkZciQuEjTee6spNnPWXiEzCu" *)
Theorem mul_add_nat_distrL : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> n * (m + k) = n * m + n * k.
let n.
assume Hn: nat_p n.
let m.
assume Hm: nat_p m.
apply nat_ind.
- prove n * (m + 0) = n * m + n * 0.
  rewrite add_nat_0R.
  rewrite mul_nat_0R.
  prove n * m = n * m + 0.
  apply (eq_sym set).
  exact (add_nat_0R (n*m)).
- let k.
  assume Hk: nat_p k.
  assume IHk: n * (m + k) = n * m + n * k.
  prove n * (m + ordsucc k) = n * m + n * ordsucc k.
  rewrite (add_nat_SR m k Hk).
  prove n * ordsucc (m + k) = n * m + n * ordsucc k.
  rewrite (mul_nat_SR n (m+k) (add_nat_p m Hm k Hk)).
  prove n + n * (m + k) = n * m + n * ordsucc k.
  rewrite IHk.
  prove n + (n * m + n * k) = n * m + n * ordsucc k.
  rewrite (mul_nat_SR n k Hk).
  prove n + (n * m + n * k) = n * m + (n + n * k).
  rewrite <- (add_nat_asso n Hn (n*m) (mul_nat_p n Hn m Hm) (n*k) (mul_nat_p n Hn k Hk)).
  prove (n + n * m) + n * k = n * m + (n + n * k).
  rewrite (add_nat_com n Hn (n*m) (mul_nat_p n Hn m Hm)).
  prove (n * m + n) + n * k = n * m + (n + n * k).
  exact (add_nat_asso (n*m) (mul_nat_p n Hn m Hm) n Hn (n*k) (mul_nat_p n Hn k Hk)).
Qed.

(* Treasure "1DUTD5qvSY1Hz2YAvMws7D3mmA4BcdvBuA" *)
Theorem mul_add_nat_distrR : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n + m) * k = n * k + m * k.
let n.
assume Hn: nat_p n.
let m.
assume Hm: nat_p m.
let k.
assume Hk: nat_p k.
prove (n + m) * k = n * k + m * k.
rewrite (mul_nat_com (n+m) (add_nat_p n Hn m Hm) k Hk).
prove k * (n + m) = n * k + m * k.
rewrite (mul_nat_com n Hn k Hk).
prove k * (n + m) = k * n + m * k.
rewrite (mul_nat_com m Hm k Hk).
prove k * (n + m) = k * n + k * m.
exact (mul_add_nat_distrL k Hk n Hn m Hm).
Qed.

(* Treasure "1A8fw8fJRgijJz9Qcn83L3C3rzdzd2EnGH" *)
Theorem mul_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n*m)*k = n*(m*k).
let n.
assume Hn: nat_p n.
let m.
assume Hm: nat_p m.
apply nat_ind.
- prove (n*m)*0=n*(m*0).
  rewrite mul_nat_0R at 2. rewrite mul_nat_0R at 2.
  exact (mul_nat_0R (n*m)).
- let k.
  assume Hk: nat_p k.
  assume IHk: (n*m)*k = n*(m*k).
  prove (n * m) * ordsucc k = n * (m * ordsucc k).
  rewrite mul_nat_SR.
  + prove n * m + (n * m) * k = n * (m * ordsucc k).
    rewrite mul_nat_SR.
    * { prove n * m + (n * m) * k = n * (m + m * k).
        rewrite mul_add_nat_distrL.
        - prove n * m + (n * m) * k = n * m + n * (m * k).
          rewrite IHk.
          exact (eqI set (n * m + n * (m * k))).
        - exact Hn.
        - exact Hm.
        - exact (mul_nat_p m Hm k Hk).
      }
    * exact Hk.
  + exact Hk.
Qed.

(* Treasure "1789Q3XRsNGc4aoo5BCLAhptVdo8CrJus2" *)
Example add_nat_1_1_2 : 1 + 1 = 2.
prove 1 + ordsucc 0 = 2.
rewrite (add_nat_SR 1 0 nat_0).
prove ordsucc (1 + 0) = 2.
rewrite (add_nat_0R 1).
prove ordsucc 1 = 2.
exact (eqI set 2).
Qed.

End NatArith.
