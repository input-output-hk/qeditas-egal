(* Title "Arithmetic on the Natural Numbers" *)
(* Author "Chad E. Brown" *)

(* Salt "2BWsDi2E2j3aMh1yK" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
End Poly1_eq.
Infix = 502 := eq.
Section Poly1_eqthms.
Variable A : SType.
Axiom eqI : forall x : A , x = x.
Axiom eq_sym : forall x y : A , x = y -> y = x.
End Poly1_eqthms.
Section Choice.
Variable A : SType.
Parameter Eps : (A -> prop) -> A.
End Choice.
Binder some , := Eps.
Axiom classic : forall P : prop , P \/ ~ P.
Section IfA.
Variable A : SType.
Definition If : prop -> A -> A -> A := (fun p x y => some z : A , p /\ z = x \/ ~ p /\ z = y).
Notation IfThenElse If.
Axiom If_0 : forall p : prop , forall x y : A , ~ p -> (if p then x else y) = y.
Axiom If_1 : forall p : prop , forall x y : A , p -> (if p then x else y) = x.
End IfA.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
(* Unicode Empty "2205" *)
Parameter Empty : set.
Axiom EmptyE : forall x : set , x /:e Empty.
(* Unicode Union "22C3" *)
Parameter Union : set -> set.
(* Parameter In_rec MK74iPEyb2n2boTzfPvwdtg5EW5kMbn6cAH6g2Bpcyn2bpow *)
Parameter In_rec : (set -> (set -> set) -> set) -> set -> set.
Axiom In_rec_eq : forall F : set -> (set -> set) -> set , (forall X : set , forall g h : set -> set , (forall x , x :e X -> g x = h x) -> F X g = F X h) -> forall X : set , In_rec F X = F X (In_rec F).
(* Parameter ordsucc MJAVHZ4UTjfNkP94R1Y274wA1jSL4zvYwwczio73KbaM1Zkf *)
Parameter ordsucc : set -> set.
Axiom ordsuccI2 : forall x : set , x :e ordsucc x.
Axiom ordsuccE : forall x y : set , y :e ordsucc x -> y :e x \/ y = x.
Notation Nat Empty ordsucc.
Definition nat_p : set -> prop := fun n : set => forall p : set -> prop , p 0 -> (forall x : set , p x -> p (ordsucc x)) -> p n.
Axiom nat_0 : nat_p 0.
Axiom nat_ordsucc : forall n : set , nat_p n -> nat_p (ordsucc n).
Axiom nat_ind : forall p : set -> prop , p 0 -> (forall n , nat_p n -> p n -> p (ordsucc n)) -> forall n , nat_p n -> p n.
Axiom Union_ordsucc_eq : forall n , nat_p n -> Union (ordsucc n) = n.

(** Main Body **)

Section NatRec.

Variable z:set.
Variable f:set->set->set.
Let F : set->(set->set)->set := fun n g => if Union n :e n then f (Union n) (g (Union n)) else z.

Definition nat_primrec : set->set := In_rec F.

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

Theorem nat_primrec_0 : nat_primrec 0 = z.
prove (In_rec F 0 = z).
rewrite (In_rec_eq F nat_primrec_r).
prove F 0 (In_rec F) = z.
prove (if Union 0 :e 0 then f (Union 0) (In_rec F (Union 0)) else z) = z.
exact (If_0 set (Union 0 :e 0) (f (Union 0) (In_rec F (Union 0))) z (EmptyE (Union 0))).
Qed.

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

Theorem add_nat_0R : forall n:set, n + 0 = n.
exact (fun n => nat_primrec_0 n (fun _ r => ordsucc r)).
Qed.

Theorem add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
exact (fun n m Hm => nat_primrec_S n (fun _ r => ordsucc r) m Hm).
Qed.

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

Theorem mul_nat_0R : forall n:set, n * 0 = 0.
exact (fun n => nat_primrec_0 0 (fun _ r => n + r)).
Qed.

Theorem mul_nat_SR : forall n m:set, nat_p m -> n * ordsucc m = n + n * m.
exact (fun n m Hm => nat_primrec_S 0 (fun _ r => n + r) m Hm).
Qed.

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

Example add_nat_1_1_2 : 1 + 1 = 2.
prove 1 + ordsucc 0 = 2.
rewrite (add_nat_SR 1 0 nat_0).
prove ordsucc (1 + 0) = 2.
rewrite (add_nat_0R 1).
prove ordsucc 1 = 2.
exact (eqI set 2).
Qed.

End NatArith.
