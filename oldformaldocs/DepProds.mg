(* Title "Dependent Products and Simple Exponents of Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "XWpA6PLSwUwWCTkM" *)

Definition Pi : set -> (set -> set) -> set := fun X Y => {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

(* Treasure "1CyFLj9GKzyX5m4ZBNNJjRmVJoAniWGxxg" *)
Theorem PiI : forall X:set, forall Y:set->set, forall f:set,
    (forall u :e f, pair_p u /\ u 0 :e X) -> (forall x :e X, f x :e Y x) -> f :e Pi_ x :e X, Y x.
let X Y f.
assume H1: forall u :e f, pair_p u /\ u 0 :e X.
assume H2: forall x :e X, f x :e Y x.
prove f :e {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.
apply SepI.
- prove f :e Power (Sigma_ x :e X, Union (Y x)).
  apply PowerI.
  prove f c= Sigma_ x :e X, Union (Y x).
  let z.
  assume Hz: z :e f.
  prove z :e Sigma_ x :e X, Union (Y x).
  apply (H1 z Hz).
  assume H3: pair (z 0) (z 1) = z.
  assume H4: z 0 :e X.
  rewrite <- H3.
  prove pair (z 0) (z 1) :e Sigma_ x :e X, Union (Y x).
  apply pair_Sigma.
  + prove z 0 :e X.
    exact H4.
  + prove z 1 :e Union (Y (z 0)).
    apply (UnionI (Y (z 0)) (z 1) (f (z 0))).
    * prove z 1 :e f (z 0).
      apply apI.
      prove pair (z 0) (z 1) :e f.
      rewrite H3.
      exact Hz.
    * prove f (z 0) :e Y (z 0).
      exact (H2 (z 0) H4).
- prove forall x :e X, f x :e Y x.
  exact H2.
Qed.

(* Treasure "1MWVW1LWpmaezYiuHND1MwP4GfsRtQYFS3" *)
Theorem PiE : forall X:set, forall Y:set->set, forall f:set,
  f :e (Pi_ x :e X, Y x) -> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).
let X Y f.
assume Hf: f :e Pi_ x :e X, Y x.
apply (SepE (Power (Sigma_ x :e X, Union (Y x))) (fun f => forall x :e X, f x :e Y x) f Hf).
assume H1: f :e (Power (Sigma_ x :e X, Union (Y x))).
assume H2: forall x :e X, f x :e Y x.
apply andI.
- prove forall u :e f, pair_p u /\ u 0 :e X.
  let u.
  assume Hu: u :e f.
  claim L1: f c= Sigma_ x :e X, Union (Y x).
  { exact (PowerE (Sigma_ x :e X, Union (Y x)) f H1). }
  claim L2: u :e Sigma_ x :e X, Union (Y x).
  { exact (L1 u Hu). }
  apply andI.
  + prove pair_p u.
    claim L3: pair (proj0 u) (proj1 u) = u.
    { exact (proj_Sigma_eta X (fun x => Union (Y x)) u L2). }
    rewrite <- L3.
    prove pair_p (pair (proj0 u) (proj1 u)).
    exact (pair_p_I (proj0 u) (proj1 u)).
  + prove u 0 :e X.
    exact (ap0_Sigma X (fun x => Union (Y x)) u L2).
- prove forall x :e X, f x :e Y x.
  exact H2.
Qed.

(* Treasure "16GG3US1cu3JCZQX598CDn5kB1hgxtCGRj" *)
Theorem PiEq : forall X:set, forall Y:set->set, forall f:set,
    f :e Pi X Y <-> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).
let X Y f. apply iffI.
- exact (PiE X Y f).
- assume H1.
  apply H1.
  assume H2: forall u :e f, pair_p u /\ u 0 :e X.
  assume H3: forall x :e X, f x :e Y x.
  exact (PiI X Y f H2 H3).
Qed.

(* Treasure "15smqbgD2gjsgq8oykTDFzhDKcgFaV77th" *)
Theorem lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
let X Y F.
assume H1: forall x :e X, F x :e Y x.
prove (fun x :e X => F x) :e (Pi_ x :e X, Y x).
apply PiI.
- prove forall u :e (fun x :e X => F x), pair_p u /\ u 0 :e X.
  let u.
  assume Hu: u :e fun x :e X => F x.
  claim L1: exists x :e X, exists y :e F x, u = pair x y.
  {
    exact (lamE X F u Hu).
  }
  apply (exandE set (fun x => x :e X) (fun x => exists y :e F x, u = pair x y) L1).
  let x.
  assume Hx: x :e X.
  assume H2: exists y :e F x, u = pair x y.
  apply (exandE set (fun y => y :e F x) (fun y => u = pair x y) H2).
  let y.
  assume Hy: y :e F x.
  assume H3: u = pair x y.
  apply andI.
  + prove pair_p u.
    rewrite H3.
    apply pair_p_I.
  + prove u 0 :e X.
    rewrite H3.
    prove pair x y 0 :e X.
    rewrite pair_ap_0.
    prove x :e X.
    exact Hx.
- prove forall x :e X, (fun x :e X => F x) x :e Y x.
  let x.
  assume Hx: x :e X.
  rewrite (beta X F x Hx).
  prove F x :e Y x.
  exact (H1 x Hx).
Qed.

(* Treasure "1BbQREWDNwbQCN4GPFyUifXfRqKZn7kJFq" *)
Theorem ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.
let X Y f x.
assume Hf: f :e Pi_ x :e X, Y x.
exact (SepE2 (Power (Sigma_ x :e X, Union (Y x))) (fun f => forall x :e X, f x :e Y x) f Hf x).
Qed.

(* Treasure "185KM6BhBNtqoCBKFBZyVhNwtjVXNUaaro" *)
Lemma Pi_ext_Subq : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x c= g x) -> f c= g.
let X Y f.
assume Hf: f :e Pi_ x :e X, Y x.
let g.
assume Hg: g :e Pi_ x :e X, Y x.
assume H1: forall x :e X, f x c= g x.
apply (PiE X Y f Hf).
assume Hf1: forall u :e f, pair_p u /\ u 0 :e X.
assume Hf2: forall x :e X, f x :e Y x.
apply (PiE X Y g Hg).
assume Hg1: forall u :e g, pair_p u /\ u 0 :e X.
assume Hg2: forall x :e X, g x :e Y x.
let u.
assume Hu: u :e f.
prove u :e g.
apply (Hf1 u Hu).
assume H2: pair (u 0) (u 1) = u.
assume H3: u 0 :e X.
rewrite <- H2.
prove pair (u 0) (u 1) :e g.
apply apE.
prove u 1 :e g (u 0).
apply (H1 (u 0) H3).
prove u 1 :e f (u 0).
apply apI.
prove pair (u 0) (u 1) :e f.
rewrite H2.
prove u :e f.
exact Hu.
Qed.

(* Treasure "1JMpnur9pDsmXjtm9Qv1ab6Dg5GaFV6UXU" *)
Theorem Pi_ext : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x = g x) -> f = g.
let X Y f.
assume Hf: f :e Pi_ x :e X, Y x.
let g.
assume Hg: g :e Pi_ x :e X, Y x.
assume H1: forall x :e X, f x = g x.
prove f = g.
apply set_ext.
- prove f c= g.
  apply (Pi_ext_Subq X Y f Hf g Hg).
  let x.
  assume Hx : x :e X.
  prove f x c= g x.
  rewrite (H1 x Hx).
  prove g x c= g x.
  exact (Subq_ref (g x)).
- prove g c= f.
  apply (Pi_ext_Subq X Y g Hg f Hf).
  let x.
  assume Hx : x :e X.
  prove g x c= f x.
  rewrite (H1 x Hx).
  prove g x c= g x.
  exact (Subq_ref (g x)).
Qed.

(* Treasure "1GdtKh8FRQgvg5wPh5JkfWUVHJdKCkokjj" *)
Theorem Pi_eta : forall X:set, forall Y:set -> set, forall f:set, f :e (Pi_ x :e X, Y x) -> (fun x :e X => f x) = f.
let X Y f.
assume Hf: f :e Pi_ x :e X, Y x.
claim L1: (fun x :e X => f x) :e Pi_ x :e X, Y x.
{
  apply lam_Pi.
  let x.
  assume Hx : x :e X.
  prove f x :e Y x.
  exact (ap_Pi X Y f x Hf Hx).
}
apply (Pi_ext X Y (fun x :e X => f x) L1 f Hf).
prove forall x :e X, (fun x :e X => f x) x = f x.
let x.
assume Hx : x :e X.
prove (fun x :e X => f x) x = f x.
exact (beta X (ap f) x Hx).
Qed.

(* Treasure "15YJSz1VXP9uNqrpsYv3rVbaFKRW6Gk4TF" *)
Theorem Pi_Power_1 : forall X:set, forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Pi_ x :e X, Y x) :e Power 1.
let X Y.
assume H1: forall x :e X, Y x :e Power 1.
prove (Pi_ x :e X, Y x) :e Power 1.
apply PowerI.
prove (Pi_ x :e X, Y x) c= 1.
let f.
assume Hf: f :e Pi_ x :e X, Y x.
prove f :e 1.
claim L1: f = 0.
{
  apply Empty_eq.
  let z.
  assume H2: z :e f.
  apply (PiE X Y f Hf).
  assume H3: forall u :e f, pair_p u /\ u 0 :e X.
  assume H4: forall x :e X, f x :e Y x.
  apply (H3 z H2).
  assume H5: pair (z 0) (z 1) = z.
  assume H6: z 0 :e X.
  claim L1a: f (z 0) :e Y (z 0).
  { exact (H4 (z 0) H6). }
  claim L1b: Y (z 0) :e Power 1.
  { exact (H1 (z 0) H6). }
  claim L1c: f (z 0) :e 1.
  { exact (PowerE 1 (Y (z 0)) L1b (f (z 0)) L1a). }
  claim L1d: f (z 0) :e {0}.
  {
    exact (Subq_1_Sing0 (f (z 0)) L1c).
  }
  claim L1e: f (z 0) = 0.
  { exact (SingE 0 (f (z 0)) L1d). }
  claim L1f: z 1 :e f (z 0).
  {
    apply apI.
    prove pair (z 0) (z 1) :e f.
    rewrite H5.
    exact H2.
  }
  claim L1g: z 1 :e 0.
  {
    rewrite <- L1e at 2.
    exact L1f.
  }
  exact (EmptyE (z 1) L1g).
}
rewrite L1.
exact In_0_1.
Qed.

(* Treasure "1AuBPUwRzLCGV8TMZyRFiqbcXhAyGYXKVN" *)
Theorem Pi_0_dom_mon : forall X Y:set, forall A:set->set, X c= Y -> (forall y :e Y, y /:e X -> 0 :e A y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, A y.
let X Y A.
assume H1: X c= Y.
assume H2: forall y :e Y, y /:e X -> 0 :e A y.
let f.
assume Hf: f :e Pi_ x :e X, A x.
prove f :e Pi_ y :e Y, A y.
apply (PiE X A f Hf).
assume Hf1: forall u :e f, pair_p u /\ u 0 :e X.
assume Hf2: forall x :e X, f x :e A x.
apply (PiI Y A f).
- prove forall u :e f, pair_p u /\ u 0 :e Y.
  let u.
  assume Hu: u :e f.
  apply (Hf1 u Hu).
  assume H3: pair_p u.
  assume H4: u 0 :e X.
  apply andI.
  + prove pair_p u. exact H3.
  + prove u 0 :e Y. exact (H1 (u 0) H4).
- prove forall y :e Y, f y :e A y.
  let y.
  assume Hy: y :e Y.
  prove f y :e A y.
  apply (classic (y :e X)).
  + assume H3: y :e X.
    exact (Hf2 y H3).
  + assume H3: y /:e X.
    prove f y :e A y.
    claim L1: f y = 0.
    {
      rewrite <- (Pi_eta X A f Hf).
      prove (fun x :e X => f x) y = 0.
      exact (beta0 X (ap f) y H3).
    }
    rewrite L1.
    prove 0 :e A y.
    exact (H2 y Hy H3).
Qed.

(* Treasure "1H7DJB5fLajknRMWJ8ALFT3MRwVFFbL1jE" *)
Theorem Pi_cod_mon : forall X:set, forall A B:set->set, (forall x :e X, A x c= B x) -> (Pi_ x :e X, A x) c= Pi_ x :e X, B x.
let X A B.
assume H1: forall x :e X, A x c= B x.
prove (Pi_ x :e X, A x) c= Pi_ x :e X, B x.
let f.
assume Hf: f :e Pi_ x :e X, A x.
prove f :e Pi_ x :e X, B x.
apply (PiE X A f Hf).
assume Hf1: forall u :e f, pair_p u /\ u 0 :e X.
assume Hf2: forall x :e X, f x :e A x.
apply (PiI X B f).
- prove forall u :e f, pair_p u /\ u 0 :e X.
  exact Hf1.
- prove forall x :e X, f x :e B x.
  let x.
  assume Hx: x :e X.
  prove f x :e B x.
  apply (H1 x Hx).
  prove f x :e A x.
  exact (Hf2 x Hx).
Qed.

(* Treasure "13MnagyDLem6kzxiz9pcfu7iwJ9QK3wExE" *)
Theorem Pi_0_mon : forall X Y:set, forall A B:set->set,
 (forall x :e X, A x c= B x) -> X c= Y -> (forall y :e Y, y /:e X -> 0 :e B y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, B y.
let X Y A B.
assume H1: forall x :e X, A x c= B x.
assume H2: X c= Y.
assume H3: forall y :e Y, y /:e X -> 0 :e B y.
apply (Subq_tra (Pi_ x :e X, A x) (Pi_ x :e X, B x) (Pi_ y :e Y, B y)).
- prove (Pi_ x :e X, A x) c= (Pi_ x :e X, B x).
  exact (Pi_cod_mon X A B H1).
- prove (Pi_ x :e X, B x) c= (Pi_ y :e Y, B y).
  exact (Pi_0_dom_mon X Y B H2 H3).
Qed.

Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

(* Treasure "13t4yswZYreuT8mKX7tVwGnWJGe3HjuN8b" *)
Theorem setexp_2_eq : forall X:set, X :*: X = X :^: 2.
let X. apply set_ext.
- let z.
  assume Hz: z :e X :*: X.
  apply (and3E (pair (proj0 z) (proj1 z) = z) (proj0 z :e X) (proj1 z :e X) (Sigma_eta_proj0_proj1 X (fun _ => X) z Hz)).
  assume H1: pair (proj0 z) (proj1 z) = z.
  assume H2: proj0 z :e X.
  assume H3: proj1 z :e X.
  rewrite <- H1.
  prove pair (proj0 z) (proj1 z) :e X :^: 2.
  prove pair (proj0 z) (proj1 z) :e Pi_ i :e 2, X.
  rewrite (tuple_pair (proj0 z) (proj1 z)).
  prove (proj0 z,proj1 z) :e Pi_ i :e 2, X.
  prove (fun i :e 2 => if i = 0 then proj0 z else proj1 z) :e Pi_ i :e 2, X.
  apply lam_Pi.
  let i.
  assume Hi: i :e 2.
  prove (if i = 0 then proj0 z else proj1 z) :e X.
  apply (If_or set (i=0) (proj0 z) (proj1 z)).
  + assume H4: (if i = 0 then proj0 z else proj1 z) = proj0 z.
    rewrite H4.
    exact H2.
  + assume H4: (if i = 0 then proj0 z else proj1 z) = proj1 z.
    rewrite H4.
    exact H3.
- let f.
  assume Hf: f :e X :^: 2.
  prove f :e X :*: X.
  apply (PiE 2 (fun _ => X) f Hf).
  assume H1: forall u :e f, pair_p u /\ u 0 :e 2.
  assume H2: forall x :e 2, f x :e X.
  claim L1: pair (f 0) (f 1) = f.
  {
    prove pair_p f.
    apply pair_p_I2.
    prove forall u :e f, pair_p u /\ u 0 :e 2.
    exact H1.
  }
  rewrite <- L1.
  prove pair (f 0) (f 1) :e X :*: X.
  prove pair (f 0) (f 1) :e Sigma_ x :e X, X.
  apply pair_Sigma.
  + prove f 0 :e X.
    apply H2.
    prove 0 :e 2.
    exact In_0_2.
  + prove f 1 :e X.
    apply H2.
    prove 1 :e 2.
    exact In_1_2.
Qed.

(* Treasure "1CXQUfrxo5kk5mCad1Cx1waFaJXrTGDLcY" *)
Theorem setexp_0_dom_mon : forall A:set, 0 :e A -> forall X Y:set, X c= Y -> A :^: X c= A :^: Y.
let A.
assume H1: 0 :e A.
let X Y.
assume H2: X c= Y.
apply (Pi_0_dom_mon X Y (fun _ => A) H2).
let y.
assume _ _.
exact H1.
Qed.

(* Treasure "135GGUm7uHEMa1PNey1rDWBzMH8Qv6UruA" *)
Theorem setexp_0_mon : forall X Y A B:set, 0 :e B -> A c= B -> X c= Y -> A :^: X c= B :^: Y.
let X Y A B.
assume H1: 0 :e B.
assume H2: A c= B.
assume H3: X c= Y.
apply (Pi_0_mon X Y (fun _ => A) (fun _ => B)).
- prove forall x :e X, A c= B. exact (fun x _ => H2).
- prove X c= Y. exact H3.
- prove forall y :e Y, y /:e X -> 0 :e B. exact (fun y _ _ => H1).
Qed.

(* Treasure "1739JriiCvRubArJrH2Ev2hDSJWuZ5Ejrv" *)
Theorem nat_in_setexp_mon : forall A:set, 0 :e A -> forall n, nat_p n -> forall m :e n, A :^: m c= A :^: n.
let A.
assume H1: 0 :e A.
let n.
assume Hn: nat_p n.
let m.
assume Hm: m :e n.
apply (setexp_0_dom_mon A H1 m n).
prove m c= n.
exact (nat_trans n Hn m Hm).
Qed.
