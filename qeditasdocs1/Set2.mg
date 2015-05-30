(* Title "Basic Set Operations" *)
(* Author "Chad E. Brown" *)

(* Salt "cpsZu1tVzsnNo79P" *)

Require "353ECBA7EFDC4F9D84E83D1C07C032B98147CEBE". (** for Qeditas **)

Theorem binunion_asso:forall X Y Z:set, X :\/: (Y :\/: Z) = (X :\/: Y) :\/: Z.
let X Y Z. apply set_ext.
- let w. assume H1: w :e X :\/: (Y :\/: Z).
  prove w :e (X :\/: Y) :\/: Z.
  apply (binunionE X (Y :\/: Z) w H1).
  + assume H2: w :e X.
    apply binunionI1. apply binunionI1. exact H2.
  + assume H2: w :e Y :\/: Z.
    apply (binunionE Y Z w H2).
    * assume H3: w :e Y.
      apply binunionI1. apply binunionI2. exact H3.
    * assume H3: w :e Z.
      apply binunionI2. exact H3.
- let w. assume H1: w :e (X :\/: Y) :\/: Z.
  prove w :e X :\/: (Y :\/: Z).
  apply (binunionE (X :\/: Y) Z w H1).
  + assume H2: w :e X :\/: Y.
    apply (binunionE X Y w H2).
    * assume H3: w :e X.
      apply binunionI1. exact H3.
    * assume H3: w :e Y.
      apply binunionI2. apply binunionI1. exact H3.
  + assume H2: w :e Z.
    apply binunionI2. apply binunionI2. exact H2.
Qed.

Lemma binunion_com_Subq:forall X Y:set, X :\/: Y c= Y :\/: X.
let X Y w. assume H1: w :e X :\/: Y.
prove w :e Y :\/: X.
apply (binunionE X Y w H1).
- assume H2: w :e X. apply binunionI2. exact H2.
- assume H2: w :e Y. apply binunionI1. exact H2.
Qed.

Theorem binunion_com:forall X Y:set, X :\/: Y = Y :\/: X.
let X Y. apply set_ext.
- exact (binunion_com_Subq X Y).
- exact (binunion_com_Subq Y X).
Qed.

Theorem binunion_idl:forall X:set, Empty :\/: X = X.
let X. apply set_ext.
- let x. assume H1: x :e Empty :\/: X.
  apply (binunionE Empty X x H1).
  + assume H2: x :e Empty. prove False. exact (EmptyE x H2).
  + assume H2: x :e X. exact H2.
- let x. assume H2: x :e X. prove x :e Empty :\/: X. apply binunionI2. exact H2.
Qed.

Theorem binunion_idr:forall X:set, X :\/: Empty = X.
let X.
rewrite (binunion_com X Empty).
exact (binunion_idl X).
Qed.

Theorem binunion_idem:forall X:set, X :\/: X = X.
let X. apply set_ext.
- let x. assume H1: x :e X :\/: X.
  apply (binunionE X X x H1).
  + assume H2: x :e X. exact H2.
  + assume H2: x :e X. exact H2.
- let x. assume H1: x :e X. apply binunionI1. exact H1.
Qed.

Theorem binunion_Subq_1: forall X Y:set, X c= X :\/: Y.
exact binunionI1.
Qed.

Theorem binunion_Subq_2: forall X Y:set, Y c= X :\/: Y.
exact binunionI2.
Qed.

Theorem binunion_Subq_min: forall X Y Z:set, X c= Z -> Y c= Z -> X :\/: Y c= Z.
let X Y Z.
assume H1: X c= Z.
assume H2: Y c= Z.
let w.
assume H3: w :e X :\/: Y.
apply (binunionE X Y w H3).
- assume H4: w :e X. exact (H1 w H4).
- assume H4: w :e Y. exact (H2 w H4).
Qed.

Theorem Subq_binunion_eq:forall X Y, (X c= Y) = (X :\/: Y = Y).
let X Y. apply prop_ext2.
- assume H1: X c= Y.
  prove X :\/: Y = Y.
  apply set_ext.
  + prove X :\/: Y c= Y. apply (binunion_Subq_min X Y Y).
    * prove X c= Y. exact H1.
    * prove Y c= Y. exact (Subq_ref Y).
  + prove Y c= X :\/: Y. exact (binunion_Subq_2 X Y).
- assume H1: X :\/: Y = Y.
  prove X c= Y.
  rewrite <- H1.
  prove X c= X :\/: Y.
  exact (binunion_Subq_1 X Y).
Qed.

Theorem binunion_nIn_I : forall X Y z:set, z /:e X -> z /:e Y -> z /:e X :\/: Y.
let X Y z.
assume H1: z /:e X.
assume H2: z /:e Y.
assume H3: z :e X :\/: Y.
exact (binunionE X Y z H3 False H1 H2).
Qed.

Theorem binunion_nIn_E : forall X Y z:set, z /:e X :\/: Y -> z /:e X /\ z /:e Y.
let X Y z.
assume H1: z /:e X :\/: Y.
prove z /:e X /\ z /:e Y.
apply andI.
- prove z /:e X.
  assume H2: z :e X.
  apply H1.
  prove z :e X :\/: Y.
  exact (binunionI1 X Y z H2).
- prove z /:e Y.
  assume H2: z :e Y.
  apply H1.
  prove z :e X :\/: Y.
  exact (binunionI2 X Y z H2).
Qed.

Definition binintersect:set->set->set
:= fun X Y => {x :e X |x :e Y}.

(* Unicode :/\: "2229" *)
Infix :/\: 340 left := binintersect.

Theorem binintersectI:forall X Y z, z :e X -> z :e Y -> z :e X :/\: Y.
exact (fun X Y z H1 H2 => SepI X (fun x:set => x :e Y) z H1 H2).
Qed.

Theorem binintersectE:forall X Y z, z :e X :/\: Y -> z :e X /\ z :e Y.
exact (fun X Y z H1 => SepE X (fun x:set => x :e Y) z H1).
Qed.

Theorem binintersectE1:forall X Y z, z :e X :/\: Y -> z :e X.
exact (fun X Y z H1 => SepE1 X (fun x:set => x :e Y) z H1).
Qed.

Theorem binintersectE2:forall X Y z, z :e X :/\: Y -> z :e Y.
exact (fun X Y z H1 => SepE2 X (fun x:set => x :e Y) z H1).
Qed.

Theorem binintersect_Subq_1:forall X Y:set, X :/\: Y c= X.
exact binintersectE1.
Qed.

Theorem binintersect_Subq_2:forall X Y:set, X :/\: Y c= Y.
exact binintersectE2.
Qed.

Theorem binintersect_Subq_max:forall X Y Z:set, Z c= X -> Z c= Y -> Z c= X :/\: Y.
let X Y Z.
assume H1: Z c= X.
assume H2: Z c= Y.
let w.
assume H3: w :e Z.
apply (binintersectI X Y w).
- prove w :e X. exact (H1 w H3).
- prove w :e Y. exact (H2 w H3).
Qed.

Theorem binintersect_asso:forall X Y Z:set, X :/\: (Y :/\: Z) = (X :/\: Y) :/\: Z.
let X Y Z. apply set_ext.
- prove X :/\: (Y :/\: Z) c= (X :/\: Y) :/\: Z.
  apply (binintersect_Subq_max (X :/\: Y) Z (X :/\: (Y :/\: Z))).
  + prove X :/\: (Y :/\: Z) c= X :/\: Y.
    apply (binintersect_Subq_max X Y (X :/\: (Y :/\: Z))).
    * prove X :/\: (Y :/\: Z) c= X. apply binintersect_Subq_1.
    * { prove X :/\: (Y :/\: Z) c= Y. apply (Subq_tra (X :/\: (Y :/\: Z)) (Y :/\: Z) Y).
        - apply binintersect_Subq_2.
        - apply binintersect_Subq_1.
      }
  + prove X :/\: (Y :/\: Z) c= Z. apply (Subq_tra (X :/\: (Y :/\: Z)) (Y :/\: Z) Z).
    * apply binintersect_Subq_2.
    * apply binintersect_Subq_2.
- prove (X :/\: Y) :/\: Z c= X :/\: (Y :/\: Z).
  apply (binintersect_Subq_max X (Y :/\: Z) ((X :/\: Y) :/\: Z)).
  + prove (X :/\: Y) :/\: Z c= X. apply (Subq_tra ((X :/\: Y) :/\: Z) (X :/\: Y) X).
    * apply binintersect_Subq_1.
    * apply binintersect_Subq_1.
  + prove (X :/\: Y) :/\: Z c= Y :/\: Z.
    apply (binintersect_Subq_max Y Z ((X :/\: Y) :/\: Z)).
    * { prove (X :/\: Y) :/\: Z c= Y. apply (Subq_tra ((X :/\: Y) :/\: Z) (X :/\: Y) Y).
        - apply binintersect_Subq_1.
        - apply binintersect_Subq_2.
      }
    * prove (X :/\: Y) :/\: Z c= Z. apply binintersect_Subq_2.
Qed.

Lemma binintersect_com_Subq: forall X Y:set, X :/\: Y c= Y :/\: X.
let X Y. apply (binintersect_Subq_max Y X (X :/\: Y)).
- prove X :/\: Y c= Y. apply binintersect_Subq_2.
- prove X :/\: Y c= X. apply binintersect_Subq_1.
Qed.

Theorem binintersect_com: forall X Y:set, X :/\: Y = Y :/\: X.
let X Y. apply set_ext.
- exact (binintersect_com_Subq X Y).
- exact (binintersect_com_Subq Y X).
Qed.

Theorem binintersect_annil:forall X:set, Empty :/\: X = Empty.
let X. apply Empty_Subq_eq.
prove Empty :/\: X c= Empty. apply binintersect_Subq_1.
Qed.

Theorem binintersect_annir:forall X:set, X :/\: Empty = Empty.
let X.
prove X :/\: Empty = Empty.
rewrite (binintersect_com X Empty).
exact (binintersect_annil X).
Qed.

Theorem binintersect_idem:forall X:set, X :/\: X = X.
let X. apply set_ext.
- prove X :/\: X c= X. apply binintersect_Subq_1.
- prove X c= X :/\: X. apply binintersect_Subq_max.
  + prove X c= X. exact (Subq_ref X).
  + prove X c= X. exact (Subq_ref X).
Qed.

Theorem binintersect_binunion_distr:forall X Y Z:set, X :/\: (Y :\/: Z) = X :/\: Y :\/: X :/\: Z.
let X Y Z. apply set_ext.
- prove X :/\: (Y :\/: Z) c= X :/\: Y :\/: X :/\: Z.
  let w.
  assume H1: w :e X :/\: (Y :\/: Z).
  prove w :e X :/\: Y :\/: X :/\: Z.
  apply (binintersectE X (Y :\/: Z) w H1).
  assume H2: w :e X.
  assume H3: w :e Y :\/: Z.
  apply (binunionE Y Z w H3).
  + assume H4: w :e Y. apply binunionI1. prove w :e X :/\: Y. exact (binintersectI X Y w H2 H4).
  + assume H4: w :e Z. apply binunionI2. prove w :e X :/\: Z. exact (binintersectI X Z w H2 H4).
- prove X :/\: Y :\/: X :/\: Z c= X :/\: (Y :\/: Z).
  apply (binintersect_Subq_max X (Y :\/: Z) (X :/\: Y :\/: X :/\: Z)).
  + prove X :/\: Y :\/: X :/\: Z c= X.
    apply (binunion_Subq_min (X :/\: Y) (X :/\: Z) X).
    * prove X :/\: Y c= X. apply binintersect_Subq_1.
    * prove X :/\: Z c= X. apply binintersect_Subq_1.
  + prove X :/\: Y :\/: X :/\: Z c= Y :\/: Z.
    apply (binunion_Subq_min (X :/\: Y) (X :/\: Z) (Y :\/: Z)).
    * { prove X :/\: Y c= Y :\/: Z. apply (Subq_tra (X :/\: Y) Y (Y :\/: Z)).
        - apply binintersect_Subq_2.
        - apply binunion_Subq_1.
      }
    * { prove X :/\: Z c= Y :\/: Z. apply (Subq_tra (X :/\: Z) Z (Y :\/: Z)).
        - apply binintersect_Subq_2.
        - apply binunion_Subq_2.
      }
Qed.

Theorem binunion_binintersect_distr:forall X Y Z:set, X :\/: Y :/\: Z = (X :\/: Y) :/\: (X :\/: Z).
let X Y Z. apply set_ext.
- prove X :\/: Y :/\: Z c= (X :\/: Y) :/\: (X :\/: Z).
  apply (binintersect_Subq_max (X :\/: Y) (X :\/: Z) (X :\/: Y :/\: Z)).
  + prove X :\/: Y :/\: Z c= X :\/: Y.
    apply (binunion_Subq_min X (Y :/\: Z) (X :\/: Y)).
    * prove X c= X :\/: Y. apply binunion_Subq_1.
    * { prove Y :/\: Z c= X :\/: Y. apply (Subq_tra (Y :/\: Z) Y (X :\/: Y)).
        - prove Y :/\: Z c= Y. apply binintersect_Subq_1.
        - prove Y c= X :\/: Y. apply binunion_Subq_2.
      }
  + prove X :\/: Y :/\: Z c= X :\/: Z.
    apply (binunion_Subq_min X (Y :/\: Z) (X :\/: Z)).
    * prove X c= X :\/: Z. apply binunion_Subq_1.
    * { prove Y :/\: Z c= X :\/: Z. apply (Subq_tra (Y :/\: Z) Z (X :\/: Z)).
        - prove Y :/\: Z c= Z. apply binintersect_Subq_2.
        - prove Z c= X :\/: Z. apply binunion_Subq_2.
      }
- prove (X :\/: Y) :/\: (X :\/: Z) c= X :\/: Y :/\: Z.
  let w.
  assume H1: w :e (X :\/: Y) :/\: (X :\/: Z).
  prove w :e X :\/: Y :/\: Z.
  apply (binintersectE (X :\/: Y) (X :\/: Z) w H1).
  assume H2: w :e X :\/: Y.
  assume H3: w :e X :\/: Z.
  apply (binunionE X Y w H2).
  + apply binunionI1.
  + assume H4: w :e Y.
    apply (binunionE X Z w H3).
    * apply binunionI1.
    * { assume H5: w :e Z. apply binunionI2. apply binintersectI.
        - exact H4.
        - exact H5.
      }
Qed.

Theorem Subq_binintersection_eq:forall X Y:set, (X c= Y) = (X :/\: Y = X).
let X Y. apply prop_ext2.
- assume H1: X c= Y.
  prove X :/\: Y = X.
  apply set_ext.
  + prove X :/\: Y c= X. exact (binintersect_Subq_1 X Y).
  + prove X c= X :/\: Y. apply (binintersect_Subq_max X Y X).
    * exact (Subq_ref X).
    * exact H1.
- assume H1: X :/\: Y = X.
  prove X c= Y.
  rewrite <- H1.
  exact (binintersect_Subq_2 X Y).
Qed.

Theorem binintersect_nIn_I1 : forall X Y z:set, z /:e X -> z /:e X :/\: Y.
let X Y z.
assume H1: z /:e X.
assume H2: z :e X :/\: Y.
exact (H1 (binintersectE1 X Y z H2)).
Qed.

Theorem binintersect_nIn_I2 : forall X Y z:set, z /:e Y -> z /:e X :/\: Y.
let X Y z.
assume H1: z /:e Y.
assume H2: z :e X :/\: Y.
exact (H1 (binintersectE2 X Y z H2)).
Qed.

Theorem binintersect_nIn_E : forall X Y z:set, z /:e X :/\: Y -> z /:e X \/ z /:e Y.
let X Y z.
assume H1: z /:e X :/\: Y.
prove ~(z :e X) \/ ~(z :e Y).
apply not_and_or_demorgan.
prove ~(z :e X /\ z :e Y).
assume H2: z :e X /\ z :e Y.
apply H2.
assume H3: z :e X.
assume H4: z :e Y.
apply H1.
prove z :e X :/\: Y.
exact (binintersectI X Y z H3 H4).
Qed.

Definition setminus:set->set->set
:= fun X Y => Sep X (fun x => x /:e Y).

(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

Theorem setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
exact (fun X Y z H1 H2 => SepI X (fun x:set => x /:e Y) z H1 H2).
Qed.

Theorem setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
exact (fun X Y z H => SepE X (fun x:set => x /:e Y) z H).
Qed.

Theorem setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.
exact (fun X Y z H => SepE1 X (fun x:set => x /:e Y) z H).
Qed.

Theorem setminusE2:forall X Y z, (z :e X :\: Y) -> z /:e Y.
exact (fun X Y z H => SepE2 X (fun x:set => x /:e Y) z H).
Qed.

Theorem setminus_Subq:forall X Y:set, X :\: Y c= X.
exact setminusE1.
Qed.

Theorem setminus_Subq_contra:forall X Y Z:set, Z c= Y -> X :\: Y c= X :\: Z.
let X Y Z.
assume H1: Z c= Y.
let x.
assume H2: x :e X :\: Y.
apply (setminusE X Y x H2).
assume H3: x :e X.
assume H4: x /:e Y.
prove x :e X :\: Z.
apply setminusI.
- exact H3.
- prove x /:e Z. exact (Subq_contra Z Y x H1 H4).
Qed.

Theorem setminus_nIn_I1: forall X Y z, z /:e X -> z /:e X :\: Y.
exact (fun X Y z H1 H2 => H1 (setminusE1 X Y z H2)).
Qed.

Theorem setminus_nIn_I2: forall X Y z, z :e Y -> z /:e X :\: Y.
exact (fun X Y z H1 H2 => setminusE2 X Y z H2 H1).
Qed.

Theorem setminus_nIn_E: forall X Y z, z /:e X :\: Y -> z /:e X \/ z :e Y.
let X Y z.
assume H1: z /:e X :\: Y.
prove ~(z :e X) \/ z :e Y.
prove (fun p q:prop => ~p \/ q) (z :e X) (z :e Y).
rewrite <- eq_imp_or.
prove z :e X -> z :e Y.
assume H2: z :e X.
apply NNPP.
assume H3: z /:e Y.
apply H1.
prove z :e X :\: Y.
apply setminusI.
- exact H2.
- exact H3.
Qed.

Theorem setminus_selfannih:forall X:set, (X :\: X) = Empty.
let X. apply Empty_eq.
let x. assume H: x :e X :\: X. exact (setminusE2 X X x H (setminusE1 X X x H)).
Qed.

Theorem setminus_binintersect:forall X Y Z:set, X :\: Y :/\: Z = (X :\: Y) :\/: (X :\: Z).
let X Y Z. apply set_ext.
- prove X :\: Y :/\: Z c= (X :\: Y) :\/: (X :\: Z).
  let x. assume H1: x :e X :\: Y :/\: Z.
  prove x :e (X :\: Y) :\/: (X :\: Z).
  apply (setminusE X (Y :/\: Z) x H1).
  assume H2: x :e X.
  assume H3: x /:e Y :/\: Z.
  apply NNPP.
  assume H4: x /:e (X :\: Y) :\/: (X :\: Z).
  apply H3.
  prove x :e Y :/\: Z. apply binintersectI.
  + prove x :e Y. apply NNPP. assume H5: x /:e Y. apply H4.
    prove x :e (X :\: Y) :\/: (X :\: Z).
    apply binunionI1.
    prove x :e X :\: Y.
    apply setminusI.
    * exact H2.
    * exact H5.
  + prove x :e Z. apply NNPP. assume H5: x /:e Z. apply H4.
    prove x :e (X :\: Y) :\/: (X :\: Z).
    apply binunionI2.
    prove x :e X :\: Z.
    apply setminusI.
    * exact H2.
    * exact H5.
- prove (X :\: Y) :\/: (X :\: Z) c= X :\: Y :/\: Z.
  apply (binunion_Subq_min (X :\: Y) (X :\: Z) (X :\: Y :/\: Z)).
  + prove (X :\: Y) c= X :\: Y :/\: Z.
    apply setminus_Subq_contra.
    prove Y :/\: Z c= Y.
    apply binintersect_Subq_1.
  + prove (X :\: Z) c= X :\: Y :/\: Z.
    apply setminus_Subq_contra.
    prove Y :/\: Z c= Z.
    apply binintersect_Subq_2.
Qed.

Theorem setminus_binunion:forall X Y Z:set, X :\: Y :\/: Z = (X :\: Y) :\: Z.
let X Y Z. apply set_ext.
- prove X :\: Y :\/: Z c= (X :\: Y) :\: Z.
  let x.
  assume H1: x :e X :\: Y :\/: Z.
  apply (setminusE X (Y :\/: Z) x H1).
  assume H2: x :e X.
  assume H3: x /:e Y :\/: Z.
  apply (binunion_nIn_E Y Z x H3).
  assume H4: x /:e Y.
  assume H5: x /:e Z.
  prove x :e (X :\: Y) :\: Z.
  apply setminusI.
  + prove x :e X :\: Y. apply setminusI.
    * prove x :e X. exact H2.
    * prove x /:e Y. exact H4.
  + prove x /:e Z. exact H5.
- prove (X :\: Y) :\: Z c= X :\: Y :\/: Z.
  let x.
  assume H1: x :e (X :\: Y) :\: Z.
  apply (setminusE (X :\: Y) Z x H1).
  assume H2: x :e X :\: Y.
  assume H3: x /:e Z.
  apply (setminusE X Y x H2).
  assume H4: x :e X.
  assume H5: x /:e Y.
  prove x :e X :\: Y :\/: Z.
  apply setminusI.
  + prove x :e X. exact H4.
  + prove x /:e Y :\/: Z. apply binunion_nIn_I.
    * exact H5.
    * exact H3.
Qed.

Theorem binintersect_setminus:forall X Y Z:set, (X :/\: Y) :\: Z = X :/\: (Y :\: Z).
let X Y Z. apply set_ext.
- prove (X :/\: Y) :\: Z c= X :/\: (Y :\: Z).
  let x.
  assume H1: x :e (X :/\: Y) :\: Z.
  apply (setminusE (X :/\: Y) Z x H1).
  assume H2: x :e X :/\: Y.
  assume H3: x /:e Z.
  apply (binintersectE X Y x H2).
  assume H4: x :e X.
  assume H5: x :e Y.
  prove x :e X :/\: (Y :\: Z).
  apply binintersectI.
  + exact H4.
  + prove x :e Y :\: Z.
    apply setminusI.
    * exact H5.
    * exact H3.
- prove X :/\: (Y :\: Z) c= (X :/\: Y) :\: Z.
  let x.
  assume H1: x :e X :/\: (Y :\: Z).
  apply (binintersectE X (Y :\: Z) x H1).
  assume H2: x :e X.
  assume H3: x :e Y :\: Z.
  apply (setminusE Y Z x H3).
  assume H4: x :e Y.
  assume H5: x /:e Z.
  prove x :e (X :/\: Y) :\: Z.
  apply setminusI.
  + prove x :e X :/\: Y.
    exact (binintersectI X Y x H2 H4).
  + prove x /:e Z.
    exact H5.
Qed.

Theorem binunion_setminus:forall X Y Z:set, X :\/: Y :\: Z = (X :\: Z) :\/: (Y :\: Z).
let X Y Z. apply set_ext.
- prove X :\/: Y :\: Z c= (X :\: Z) :\/: (Y :\: Z).
  let w.
  assume H1: w :e X :\/: Y :\: Z.
  apply (setminusE (X :\/: Y) Z w H1).
  assume H2: w :e X :\/: Y.
  assume H3: w /:e Z.
  prove w :e (X :\: Z) :\/: (Y :\: Z).
  apply (binunionE X Y w H2).
  + assume H4: w :e X.
    apply binunionI1.
    prove w :e X :\: Z.
    exact (setminusI X Z w H4 H3).
  + assume H4: w :e Y.
    apply binunionI2.
    prove w :e Y :\: Z.
    exact (setminusI Y Z w H4 H3).
- prove (X :\: Z) :\/: (Y :\: Z) c= X :\/: Y :\: Z.
  apply (binunion_Subq_min (X :\: Z) (Y :\: Z) (X :\/: Y :\: Z)).
  + prove (X :\: Z) c= X :\/: Y :\: Z.
    let w.
    assume H1: w :e X :\: Z.
    apply (setminusE X Z w H1).
    assume H2: w :e X.
    assume H3: w /:e Z.
    prove w :e X :\/: Y :\: Z.
    apply setminusI.
    * prove w :e X :\/: Y. exact (binunionI1 X Y w H2).
    * prove w /:e Z. exact H3.
  + prove (Y :\: Z) c= X :\/: Y :\: Z.
    let w.
    assume H1: w :e Y :\: Z.
    apply (setminusE Y Z w H1).
    assume H2: w :e Y.
    assume H3: w /:e Z.
    prove w :e X :\/: Y :\: Z.
    apply setminusI.
    * prove w :e X :\/: Y. exact (binunionI2 X Y w H2).
    * prove w /:e Z. exact H3.
Qed.

Theorem setminus_setminus:forall X Y Z:set, X :\: (Y :\: Z) = (X :\: Y) :\/: (X :/\: Z).
let X Y Z. apply set_ext.
- prove X :\: (Y :\: Z) c= (X :\: Y) :\/: (X :/\: Z).
  let w.
  assume H1: w :e X :\: (Y :\: Z).
  apply (setminusE X (Y :\: Z) w H1).
  assume H2: w :e X.
  assume H3: w /:e Y :\: Z.
  apply (setminus_nIn_E Y Z w H3).
  + assume H4: w /:e Y.
    prove w :e (X :\: Y) :\/: (X :/\: Z).
    apply binunionI1.
    exact (setminusI X Y w H2 H4).
  + assume H4: w :e Z.
    prove w :e (X :\: Y) :\/: (X :/\: Z).
    apply binunionI2.
    exact (binintersectI X Z w H2 H4).
- prove (X :\: Y) :\/: (X :/\: Z) c= X :\: (Y :\: Z).
  apply (binunion_Subq_min (X :\: Y) (X :/\: Z) (X :\: (Y :\: Z))).
  + prove X :\: Y c= X :\: (Y :\: Z).
    let w.
    assume H1: w :e X :\: Y.
    apply (setminusE X Y w H1).
    assume H2: w :e X.
    assume H3: w /:e Y.
    prove w :e X :\: (Y :\: Z).
    apply setminusI.
    * exact H2.
    * prove w /:e Y :\: Z.
      apply setminus_nIn_I1.
      prove w /:e Y.
      exact H3.
  + prove X :/\: Z c= X :\: (Y :\: Z).
    let w.
    assume H1: w :e X :/\: Z.
    apply (binintersectE X Z w H1).
    assume H2: w :e X.
    assume H3: w :e Z.
    prove w :e X :\: (Y :\: Z).
    apply setminusI.
    * exact H2.
    * prove w /:e Y :\: Z.
      apply setminus_nIn_I2.
      prove w :e Z.
      exact H3.
Qed.

Theorem setminus_annil:forall X:set, Empty :\: X = Empty.
let X. apply Empty_eq.
let x.
assume H1: x :e Empty :\: X.
exact (EmptyE x (setminusE1 Empty X x H1)).
Qed.

Theorem setminus_idr:forall X:set, X :\: Empty = X.
let X. apply set_ext.
- prove X :\: Empty c= X. exact (setminus_Subq X Empty).
- prove X c= X :\: Empty.
  let x.
  assume H1: x :e X.
  prove x :e X :\: Empty.
  apply setminusI.
  + exact H1.
  + exact (EmptyE x).
Qed.
