(* Title "Socrates Introductory Example" *)
(* Author "Chad E. Brown" *)

(* Salt "Some Random Salt" *)

Section Socrates.

Variable A:SType.
Variable Man:A->prop.
Variable Mortal:A->prop.
Hypothesis ManMortal: forall x:A, Man x -> Mortal x.
Variable Socrates:A.
Hypothesis SocratesMan: Man Socrates.
(* Treasure "1F7k7QuUzjoERGbQLr6T3Y3ZeZdxzamHWu" *)
Theorem SocratesMortal: Mortal Socrates.
exact ManMortal Socrates SocratesMan.
Qed.

End Socrates.

(* Salt "Some Other Random Salt" *)

(**
 All elephants are pink.
 Nellie is an elephant, therefore Nellie is pink.
 - Destiny of the Daleks (Doctor Who, 1979)
 **)
Section Nellie.

Variable A:SType.
Variable Elephant:A->prop.
Variable Pink:A->prop.
Hypothesis ElephantsPink: forall x:A, Elephant x -> Pink x.
Variable Nellie:A.
Hypothesis NellieElephant: Elephant Nellie.
(* Treasure "15wcUqiRHwb5t17iw6Lpafzm2iFhccRWwS" *)
Theorem NelliePink: Pink Nellie.
exact ElephantsPink Nellie NellieElephant.
Qed.

End Nellie.

Section NellieWithApply.

Variable A:SType.
Variable Elephant:A->prop.
Variable Pink:A->prop.
Hypothesis ElephantsPink: forall x:A, Elephant x -> Pink x.
Variable Nellie:A.
Hypothesis NellieElephant: Elephant Nellie.
(* Treasure "15wcUqiRHwb5t17iw6Lpafzm2iFhccRWwS" *)
Theorem NelliePink2: Pink Nellie.
apply ElephantsPink.
prove Elephant Nellie.
exact NellieElephant.
Qed.

End NellieWithApply.

Section NellieWithApplyAndAssume.

Variable A:SType.
Variable Elephant:A->prop.
Variable Pink:A->prop.
Hypothesis ElephantsPink: forall x:A, Elephant x -> Pink x.
Variable Nellie:A.
(* Treasure "15wcUqiRHwb5t17iw6Lpafzm2iFhccRWwS" *)
Theorem NelliePink3: Elephant Nellie -> Pink Nellie.
assume H: Elephant Nellie.
apply ElephantsPink.
prove Elephant Nellie.
exact H.
Qed.

End NellieWithApplyAndAssume.

Section NellieWithApplyAssumeAndLet.

Variable A:SType.
Variable Elephant:A->prop.
Variable Pink:A->prop.
Hypothesis ElephantsPink: forall x:A, Elephant x -> Pink x.
(* Treasure "15wcUqiRHwb5t17iw6Lpafzm2iFhccRWwS" *)
Theorem NelliePink4: forall n:A, Elephant n -> Pink n.
let n.
assume H: Elephant n.
apply ElephantsPink.
prove Elephant n.
exact H.
Qed.

(* Treasure "17irP55rL1WFyRtXy22BfpVhG6edW1syW1" *)
Theorem NelliePink5: forall n:A, Elephant n -> Pink n.
exact ElephantsPink.
Qed.

End NellieWithApplyAssumeAndLet.
