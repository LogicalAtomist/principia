Import No1.
Import No2.
Import No3.
Import No4.
Import No5. 

 Theorem n3_47 : ∀ P Q R S : Prop,
 ((P → R) ∧ (Q → S)) → (P ∧ Q) → R ∧ S.
Proof. intros P Q R S.
 specialize Simp3_26 with (P→R) (Q→S).
 intros Simp3_26a. (*Yuelin's book has n2_34. This doesn't exist.*)
 specialize Fact3_45 with P R Q.
 intros Fact3_45a. (*Yuelin's book has n2_45. Fact3_45 is meant.*)
 replace (R∧Q) with (Q∧R) in Fact3_45a.
 Syll Simp3_26a Fact3_45a Sa. (*Syll2_05*)
 specialize Simp3_27 with (P→R) (Q→S).
 intros Simp3_27a. (*Yuelin's book has n2_36. This doesn't exist.*)
 specialize Fact3_45 with Q S R.
 intros Fact3_45b. (*Yuelin's book has n2_45. Fact3_45 is meant.*)
 replace (S∧R) with (R∧S) in Fact3_45b.
 Syll Simp3_27a Fact3_45b Sb. (*Syll2_05*)
 clear Simp3_26a. clear Fact3_45a. 
   clear Simp3_27a. clear Fact3_45b.
 Conj Sa Sb.
 split.
 apply Sa.
 apply Sb.
 specialize Comp3_43 with ((P→R)∧(Q→S)) ((P∧Q)→(Q∧R)) ((Q∧R)→(R∧S)).
 intros Comp3_43a. (*Yuelin's book has n2_39. Comp3_43 is meant. PM and I have n2_83 here.*)
 MP Comp3_43a H.
 specialize Syll3_33 with (P∧Q) (Q∧R) (R∧S).
 intros Syll3_33a. (*Yuelin's book has n2_39. Syll3_33 is meant. My n2_83 does this work, too.*)
 Syll Comp3_43a Syll3_33a Sc. (*Yuelin seems to do another application of Syll3_33, citing the same number n2_39. But that would also require here, as above, Conjunction, which Yuelin does not bother citing.*)
 apply Sc.
 apply EqBi.
 apply n4_3.
 apply EqBi.
 apply n4_3.
Qed.