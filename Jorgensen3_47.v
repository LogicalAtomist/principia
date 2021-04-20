Theorem n3_47a : ∀ P Q R S : Prop,
  ((P → R) ∧ (Q → S)) → (P ∧ Q) → R ∧ S.
Proof. intros P Q R S.
  specialize Simp3_26 with (P→R) (Q→S).
  intros Simp3_26a.
  specialize Fact3_45 with P R Q.
  intros Fact3_45a.
  Syll Fact3_45a Simp3_26a Sa.
  specialize n3_22 with R Q.
  intros n3_22a.
  specialize Syll2_05 with (P∧Q) (R∧Q) (Q∧R).
  intros Syll2_05a. (*Not cited by Jorgensen*)
  MP Syl2_05a n3_22a.
  Syll Sa Syll2_05a Sb.
  specialize Simp3_27 with (P→R) (Q→S).
  intros Simp3_27a.
  specialize Fact3_45 with Q S R.
  intros Fact3_45b.
  Syll Simp3_26a Fact3_45b Sc.
  specialize n3_22 with S R.
  intros n3_22b.
  specialize Syll2_05 with (Q∧R) (S∧R) (R∧S).
  intros Syll2_05b. (*Not cited by Jorgensen*)
  MP Syl2_05b n3_22b.
  Syll Sc Syll2_05a Sd.
  specialize n2_83 with ((P→R)∧(Q→S)) (P∧Q) (Q∧R) (R∧S).
  intros n2_83a. (*This with MP works, but it omits Conj3_03.*)
  MP n2_83a Sb.
  MP n2_83a Sd.
  apply n2_83a.
Qed.