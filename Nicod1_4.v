Theorem N1_4 : ∀ P Q : Prop,
  P ∨ Q → Q ∨ P.
Proof. intros P Q.
  specialize n2_2 with Q P.
  intros n2_2a.
  specialize Assoc1_5 with P Q P.
  intros Assoc1_5a.
  specialize Sum1_6 with P Q (Q ∨ P).
  intros Sum1_6a.
  MP Sum1_6a n2_2a.
  Syll Sum1_6a Assoc1_5a Sa.
  specialize Taut1_2 with P.
  intros Taut1_2a.
  specialize Sum1_6 with Q (P ∨ P) P.
  intros Sum1_6b.
  MP Sum1_6b Taut1_2a.
  Syll Sa Sum1_6b Sb.
  apply Sb.
Qed.