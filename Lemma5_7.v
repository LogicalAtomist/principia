Theorem L5_7 : ∀ P Q R S : Prop,
  ((P↔Q) ∧ (R↔S)) → ((P↔R) → (Q↔S)).
Proof.  intros P Q R S.
  specialize n4_22 with Q P R.
  intros n4_22a.
  specialize n4_22 with Q R S.
  intros n4_22b.
  specialize Exp3_3 with (Q↔R) (R↔S) (Q↔S).
  intros Exp3_3a.
  MP Exp3_3a n4_22b.
  Syll n4_22a Exp3_3a Sa.
  replace (Q↔P) with (P↔Q) in Sa.
  specialize Imp3_31 with ((P↔Q)∧(P↔R)) (R↔S) (Q↔S).
  intros Imp3_31a.
  MP Imp3_31a Sa.
  replace (((P ↔ Q) ∧ (P ↔ R)) ∧ (R ↔ S)) with 
    ((P ↔ Q) ∧((P ↔ R) ∧ (R ↔ S))) in Imp3_31a.
  replace ((P ↔ R) ∧ (R ↔ S)) with 
    ((R ↔ S) ∧ (P ↔ R)) in Imp3_31a.
  replace ((P ↔ Q) ∧ (R ↔ S) ∧ (P ↔ R)) with 
    (((P ↔ Q) ∧ (R ↔ S)) ∧ (P ↔ R)) in Imp3_31a.
  specialize Exp3_3 with ((P ↔ Q) ∧ (R ↔ S)) (P↔R) (Q↔S).
  intros Exp3_3b.
  MP Exp3_3b Imp3_31a.
  apply Exp3_3b.
  apply EqBi.
  apply n4_32. (*With (P ↔ Q) (R ↔ S) (P ↔ R)*)
  apply EqBi. 
  apply n4_3. (*With (R ↔ S) (P ↔ R)*)
  replace ((P ↔ Q) ∧((P ↔ R) ∧ (R ↔ S))) with 
    (((P ↔ Q) ∧ (P ↔ R)) ∧ (R ↔ S)).
  reflexivity.
  apply EqBi.
  specialize n4_32 with (P↔Q) (P↔R) (R↔S).
  intros n4_32a.
  apply n4_32a.
  apply EqBi.
  apply n4_21. (*With P Q*)
Qed.