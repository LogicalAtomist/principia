Require Import Unicode.Utf8.

Module No1.
Import Unicode.Utf8.
  (*We first give the axioms of Principia
for the propositional calculus in *1.*)

Axiom MP1_1 : ∀  P Q : Prop,
  (P → Q) → P → Q. (*Modus ponens*)

  (**1.11 ommitted: it is MP for propositions containing variables. Likewise, ommitted the well-formedness rules 1.7, 1.71, 1.72*)

Axiom Taut1_2 : ∀ P : Prop, P ∨ P→ P. (*Tautology*)

Axiom Add1_3 : ∀ P Q : Prop, Q → P ∨ Q. (*Addition*)

Axiom Perm1_4 : ∀ P Q : Prop, P ∨ Q → Q ∨ P. (*Permutation*)

Axiom Assoc1_5 : ∀ P Q R : Prop, P ∨ (Q ∨ R) → Q ∨ (P ∨ R).

Axiom Sum1_6: ∀ P Q R : Prop, (Q → R) → (P ∨ Q → P ∨ R).
  (*These are all the propositional axioms of Principia Mathematica.*)

Axiom Impl1_01 : ∀ P Q : Prop, (P → Q) = (~P ∨ Q).
    (*This is a definition in Principia: there → is a defined sign and ∨, ~ are primitive ones. The purposes of giving this as an Axiom are two: first, to allow for the use of definitions in proofs, and second, to circumvent Coq's definitions of these primitive notions in Coq.*)

End No1.