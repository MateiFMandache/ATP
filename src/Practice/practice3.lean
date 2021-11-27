/-
The aim here is to write a solver that can handle ∨ and ∧ in both hypotheses and goals.
This requires dealing with multiple goals. -/

meta def tactic.interactive.main_tactic : tactic unit := sorry

example (P Q R : Prop) (h : (P ∨ Q) ∧ (P ∨ R)) : (P ∨ Q ∧ R) :=
by sorry