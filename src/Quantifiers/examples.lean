import Quantifiers.main

universe u

example {α : Type u} (a : α) : α :=
by main

example {α : Type u} (P : α → α → Prop) (h : ∃ x, ∀ y, P x y) : ∃ x, ∀ y, P x y :=
by main

example {α : Type u} (P : α → Prop) (Q : α → Prop) (h₁ : ∃ x, P x)
(h₂ : ∀ x, P x → Q x) : ∃ x, Q x :=
by main

example {α β : Type u} (P : α → α → β → α → Prop) (Q : α → α → β → α → Prop)
(b : β) (h₁ : ∀ x, ∃ y, ∀ z w, P x y z w) (h₂ : ∃ x, ∀ y z w, P x y z w → Q x y z w)
: ∃ x y z, ∀ w, Q x y z w :=
by main
