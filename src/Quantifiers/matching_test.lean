import Quantifiers.matching

universe u

open tactic

example {α : Type u} (a : α) : α :=
by do (dir, goals) ← create_directory,
  mi ← create_match_info dir goals,
  trace_match_info mi, -- the important line

  ta ← get_local `a,
  exact ta

example {α : Type u} (P : α → Prop) (Q : α → Prop) (h₁ : ∃ x, P x)
(h₂ : ∀ x, P x → Q x) : ∃ x, Q x :=
by do (dir, goals) ← create_directory,
  mi ← create_match_info dir goals,
  trace_match_info mi, -- the important line

  t₁ ← get_local `h₁,
  nmx ← get_unused_name `x,
  nmh ← get_unused_name `h,
  cases t₁ [nmx, nmh],
  x ← get_local nmx,
  h ← get_local nmh,
  applyc ``exists.intro,
  t₂ ← get_local `h₂,
  apply t₂,
  exact h
