import Quantifiers.directory

meta def tactic.interactive.print_directory : tactic unit :=
do (dir, _) ← create_directory,
  trace_directory dir

universe u
example {α : Type u} (P : α → Prop) (a : α) (h : P a) : ∃ x, P x :=
begin
  print_directory,
  exact ⟨a, h⟩
end
