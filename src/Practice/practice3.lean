/-
The aim here is to write a solver that can handle ∨ and ∧ in both hypotheses and goals.
This requires dealing with multiple goals. -/

open tactic
open list
open expr

meta def and_and_or : list expr → list expr → expr → tactic unit
-- first argument is list of hypotheses yet to be processed
-- second argument is target
| (cons h t) (cons `(%%a ∨ %%b) u) e :=
  seq'
    (do ex ← to_expr ``(or.elim %%h),
    apply ex >> skip)
    (do nm ← get_unused_name `h,
    h' ← intro nm,
    tp ← infer_type h',
    and_and_or (cons h' t) (cons tp u) e)
| (cons h t) (cons `(%%a ∧ %%b) u) e :=
do nm₁ ← get_unused_name `h,
  nm₂ ← get_unused_name `h,
  ea ← to_expr ``(and.left %%h),
  eb ← to_expr ``(and.right %%h),
  ha ← assertv nm₁ a ea,
  hb ← assertv nm₂ b eb,
  clear h,
  and_and_or
    (cons ha (cons hb t))
    (cons a (cons b u))
    e
| (cons _ t) (cons _ u) e := and_and_or t u e
| nil (cons _ t) _ := fail "Unsynchronized lists as arguments to and_and_or"
| (cons _ t) nil _ := fail "Unsynchronized lists as arguments to and_and_or"
| nil nil `(%%a ∨ %%b) :=
  (applyc ``or.inl >> and_and_or nil nil a) <|>
  (applyc ``or.inr >> and_and_or nil nil b)
| nil nil `(%%a ∧ %%b) :=
  seq' (applyc ``and.intro) (target >>= and_and_or nil nil)
| nil nil _ := assumption

meta def tactic.interactive.main_tactic : tactic unit :=
do t ← target,
  l ← local_context,
  tps ← l.mmap infer_type,
  and_and_or l tps t

example (P Q R : Prop) (h₁ : P) (h₂ : Q ∧ R): (P ∧ Q ∧ R) :=
by main_tactic

example (P Q R : Prop) (h : Q ∧ R) : (P ∨ Q ∨ R) :=
by main_tactic

example (P Q R : Prop) (h : (P ∨ Q) ∧ (P ∨ R)) : (P ∨ Q ∧ R) :=
by main_tactic

example (P Q R : Prop) (h : (P ∨ Q) ∧ (P ∨ R) ∧ (Q ∨ R)) :
  (P ∧ Q) ∨ (P ∧ R) ∨ (Q ∧ R) :=
by main_tactic