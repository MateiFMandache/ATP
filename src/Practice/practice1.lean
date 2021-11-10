/-
The aim is to create a generic tactic that can prove the following theorem:
theorem main {α : Type*} (a : α) (P : α → Prop) (h : P a) : ∃ x, P x
-/

open tactic

meta def conclusion : expr → tactic expr
| `(∃ _, %%t) := conclusion t
| t           := return t

meta def depth : expr → tactic nat
| `(∃ _, %%t) := do t ← depth t, return (t + 1)
| t           := return 0

meta structure match_info : Type :=
(limit : ℕ) (mapping : ℕ → option expr)

meta def merge : match_info → match_info → tactic match_info
| (match_info.mk 0 _)              m                                := return m
| m                                (match_info.mk 0 _)              := return m
| (match_info.mk (nat.succ n₁) f₁) (match_info.mk (nat.succ n₂) f₂) :=
  let n := min n₁ n₂ in
    if (f₁ n = f₂ n ∨ f₁ n = none ∨ f₂ n = none)
      then do m ← merge {limit := n₁, mapping := f₁}
                        {limit := n₂, mapping := f₂},
        return {limit   := m.limit + 1,
                mapping := λ k, if k ≠ n then m.mapping k else
                                if f₁ n ≠ none then f₁ n else f₂ n}
      else failed

meta def match_expr : expr → expr → tactic match_info
| (expr.app a₁ a₂) (expr.app b₁ b₂) :=
  do m₁ ← match_expr a₁ b₁,
     m₂ ← match_expr a₂ b₂,
     merge m₁ m₂
| (expr.var n)          t                     :=
  return {limit := n + 1, mapping := λ m, if m = n then t else none }
| t₁                    t₂                    :=
  if t₁ = t₂ then return {limit := 0, mapping := λ _, none} else failed

meta def find_element_of_type (t : expr) : tactic expr :=
-- searches for an element of given type in the local context.
-- Fails if it can't find one.
do l ← local_context,
  first $ l.map (λ h,
    (infer_type h >>= (unify t) >> return h))

meta def build_term (m : match_info) : ℕ → expr → expr → tactic expr
/- arguments to build_term
  d : ℕ the depth, how many nested ∃ there are
  h : expr the term built so far
  t : expr the type of the term we are trying to build
-/
| 0            h t := return h
| (nat.succ n) h t := do match t with
  | `(Exists %%motive) :=
  do e ← match m.mapping n with
    | (some e) := return e
    | none     := match motive with
      | `(λ _ : %%search_type, _) := find_element_of_type search_type
      | _ := failed end end,
  previous_t ← whnf (expr.app motive e),
  term ← build_term n h previous_t,
  a ← to_expr ```(@Exists.intro _ %%motive %%e %%term),
  return a
  | _ := failed
  end

meta def main_tactic : tactic unit :=
do t ← target,
  c ← conclusion t,
  d ← depth t,
  l ← local_context,
  first $ l.map (λ h,
    do ht ← infer_type h >>= whnf,
    m ← match_expr c ht,
    answer ← (build_term m d h t),
    exact answer)

meta def tactic.interactive.main_tactic : tactic unit := main_tactic

example {α : Type*} (a : α) (P : α → Prop) (h : P a) : ∃ x, P x :=
by main_tactic

example {α : Type*} (a b: α) (P : α → α → Prop)
(h : P a b) : ∃ x y, P x y :=
by main_tactic

example {α : Type*} (a b c: α) (P : α → α → Prop) (f : α → α)
(h₁ : P (f a) b) (h₂ : P (f c) (f a)) (h₃ : P b c) : ∃ x y, P (f x) y :=
by main_tactic

example {α : Type*} (a : α) (P : Prop) (h : P) : ∃ (z : α), P :=
by main_tactic

example {α : Type*} (a b: α) (P : α → α → Prop)
(h : P a b) : ∃ x y, ∃ (z : α), P x y :=
by main_tactic
