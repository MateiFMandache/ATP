/- The aim here is to make a prover of not equal statements
about integers, e.g. 3 = 5 → false -/

open tactic

meta def no_confusion_false_prover : expr → tactic expr
-- Argumet: the neq statement we want to prove
-- returns proof term
| `(0 = nat.succ %%n → false) := to_expr ``(@nat.no_confusion false _ _)
| `(nat.succ %%n = 0 → false) := to_expr ``(@nat.no_confusion false _ _)
| `(nat.succ %%n₁ = nat.succ %%n₂ → false) :=
  do h ← get_unused_name `h >>= intro,
    e ← to_expr ``(@nat.no_confusion false _ _ %%h),
    let tp := `((%%n₁ : ℕ) = %%n₂ → false),
    nm₁ ← get_unused_name `t,
    -- introduce previous step as a subgoal
    t ← to_expr ``(%%tp: Prop) >>= assert nm₁,
      prev ← no_confusion_false_prover tp,
      exact prev,
    return (expr.app e t)
| _ := failed

open nat

-- 0 ≠ 1
example : 0 = succ 0 → false :=
by do target >>= no_confusion_false_prover >>= exact

-- 2 ≠ 0
example : succ (succ 0) = 0 → false :=
by do target >>= no_confusion_false_prover >>= exact

-- 1 ≠ 2
example : succ 0 = succ (succ 0) → false :=
by do target >>= no_confusion_false_prover >>= exact

-- 3 ≠ 5
example : succ (succ (succ 0)) =
succ (succ (succ (succ (succ 0)))) → false :=
by do target >>= no_confusion_false_prover >>= exact
