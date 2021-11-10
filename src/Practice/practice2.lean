/- The aim in this file is to implement a "Maze solver" that, wherever possible,
builds a term of the correct type by composing functions and constants of other types.
Care is taken to avoid infinite loops.
-/
open tactic

meta structure conclusion_and_ingredients :=
(conclusion : expr) (ingredients : list expr)

meta def to_conclusion_and_ingredients : expr → tactic conclusion_and_ingredients
| `(%%a → %%b) := do ci ← to_conclusion_and_ingredients b,
                    return {conclusion := ci.conclusion,
                            ingredients := list.cons a ci.ingredients}
| e            := return {conclusion := e, ingredients := []}

meta def my_tac : expr → expr → tactic unit 
| a b := unify a b

meta def my_match_aux (e : expr) : list expr → tactic bool
-- returns whether a given expression unifies with an expression in a list
| []       := return ff
| (a :: l) := (unify a e >> return tt) <|> return ff 

meta def my_match : list expr → list expr → tactic bool
-- returns whether a pair of lists contain two expressions which unify
| []        _  := return ff
| (a :: l₁) l₂ := do b₁ ← my_match_aux a l₂,
                    b₂ ← my_match l₁ l₂,
                    return (bor b₁ b₂)

meta def maze_solve : expr → list expr → tactic expr
| goal no_looping :=
  do l ← local_context,
    first $ l.map (λ h,
    do ht ← infer_type h >>= whnf,
      ci ← to_conclusion_and_ingredients ht,
      unify ci.conclusion goal,
      looping ← my_match no_looping ci.ingredients,
      cond looping failed skip,
      list.foldl
        (λ acc e, do acc' ← acc, e' ← e, return (expr.app acc' e'))
        (return h)
        (ci.ingredients.map (λ e,
          maze_solve e (e :: no_looping)))
    )

meta def tactic.interactive.main_tactic : tactic unit :=
do t ← target, solution ← maze_solve t [], exact solution

example {α₁ α₂ : Type} (f : α₁ → α₂) (a : α₁) : α₂ :=
by main_tactic

example {α₁ α₂ α₃ α₄ α₅ : Type}
  (f₁ : α₁ → α₂ → α₅)
  (a₁ : α₁)
  (f₂ : α₃ → α₄ → α₂)
  (a₂ : α₃)
  (f₃ : α₅ → α₃)
  (f₄ : α₂ → α₄)
  (f₅ : α₃ → α₄) : α₅ :=
by main_tactic