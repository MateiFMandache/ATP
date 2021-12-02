import meta.expr

inductive side : Type
| choose : side
| given : side

open side
instance dec_side_eq : decidable_eq side :=
begin
  dunfold decidable_eq,
  dunfold decidable_rel,
  intros a b,
  exact match a, b with
    | choose, choose := is_true (eq.refl choose)
    | choose, given := is_false (λ P, side.no_confusion P)
    | given, choose := is_false (λ P, side.no_confusion P)
    | given, given := is_true (eq.refl given)
  end
end

meta structure entry : Type :=
(side : side) -- Whether we can choose, or it is given to us
(ldeps : list expr) -- logical dependancies, e.g. P → Q
(edeps : list expr) -- expression dependancies, e.g. P x

meta def directory := rbmap expr entry expr.lt_prop

meta def goals := list expr

open tactic expr
meta def new_mvar (tp : expr): tactic expr :=
do nm ← get_unused_name `m,
  return (mvar nm nm tp)

meta def process_local : expr → directory → tactic directory
-- first argument is the relevant local constant
-- second argument is the current directory
| `(Exists (λ x : %%tp, %%rest)) dir := sorry
| `(∀ x : %%tp, %%rest) dir := sorry
| single dir := sorry

meta def process_goal : expr → goals → directory → tactic (directory × goals)
-- first argument is the relevant local constant
-- second argument is the current list of goals
-- third argument is the current directory
| `(Exists (λ x : %%tp, %%rest)) gls dir := sorry
| `(∀ x : %%tp, %%rest) gls dir := sorry
| single gls dir := sorry

meta def create_directory : tactic (directory × goals) :=
do ctx ← local_context,
  tgt ← target,
  let dir : directory := mk_rbmap expr entry expr.lt_prop,
  ctx.foldl
    (λ tdir h,
    do dir ← tdir,
    process_local h dir)
    (return dir) >>=
  process_goal tgt []
