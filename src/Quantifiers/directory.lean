import meta.expr
import control.random
import Quantifiers.build_type

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

meta instance side_has_to_tactic_format : has_to_tactic_format side :=
⟨λ s : side, match s with | choose := return "choose"
                          | given := return "given" end⟩ 

meta structure entry : Type :=
(side : side) -- Whether we can choose, or it is given to us
(ldeps : list expr) -- logical dependancies, e.g. P → Q
(edeps : list expr) -- expression dependancies, e.g. P x
(build_stack : build_stack) -- data for use at build time

meta def directory := rbmap expr entry expr.lt_prop

meta def goals := list expr

open tactic expr
meta def new_mvar (tp : expr): tactic expr :=
do nm ← mk_fresh_name,
  (num : fin 1000) ← random,  -- create quasi-unique display name to aid debugging
  let disp_nm := ("m" ++ to_string (num : ℕ) : name),
  return (mvar nm disp_nm tp)

meta def get_edeps : expr → tactic (list expr)
| (app f x) :=
do l₁ ← get_edeps f,
  l₂ ← get_edeps x,
  return (l₁ ++ l₂)
| (mvar nm₁ nm₂ tp) := return [mvar nm₁ nm₂ tp] 
| _ := return []

meta def process_local : expr → directory → list expr → build_stack → tactic directory
-- first argument is the relevant local constant
-- second argument is the current directory
-- third argument is the logical dependancies encountered so far
-- fourth argument is the current build stack
| `(Exists (λ x : %%tp, %%rest)) dir ldeps bs :=
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_mvar tp,
  edeps ← get_edeps tp,
  let new_bs := (list.cons build_type.ass_ex bs.1, bs.2),
  let new_dir := rbmap.insert dir new_key ⟨given, ldeps, edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_local recursion_expr new_dir ldeps new_bs
| `(∀ x : %%tp, %%rest) dir ldeps bs := 
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_mvar tp,
  edeps ← get_edeps tp,
  let new_bs := (list.cons build_type.ass_all bs.1, bs.2),
  let new_dir := rbmap.insert dir new_key ⟨choose, [], edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_local recursion_expr new_dir (list.cons new_key ldeps) new_bs
| single dir ldeps bs :=
do new_key ← new_mvar single,
  edeps ← get_edeps single,
  let new_bs := (list.cons build_type.ass_atom bs.1, bs.2),
  return $ rbmap.insert dir new_key ⟨given, ldeps, edeps, new_bs⟩

meta def process_goal : expr → goals → directory → list expr → build_stack → tactic (directory × goals)
-- first argument is the relevant local constant
-- second argument is the current list of goals
-- third argument is the current directory
-- fourth argument is the logical dependancies encountered so far
-- fifth argument is the current build stack
| `(Exists (λ x : %%tp, %%rest)) gls dir ldeps bs := 
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_mvar tp,
  edeps ← get_edeps tp,
  let new_bs := (list.cons build_type.goal_ex bs.1, bs.2),
  let new_dir := rbmap.insert dir new_key ⟨choose, [], edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_goal recursion_expr gls new_dir (list.cons new_key ldeps) new_bs
| `(∀ x : %%tp, %%rest) gls dir ldeps bs := 
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_mvar tp,
  edeps ← get_edeps tp,
  let new_bs := (list.cons build_type.goal_all bs.1, bs.2),
  let new_dir := rbmap.insert dir new_key ⟨given, ldeps, edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_goal recursion_expr (list.cons new_key gls) new_dir ldeps new_bs
| single gls dir ldeps bs := 
do new_key ← new_mvar single,
  edeps ← get_edeps single,
  let new_bs := (list.cons build_type.goal_atom bs.1, bs.2),
  return (rbmap.insert dir new_key ⟨choose, [], edeps, new_bs⟩, list.cons new_key gls)

meta def create_directory : tactic (directory × goals) :=
do ctx ← local_context,
  tgt ← target,
  let dir : directory := mk_rbmap expr entry expr.lt_prop,
  ctx.foldl
    (λ tdir h,
    do dir ← tdir,
    lcl ← infer_type h,
    process_local lcl dir [] ([],h) )
    (return dir) >>=
  λ dir, process_goal tgt [] dir [] ([],tgt)

meta def trace_directory (dir : directory) : tactic unit :=
dir.to_list.mfoldr (λ ⟨key, entr⟩ _,
  tactic.trace "---" >>
  trace key >>
  infer_type key >>= trace >>
  trace entr.side >>
  trace entr.ldeps >>
  trace entr.edeps >>
  trace entr.build_stack)
  ()