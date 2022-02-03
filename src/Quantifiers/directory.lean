import meta.expr
import control.random
import Quantifiers.build_type

meta structure entry : Type :=
(side : side) -- Whether we can choose, or it is given to us
(ldeps : list expr) -- logical dependancies, e.g. P → Q
(edeps : list expr) -- expression dependancies, e.g. P x
(build_stack : build_stack) -- data for use at build time

open tactic expr native side

meta def directory := rb_map expr entry

meta def get_side (dir : directory) (key : expr) : tactic side :=
match dir.find key with
| some e := return e.side
| none   := failed
end

meta def get_ldeps (dir : directory) (key : expr) : tactic (list expr) :=
match dir.find key with
| some e := return e.ldeps
| none   := failed
end

meta def get_edeps (dir : directory) (key : expr) : tactic (list expr) :=
match dir.find key with
| some e := return e.edeps
| none   := failed
end

meta def get_build_stack (dir : directory) (key : expr) : tactic build_stack :=
match dir.find key with
| some e := return e.build_stack
| none   := failed
end

meta def goals := list expr

meta def new_placeholder (tp : expr): tactic expr :=
do nm ← mk_fresh_name,
  (num : fin 1000) ← random,  -- create quasi-unique display name to aid debugging
  let disp_nm := ("m" ++ to_string (num : ℕ) : name),
  return (local_const nm disp_nm binder_info.default tp)

meta def find_edeps (dir : directory): expr → tactic (list expr)
| (app f x) :=
do l₁ ← find_edeps f,
  l₂ ← find_edeps x,
  return (l₁ ++ l₂)
| (local_const nm₁ nm₂ bi tp) := guard (dir.contains (local_const nm₁ nm₂ bi tp)) >>
                                  return [local_const nm₁ nm₂ bi tp] <|> return []
| _ := return []

meta def process_local : expr → directory → list expr → build_stack → tactic directory
-- first argument is the relevant local constant
-- second argument is the current directory
-- third argument is the logical dependancies encountered so far
-- fourth argument is the current build stack
| `(Exists (λ x : %%tp, %%rest)) dir ldeps bs :=
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_placeholder tp,
  edeps ← find_edeps dir tp,
  let new_bs := (list.cons (build_type.ass_ex, new_key) bs.1, bs.2),
  let new_dir := rb_map.insert dir new_key ⟨given, ldeps, edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_local recursion_expr new_dir ldeps new_bs
| `(∀ x : %%tp, %%rest) dir ldeps bs := 
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_placeholder tp,
  edeps ← find_edeps dir tp,
  let new_bs := (list.cons (build_type.ass_all, new_key) bs.1, bs.2),
  let new_dir := rb_map.insert dir new_key ⟨choose, [], edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_local recursion_expr new_dir (list.cons new_key ldeps) new_bs
| single dir ldeps bs :=
do new_key ← new_placeholder single,
  edeps ← find_edeps dir single,
  let new_bs := (list.cons (build_type.ass_atom, new_key) bs.1, bs.2),
  return $ rb_map.insert dir new_key ⟨given, ldeps, edeps, new_bs⟩

meta def process_goal : expr → goals → directory → list expr → build_stack → tactic (directory × goals)
-- first argument is the relevant local constant
-- second argument is the current list of goals
-- third argument is the current directory
-- fourth argument is the logical dependancies encountered so far
-- fifth argument is the current build stack
| `(Exists (λ x : %%tp, %%rest)) gls dir ldeps bs := 
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_placeholder tp,
  edeps ← find_edeps dir tp,
  let new_bs := (list.cons (build_type.goal_ex, new_key) bs.1, bs.2),
  let new_dir := rb_map.insert dir new_key ⟨choose, [], edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_goal recursion_expr (list.cons new_key gls) new_dir (list.cons new_key ldeps) new_bs
| `(∀ x : %%tp, %%rest) gls dir ldeps bs := 
do f ← to_expr ``(λ x : %%tp, %%rest),
  new_key ← new_placeholder tp,
  edeps ← find_edeps dir tp,
  let new_bs := (list.cons (build_type.goal_all, new_key) bs.1, bs.2),
  let new_dir := rb_map.insert dir new_key ⟨given, ldeps, edeps, new_bs⟩,
  recursion_expr ← whnf (app f new_key),
  process_goal recursion_expr gls new_dir ldeps new_bs
| single gls dir ldeps bs := 
do new_key ← new_placeholder single,
  edeps ← find_edeps dir single,
  let new_bs := (list.cons (build_type.goal_atom, new_key) bs.1, bs.2),
  return (rb_map.insert dir new_key ⟨choose, [], edeps, new_bs⟩, list.cons new_key gls)

meta def create_directory : tactic (directory × goals) :=
do ctx ← local_context,
  tgt ← target,
  let dir : directory := rb_map.mk expr entry,
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
