import Quantifiers.matching

open native tactic build_type

meta def find_buildable_index (mi : match_info) : ℕ → tactic ℕ
-- argument is number of indices chaecked so far
| n := match mi.build_stacks.nth n with
  | some bs :=
    match bs with
    | ([], _) := find_buildable_index (n + 1)
    | ((bt, _) :: _, _) :=
      if (↑bt = side.choose) then return n else
      match mi.match_group.nth n with
      | some mgs :=
        match mgs with
        | mg :: _ :=
          match mi.reference_count.find mg with
          | some references :=
            if (references > 1) then find_buildable_index (n + 1) else return n
          | none := fail "Error in find_buildable_index: corrupt match_info"
          end
        | [] := fail "Error in find_buildable_index: corrupt match_info"
        end
      | none := fail "Error in find_buildable_index: corrupt match_info"
      end
    end 
  | none := fail "Deadlock" end

meta def build_proof : match_info → tactic (list expr × rb_map ℕ expr)
-- first argument is match_info to be processed
-- first output is local variables corresponding to each build stack
-- second output is local variables corresponding to each match group

-- nothing left to do case
| (match_info.mk [([], _)] _ _ _) := return ([], rb_map.mk ℕ expr)
-- introduce new local
| (match_info.mk (([], h) :: bss) ([] :: mg) rc gc) :=
do (bs_vars, mg_vars) ← build_proof (match_info.mk bss mg rc gc),
  return ((h :: bs_vars), mg_vars)
-- general case
| mi :=
do index ← find_buildable_index mi 0,
  build_tp ← match mi.build_stacks.nth index with
    | some ((bt, _) :: _, _) := return bt
    | some ([], _) := fail "Error in build_proof"
    | none := fail "Error in build_proof"
    end,
  match_group ← match mi.match_group.nth index with
    | some (mg :: mgs) := return mg
    | some [] := fail "Error in build_proof"
    | none := fail "Error in build_proof"
    end,
  reference_count ← match mi.reference_count.find match_group with
    | some rc := return rc
    | none := fail "Error in build_proof"
    end,
  (bs_vars, mg_vars) ← build_proof
    (match_info.mk
      (mi.build_stacks.modify_nth (λ bs, (bs.1.tail, bs.2)) index)
      (mi.match_group.modify_nth (λ mgs, mgs.tail) index)
      (mi.reference_count.insert match_group (reference_count - 1))
      (mi.group_counter)),
  bs_var ← match bs_vars.nth index with
    | some bsv := return bsv
    /- if we are building the goal, the index will be out of range as
    there is no bs_var for the goal. bs_var will not be used in these cases,
    so we give it a dummy value. -/
    | none := return (expr.sort level.zero)
    end,
  mg_var ← match mg_vars.find match_group with
    | some mgv := return mgv
    /- if we are building the first unit in a match group, there will not
    yet be an entry for that match group. mg_var will not be used in these cases,
    so we give it a dummy value.-/
    | none := return (expr.sort level.zero)
    end,
  match build_tp with
  | ass_ex :=
  do nmmgv ← get_unused_name `mgv,
    nmbsv ← get_unused_name `bsv,
    cases bs_var [nmmgv, nmbsv],
    mgv ← get_local nmmgv,
    bsv ← get_local nmbsv,
    return (bs_vars.modify_nth (λ _, bsv) index, mg_vars.insert match_group mgv)
  | ass_all :=
  do nmbsv ← get_unused_name `bsv,
    let my_app := expr.app bs_var mg_var,
    tp ← infer_type my_app,
    assertv nmbsv tp my_app,
    clear bs_var,
    bsv ← get_local nmbsv,
    return (bs_vars.modify_nth (λ _, bsv) index, mg_vars)
  | ass_atom :=
    return (bs_vars, mg_vars.insert match_group bs_var)
  | goal_ex :=
    to_expr ``(Exists.intro %%mg_var) >>= apply >> return (bs_vars, mg_vars)
  | goal_all :=
  do nm ← get_unused_name `mgv,mgv ← intro nm,
    return (bs_vars, mg_vars.insert match_group mgv)
  | goal_atom :=
    exact mg_var >> return (bs_vars, mg_vars)
  end
  
