import Quantifiers.directory

open tactic
open expr

open native

meta structure match_info : Type :=
(build_stacks : list build_stack)
(match_group : list (list ℕ)) -- lists synchronised with the build stacks indicating
                              -- which match group each element is in.
(reference_count : rb_map ℕ ℕ)
(group_counter : ℕ)

meta def empty_match_info : match_info :=
match_info.mk [] [] (rb_map.mk ℕ ℕ) 0

meta def add_build_stack (bs : build_stack) (mi : match_info) : match_info :=
let (final_counter, initial_match_group, reference_count) := list.foldl
  (λ acc item, match (acc : ℕ × list ℕ × rb_map ℕ ℕ) with (c, mg, rc) :=
    (c + 1, c :: mg, rc.insert c 1)
  end)
  (mi.group_counter, [], mi.reference_count)
  bs.1
in match_info.mk (bs :: mi.build_stacks) (initial_match_group :: mi.match_group)
  reference_count final_counter

meta def add_to_match_group (original : expr × ℕ) (new : expr × ℕ) (mi : match_info)
: tactic match_info :=
match original, new with (eo, indexo), (en, indexn) :=
  let obso := mi.build_stacks.nth (mi.build_stacks.length - 1 - indexo) in
  let obsn := mi.build_stacks.nth (mi.build_stacks.length - 1 - indexn) in
  match obso, obsn with | some bso, some bsn :=
    let ino := bso.1.find_index (λ po, po.2 = eo) in
    let inn := bsn.1.find_index (λ pn, pn.2 = en) in
    match mi.match_group.nth (mi.build_stacks.length - 1 - indexo) with 
    | some omgs :=
      match omgs.nth ino with 
      | some omg :=
        match mi.match_group.nth (mi.build_stacks.length - 1 - indexn) with 
        | some nmgs :=
          match nmgs.nth inn with 
          | some nmg :=
            match mi.reference_count.find omg with
            | some rc :=
            return $ match_info.mk
              mi.build_stacks
              (mi.match_group.modify_nth
                (λ nmgs, nmgs.modify_nth
                  (λ _, omg) inn) (mi.build_stacks.length - 1 - indexn))
              ((mi.reference_count.erase nmg).insert omg (rc + 1))
              mi.group_counter
            | none := trace "error in add_to_match_group: key not found in reference_count" >> failed
            end
          | none := trace "match_groups and build_stacks out of sync" >> failed
          end
        | none := trace "match_groups and build_stacks out of sync" >> failed
        end
      | none := trace "match_groups and build_stacks out of sync" >> failed
      end
    | none := trace "match_groups and build_stacks out of sync" >> failed
    end
  | _, _ := trace "error: expression index out of range" >> failed
  end
end

meta def match_expr (dir : directory) : expr → expr → tactic unit
| (app a₁ b₁) (app a₂ b₂)           := match_expr a₁ a₂ >> match_expr b₁ b₂
| (local_const nm₁ dispnm₁ bi₁ tp₁)
  (local_const nm₂ dispnm₂ bi₂ tp₂) := guard (nm₁ = nm₂) <|>
                                       guard (dir.contains (local_const nm₁ dispnm₁ bi₁ tp₁)) >>
                                       guard (dir.contains (local_const nm₂ dispnm₂ bi₂ tp₂))
| (const nm₁ _) (const nm₂ _)       := guard (nm₁ = nm₂)
| _ _                               := failed

meta def head_is (l: list expr) (e : expr) : bool :=
match l with
| (e' :: es) := if e' = e then tt else ff
| [] := ff
end

meta def elaborate_match (dir : directory) (index : ℕ) (new_index : ℕ) :
list expr → list expr → list expr → list (expr × ℕ) → list (expr × ℕ)
→ list expr → match_info →
tactic (list (expr × ℕ) × list (expr × ℕ) × match_info)
-- first argument is ldeps of new component of current match
-- second argument is edeps of new component of current match
-- third argument is edeps of old component of current match
-- fourth argument is new subgoals, in reverse order
-- fifth argument is old subgoals
-- sixth argument is list of expressions to be checked in the right order
-- seventh argument is current match info
-- first return value is new subgoals, in reverse order
-- second return value is remaining old subgoals
-- third return value is resulting match info
| (ldep :: ldeps) nedeps oedeps new_subgoals old_subgoals (e :: es) mi :=
if e ∈ nedeps then
  match oedeps.nth (nedeps.index_of e) with
  | some oedep :=
  if e = ldep then
    if (oedep, index) ∈ old_subgoals then
      do new_mi ← add_to_match_group (oedep, index) (e, new_index) mi,
      elaborate_match ldeps (nedeps.erase e) (oedeps.erase oedep)
        ((ldep, new_index) :: new_subgoals)
        (old_subgoals.erase (oedep, index)) es new_mi
    else
      do new_mi ← add_to_match_group (oedep, index) (e, new_index) mi,
      elaborate_match ldeps (nedeps.erase e) (oedeps.erase oedep)
        new_subgoals old_subgoals es new_mi
  else
    if (oedep, index) ∈ old_subgoals then
      do new_mi ← add_to_match_group (oedep, index) (e, new_index) mi,
      elaborate_match (ldep :: ldeps) (nedeps.erase e) (oedeps.erase oedep)
        new_subgoals (old_subgoals.erase (oedep, index)) es new_mi
    else
      failed -- can't match given with given
  | none := trace "oedeps and nedeps out of sync" >> failed
  end
else
  if e = ldep then
    elaborate_match ldeps nedeps oedeps
      ((ldep, new_index) :: new_subgoals) old_subgoals es mi
  else
    elaborate_match (ldep :: ldeps) nedeps oedeps
      new_subgoals old_subgoals es mi
| [] nedeps oedeps new_subgoals old_subgoals (e :: es) mi :=
if e ∈ nedeps then
  match oedeps.nth (nedeps.index_of e) with
  | some oedep :=
    if (oedep, index) ∈ old_subgoals then
      do new_mi ← add_to_match_group (oedep, index) (e, new_index) mi,
      elaborate_match [] (nedeps.erase e) (oedeps.erase oedep)
        new_subgoals (old_subgoals.erase (oedep, index)) es new_mi
    else
      failed -- can't match given with given
  | none := fail "oedeps and nedeps out of sync"
  end
else
  elaborate_match [] nedeps oedeps
    new_subgoals old_subgoals es mi
| ldeps (nedep :: nedeps) [] new_subgoals old_subgoals es mi :=
  fail "Error in elaborate_match: unequal numbers of edeps"
| ldeps [] (oedep :: oedeps) new_subgoals old_subgoals es mi :=
  fail "Error in elaborate_match: unequal numbers of edeps"
| (ldep :: ldeps) [] [] new_subgoals old_subgoals es mi :=
  elaborate_match ldeps [] [] ((ldep, new_index) :: new_subgoals) old_subgoals es mi
| [] [] [] new_subgoals old_subgoals es mi := return (new_subgoals, old_subgoals, mi)
| _ _ _ new_subgoals old_subgoals [] mi :=
  fail "Error in elaborate_match: ran out of expressions to check too soon"

meta def old_no_looping : list (expr × ℕ) → list (expr × ℕ) → list (list expr)
→ tactic (list (list expr))
-- first argument is list of old subgoals left
-- second argument is full list of old subgoals
-- third argument is no_looping synchronised  with second argument
-- return value is no_looping synchronised with first argument
| (g₁ :: g₁s) (g₂ :: g₂s) (nl :: nls) :=
  if g₁ = g₂ then
    do nls' ← old_no_looping g₁s g₂s nls,
    return (nl :: nls')
     else old_no_looping g₁s (g₂ :: g₂s) nls 
| (g₁ :: g₁s) (g₂ :: g₂s) [] := trace "Error in old_no_looping" >> failed
| (g₁ :: g₁s) [] _ := trace "Error in old_no_looping" >> failed
| [] _ _ := return []

meta def mk_match_info (dir : directory) : list (expr × ℕ) → match_info → list (list expr) →
tactic match_info
-- first argument is list of subgoals with the index of the build stack
-- they appear in. Index is offset from end (not head).
-- second argument is match_info built so far
-- third argument is list of expressions to avoid matching with (avoid infinite loops).
-- we keep a seperate no_looping list for each goal
| [] mi no_looping := return mi
| ((subgoal, index) :: tail) mi no_looping:=
first (dir.to_list.map (λ key_and_entry,
  match key_and_entry with (key, e) :=
  do tpsg ← infer_type subgoal,
    tpkey ← infer_type key,
    match_expr dir tpsg tpkey,
    guard (e.side = side.given),
    -- in-matching not currently supported, so do not match if entry is from goal
    match e.build_stack with | ((build_type.goal_all, _) :: _, _) := failed | _ := skip end,
    guard (key ∉ no_looping.head),
    let new_index := mi.build_stacks.length,
    let mi₁ := add_build_stack e.build_stack mi,
    mi₂ ← add_to_match_group (subgoal, index) (key, new_index) mi₁,
    oedeps ← get_edeps dir subgoal,
    nbs ← get_build_stack dir key,
    (new_sgs, old_sgs, mi₃) ← elaborate_match dir index new_index e.ldeps e.edeps oedeps [] tail
      (nbs.1.map (λ b, b.2)) mi₂,
    onl ← old_no_looping old_sgs tail no_looping.tail,
    mk_match_info (list.reverse new_sgs ++ old_sgs) mi₃
    (new_sgs.map (λ _, key :: no_looping.head) ++ onl)
  end)) <|> fail "no match found"

meta def initial_match_info (dir : directory) (gls : goals) :
tactic (list (expr × ℕ) × match_info) :=
match (dir.find gls.head) with
  | some e :=
    return (gls.map (λ g, (g, 0)), add_build_stack (e.build_stack) empty_match_info)
  | none := fail "no entry found for first goal"
end

meta def create_match_info (dir : directory) (gls : goals) : tactic match_info :=
do (gs, mi) ← initial_match_info dir gls,
  mk_match_info dir gs mi (gls.map (λ g, [g]))

meta def trace_match_info (mi : match_info) : tactic unit :=
trace mi.build_stacks >>
trace mi.match_group >>
trace mi.reference_count.to_list
