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
    let inn := bso.1.find_index (λ pn, pn.2 = en) in
    match mi.match_group.nth indexo with 
    | some omgs :=
      match omgs.nth ino with 
      | some omg :=
        match mi.match_group.nth indexn with 
        | some nmgs :=
          match nmgs.nth inn with 
          | some nmg :=
            match mi.reference_count.find omg with
            | some rc :=
            return $ match_info.mk
              mi.build_stacks
              (mi.match_group.modify_nth
                (λ nmgs, nmgs.modify_nth
                  (λ _, omg) inn) indexn)
              ((mi.reference_count.erase nmg).insert omg (rc + 1))
              mi.group_counter
            | none := fail "error in add_to_match_group: key not found in reference_count"
            end
          | none := fail "match_groups and build_stacks out of sync"
          end
        | none := fail "match_groups and build_stacks out of sync"
        end
      | none := fail "match_groups and build_stacks out of sync"
      end
    | none := fail "match_groups and build_stacks out of sync"
    end
  | _, _ := fail "error: expression index out of range"
  end
end

meta def match_expr : expr → expr → tactic unit
| (app a₁ b₁) (app a₂ b₂)                         := match_expr a₁ a₂ >> match_expr b₁ b₂
| (mvar _ _ _) (mvar _ _ _)                       := return ()
| (local_const nm₁ _ _ _) (local_const nm₂ _ _ _) := guard (nm₁ = nm₂)
| (const nm₁ _) (const nm₂ _)                     := guard (nm₁ = nm₂)
| _ _                                             := failed


meta def mk_match_info (dir : directory) : list (expr × ℕ) → match_info → tactic match_info
-- first argument is list of subgoals with the index of the build stack
-- they appear in. Index is offset from end (not head).
-- second argument is match_info built so far
| [] m := return m
| ((subgoal, index) :: tail) m :=
first (dir.to_list.map (λ key_and_entry,
  match key_and_entry with (key, e) :=
  do tpsg ← infer_type subgoal,
    tpkey ← infer_type key,
    match_expr tpsg tpkey,
    sorry
  end)) <|> fail "no match found"

meta def initial_match_info (dir : directory) (gls : goals) : tactic (list (expr × ℕ) × match_info) :=
match (dir.find gls.head) with
  | some e :=
    return (gls.map (λ g, (g, 0)), add_build_stack (e.build_stack) empty_match_info)
  | none := fail "no entry found for first goal" end

meta def create_match_info (dir : directory) (gls : goals) : tactic match_info :=
do (gs, mi) ← initial_match_info dir gls,
  mk_match_info dir gs mi