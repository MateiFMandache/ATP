inductive build_type : Type
| ass_ex : build_type -- exists in assumption
| ass_all : build_type -- for all in assumption
| ass_atom : build_type -- conclusion of assumption
| goal_ex : build_type -- exists in goal
| goal_all : build_type -- for all in goal
| goal_atom : build_type -- conclusion of goal

meta def build_stack : Type := list build_type × expr

open build_type
meta instance build_type_has_to_format : has_to_format build_type :=
⟨λ s : build_type, match s with | ass_ex    := "ass_ex"
                                | ass_all   := "ass_all"
                                | ass_atom  := "ass_atom"
                                | goal_ex   := "goal_ex"
                                | goal_all  := "goal_all"
                                | goal_atom := "goal_atom" end⟩

instance inhabited_build_type : inhabited build_type :=
⟨goal_atom ⟩ 

meta instance build_stack_has_to_tactic_format : has_to_tactic_format build_stack :=
⟨λ s : build_stack, return (list.foldl (λ acc item, acc ++ ", " ++ item) ("[" ++ has_to_format.to_format s.1.head) (s.1.tail.map has_to_format.to_format) ++ "] " ++ has_to_format.to_format s.2)⟩