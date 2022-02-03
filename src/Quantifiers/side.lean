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
