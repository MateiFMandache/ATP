import Quantifiers.building

meta def tactic.interactive.main : tactic unit :=
do (dir, goals) ← create_directory,
  mi ← create_match_info dir goals,
  build_proof mi,
  tactic.skip
