import tactic.where
import .store

open tactic

meta def tactic.interactive.c (t : interactive.itactic) (ns : interactive.parse lean.parser.get_namespace) : tactic unit := do
  tcache.discharge_goals ns t
