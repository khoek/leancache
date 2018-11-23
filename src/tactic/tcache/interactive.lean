import tactic.where
import .io
import .serial

universe u

open tactic

namespace tcache

declare_trace cache .

meta def cache_trace {α : Type u} [has_to_tactic_format α] (a : α) : tactic unit :=
  when_tracing `cache $ tactic.trace a

meta def cache_file_name (ns n : name) : string :=
CACHE_DIR ++ "/" ++ to_string n ++ ".leancache"

meta def try_cache (ns n : name) : tactic unit := do
  n ← tactic.decl_name,
  pf ← tactic.unsafe_run_io $ file_read $ cache_file_name ns n,
  exact $ expr.deserialise pf,
  when_tracing `cache $ tactic.trace format!"{ns}, {n}: successfully recalled cached proof"

meta def put_cache (ns n : name) (e : expr) : tactic unit := do
  n ← tactic.decl_name,
  tactic.unsafe_run_io $ file_write (cache_file_name ns n) e.serialise

meta def execute_capture (ns n : name) (t : tactic unit) : tactic expr := do
  cache_trace format!"{ns}, {n}: regenerating cached proof",
  [m] ← get_goals,
  t >> done,
  when_tracing `cache $ tactic.trace format!"{ns}, {n}: success",
  tactic.instantiate_mvars m

end tcache

open tcache

meta def tactic.interactive.c (t : tactic.interactive.itactic) (ns : interactive.parse lean.parser.get_namespace) : tactic unit := do
  n ← tactic.decl_name,
  try_cache ns n <|> execute_capture ns n t >>= put_cache ns n
