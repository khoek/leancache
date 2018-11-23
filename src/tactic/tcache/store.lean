import .io
import .serial

universe u

open tactic

namespace tcache

declare_trace cache .

meta def ctrace {α : Type u} [has_to_tactic_format α] (a : thunk α) : tactic unit := do
  f ← has_to_tactic_format.to_tactic_format $ a (),
  when_tracing `cache $ tactic.trace $ format!"tc: {f}"

meta def hash_goal (e : expr) : tactic ℕ := do
  t ← infer_type e,
  return t.hash

meta def hash_goals (n : name) : tactic string := do
  -- FIXME this xor is probably really slow
  v ← get_goals >>= list.mfoldl (λ v d, nat.lxor v <$> hash_goal d) 0,
  return sformat!"{n}.{v}"

meta def cache_file_name (hash : string) : string :=
CACHE_DIR ++ "/" ++ hash ++ ".leancache"

meta def try_cache (ns n : name) (hash : string) : tactic unit := do
  pf ← unsafe_run_io $ file_read $ cache_file_name hash,
  exact $ expr.deserialise pf,
  ctrace format!"@{hash} - successfully recalled cached proof"

meta def put_cache (ns n : name) (hash : string) (e : expr) : tactic unit := do
  unsafe_run_io $ file_write (cache_file_name hash) e.serialise

meta def execute_capture (ns n : name) (t : tactic unit) : tactic expr := do
  [m] ← get_goals,
  t >> done,
  instantiate_mvars m

meta def try_recompute (ns n : name) (hash : string) (t : tactic unit) : tactic unit := do
  ctrace format!"@{hash} - regenerating proof",
  e ← execute_capture ns n t,
  ctrace format!"@{hash} - success",
  put_cache ns n hash e

meta def discharge_goals (ns : name) (t : tactic unit) : tactic unit := do
  n ← decl_name,
  hash ← hash_goals n,
  try_cache ns n hash <|> try_recompute ns n hash t

end tcache
