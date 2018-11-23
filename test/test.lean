import system.io
import tactic.where
import tactic.tcache

open tactic

theorem lol : 1 + 1 = 2 := begin
  simp
end

theorem lol' (x : ℕ) : 1 = 1 := rfl

run_cmd (do
  let n := `lol',
  e ← get_env,
  d ← e.get n,
  let s := expr.deserialise d.type.serialise,
  let t := expr.deserialise d.value.serialise,
  -- tactic.trace d.value.serialise,
  -- tactic.trace $ d.type.to_raw_fmt ++ "\n",
  -- tactic.trace $ s.to_raw_fmt ++ "\n",
  -- tactic.trace $ d.value.to_raw_fmt ++ "\n",
  -- tactic.trace t.to_raw_fmt,
  e ← e.add $ declaration.thm (n ++ "v2") [] s (task.pure t),
  set_env e
)

run_cmd (do
  e ← get_env,
  d ← e.get `lol,
  match d with
  | declaration.thm n l t v := tactic.trace v.get.to_raw_fmt
  | _ := skip
  end
)
















