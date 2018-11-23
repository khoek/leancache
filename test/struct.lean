import tactic.linarith
import tactic.tcache

set_option trace.cache true

structure prerat :=
(n : ℤ)
(m : ℕ)
(h₁ : m ≠ 0)
(h₂ : m ≥ 0)

def mk_prerat : prerat :=
{
  n := 3,
  m := 2,
  h₁ := by c begin
    trivial
  end,
  h₂ := by c begin
    linarith
  end
}
