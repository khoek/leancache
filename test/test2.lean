import tactic.tcache

set_option trace.cache true

namespace charlie

theorem lol : 1 + 2 = 3 := by c begin
  simp
end

end charlie
