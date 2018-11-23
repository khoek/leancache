meta def ctactic (α : Type) :=
tactic α

meta instance : monad ctactic :=
by dunfold ctactic; apply_instance

meta instance : monad_fail ctactic :=
by dunfold ctactic; apply_instance

meta instance : alternative ctactic :=
by dunfold ctactic; apply_instance

namespace cache

meta def save_info (p : pos) : ctactic unit :=
do s ← tactic.read,
   tactic.save_info_thunk p (λ _, s.to_format tt)

meta def step {α : Type} (c : ctactic α) : ctactic unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : _root_.nat) (c : ctactic α) : ctactic unit :=
tactic.istep line0 col0 line col c

meta def execute (c : ctactic unit) : tactic unit :=
c

namespace interactive

meta def itactic := ctactic unit

meta def pass : ctactic unit := return ()

end interactive

end cache
