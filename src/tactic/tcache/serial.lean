import .common

universe u

namespace name

meta def serialise (n : name) : string := sformat!"{n}`"

private meta def deserialise_core_aux : list char → string → name → name × list char
| [] s p := (p, [])
| ('`' :: rest) s p := (name.mk_string s p, rest)
| ('.' :: rest) s p := deserialise_core_aux rest "" $ name.mk_string s p
| (c :: rest) s p := deserialise_core_aux rest (s ++ to_string c) p

meta def deserialise_core (l : list char) : name × list char :=
deserialise_core_aux l "" name.anonymous

meta def deserialise (l : string) : name :=
prod.fst $ deserialise_core l.to_list

end name

namespace string

meta def serialise (s : string) : string := sformat!"{s}`"

private meta def deserialise_aux : list char → string → string × list char
| [] p := (p, [])
| ('`' :: rest) p := (p, rest)
| (c :: rest) p := deserialise_aux rest (p ++ to_string c)

meta def deserialise_core (l : list char) : string × list char :=
deserialise_aux l ""

meta def deserialise (l : string) : string :=
prod.fst $ deserialise_core l.to_list

end string

namespace nat

meta def serialise (n : nat) : string := sformat!"{n}`"

meta def deserialise_core (l : list char) : nat × list char :=
let (s, rest) := string.deserialise_core l in (s.to_nat, rest)

meta def deserialise (l : string) : nat :=
prod.fst $ deserialise_core l.to_list

end nat

namespace level

meta def serialise : level → string
| level.zero := "0"
| (level.succ l) := "+" ++ l.serialise
| (level.max a b) := "m" ++ a.serialise ++ "" ++ b.serialise
| (level.imax a b) := "i" ++ a.serialise ++ "" ++ b.serialise
| (level.param n) := error "level.param not implemented"
| (level.mvar n) := error "level.mvar not implemented"

meta def deserialise_core : list char → level × list char
| ('0' :: rest) := (level.zero, rest)
| ('+' :: rest) := let (lvl, rest) := deserialise_core rest in (level.succ lvl, rest)
| ('m' :: rest) :=
  let (a, rest) := deserialise_core rest in
  let (b, rest) := deserialise_core rest in
  (level.max a b, rest)
| ('i' :: rest) :=
  let (a, rest) := deserialise_core rest in
  let (b, rest) := deserialise_core rest in
  (level.imax a b, rest)
| _ := error "bad level"

meta def deserialise (l : string) : level :=
prod.fst $ deserialise_core l.to_list

end level

namespace binder_info

meta def serialise : binder_info → string
| binder_info.default := "d"
| binder_info.implicit := "i"
| binder_info.strict_implicit := "s"
| binder_info.inst_implicit := "m"
| binder_info.aux_decl := "a"

meta def deserialise_core : list char → binder_info × list char
| ('d' :: rest) := (binder_info.default, rest)
| ('i' :: rest) := (binder_info.implicit, rest)
| ('s' :: rest) := (binder_info.strict_implicit, rest)
| ('m' :: rest) := (binder_info.inst_implicit, rest)
| ('a' :: rest) := (binder_info.aux_decl, rest)
| _ := (binder_info.default, [])

meta def deserialise (l : string) : binder_info :=
prod.fst $ deserialise_core l.to_list

end binder_info

namespace list

private meta def deserialise_core_aux {α : Type u} (p : list char → α × list char) : ℕ → list char → list α × list char
| 0 l := ([], l)
| (n + 1) l :=
  let (nm, rest) := p l in
  let (others, rest) := deserialise_core_aux n rest in
  (nm :: others, rest)

meta def deserialise_core {α : Type u} (p : list char → α × list char) (l : list char) : list α × list char :=
let (n, rest) := nat.deserialise_core l in
deserialise_core_aux p n rest

meta def deserialise {α : Type u} (p : list char → α × list char) (l : string) : list α :=
prod.fst $ deserialise_core p l.to_list

end list

namespace expr

meta def serialise : expr → string
| (expr.const n l) := sformat!"c{n}`{l.length}`{string.intercalate \"\" (l.map level.serialise)}"
| (expr.app f a) := sformat!"a{f.serialise}{a.serialise}"
| (expr.sort l) := sformat!"s{l.serialise}"
| (expr.pi n bi t v) := sformat!"p{n}`{bi.serialise}{t.serialise}{v.serialise}"
| (expr.lam n bi t v) := sformat!"l{n}`{bi.serialise}{t.serialise}{v.serialise}"
| (expr.var n) := sformat!"v{n}`"
| e := sformat!"??e : {e.to_raw_fmt}"

meta mutual def deserialise_core, deserialise_binder_data
with deserialise_core : list char → expr × list char
| [] := error "hit end"
| ('c' :: rest) :=
  let (n, rest) := name.deserialise_core rest in
  let (l, rest) := list.deserialise_core level.deserialise_core rest in do
  (expr.const n l, rest)
| ('s' :: rest) :=
  let (l, rest) := level.deserialise_core rest in do
  (expr.sort l, rest)
| ('v' :: rest) :=
  let (n, rest) := nat.deserialise_core rest in do
  (expr.var n, rest)
| ('a' :: rest) := do
  let (f, rest) := deserialise_core rest,
  let (a, rest) := deserialise_core rest,
  (expr.app f a, rest)
| ('p' :: rest) := do
  let (n, bi, t, v, rest) := deserialise_binder_data rest,
  (expr.pi n bi t v, rest)
| ('l' :: rest) := do
  let (n, bi, t, v, rest) := deserialise_binder_data rest,
  (expr.lam n bi t v, rest)
| (c :: rest) := error sformat!"stopped at '{c}'"
with deserialise_binder_data : list char → name × binder_info × expr × expr × list char
| l :=
  let (n, rest) := name.deserialise_core l in
  let (bi, rest) := binder_info.deserialise_core rest in
  let (t, rest) := deserialise_core rest in
  let (v, rest) := deserialise_core rest in
  (n, bi, t, v, rest)

meta def deserialise (s : string) : expr :=
prod.fst $ deserialise_core s.to_list

end expr
