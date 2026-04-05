import Mathlib

variable {α : Type u}

theorem ne_one_iff_exists {x : WithOne α} : x ≠ 1 ↔ ∃ a : α, ↑a = x := Option.ne_none_iff_exists

