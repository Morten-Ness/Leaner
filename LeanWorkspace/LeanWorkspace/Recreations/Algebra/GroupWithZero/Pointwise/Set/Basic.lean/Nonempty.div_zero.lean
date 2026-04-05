import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] {s : Set α}

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 := Set.div_zero_subset s.antisymm <| by simpa [mem_div] using hs

