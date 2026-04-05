import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] {s : Set α}

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 := Set.zero_div_subset s.antisymm <| by simpa [mem_div] using hs

