import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 := Finset.div_zero_subset s.antisymm <| by simpa [mem_div] using hs

