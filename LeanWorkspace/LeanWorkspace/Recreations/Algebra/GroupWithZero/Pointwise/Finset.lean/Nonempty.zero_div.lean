import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 := Finset.zero_div_subset s.antisymm <| by simpa [mem_div] using hs

