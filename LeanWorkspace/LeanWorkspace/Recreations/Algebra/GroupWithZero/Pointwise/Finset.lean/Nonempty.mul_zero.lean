import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 := Finset.mul_zero_subset s.antisymm <| by simpa [mem_mul] using hs

