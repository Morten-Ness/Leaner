import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 := Finset.zero_mul_subset s.antisymm <| by simpa [mem_mul] using hs

