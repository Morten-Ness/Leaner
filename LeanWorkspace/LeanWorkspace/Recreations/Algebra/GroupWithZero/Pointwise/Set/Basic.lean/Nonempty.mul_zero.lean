import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [MulZeroClass α] {s : Set α}

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 := Set.mul_zero_subset s.antisymm <| by simpa [mem_mul] using hs

