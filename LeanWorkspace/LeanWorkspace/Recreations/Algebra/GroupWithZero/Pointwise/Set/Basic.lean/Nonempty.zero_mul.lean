import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [MulZeroClass α] {s : Set α}

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 := Set.zero_mul_subset s.antisymm <| by simpa [mem_mul] using hs

