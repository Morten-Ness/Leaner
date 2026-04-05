import Mathlib

section

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] {s : Set α}

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 := Set.div_zero_subset s.antisymm <| by simpa [mem_div] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [MulZeroClass α] {s : Set α}

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 := Set.mul_zero_subset s.antisymm <| by simpa [mem_mul] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] {s : Set α}

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 := Set.zero_div_subset s.antisymm <| by simpa [mem_div] using hs

end

section

open scoped Pointwise

variable {α : Type*}

variable [MulZeroClass α] {s : Set α}

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 := Set.zero_mul_subset s.antisymm <| by simpa [mem_mul] using hs

end
