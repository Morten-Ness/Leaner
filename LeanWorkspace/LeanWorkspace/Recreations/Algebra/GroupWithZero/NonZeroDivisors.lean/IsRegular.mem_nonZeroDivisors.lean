import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsRegular.mem_nonZeroDivisors (h : IsRegular r) : r ∈ M₀⁰ := ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩

