import Mathlib

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem notMem_nonZeroDivisorsRight_iff :
    x ∉ nonZeroDivisorsRight M₀ ↔ {y | y * x = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsRight_iff] using Set.nonempty_def.symm

