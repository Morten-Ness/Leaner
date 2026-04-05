import Mathlib

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem notMem_nonZeroDivisorsLeft_iff :
    x ∉ nonZeroDivisorsLeft M₀ ↔ {y | x * y = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsLeft_iff] using Set.nonempty_def.symm

