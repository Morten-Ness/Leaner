import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem notMem_nonZeroDivisors_iff :
    r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty ∨ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]

