import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem notMem_nonZeroDivisors_iff_left : r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_left, Set.nonempty_def]

