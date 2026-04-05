import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem notMem_nonZeroDivisors_iff_right : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]

