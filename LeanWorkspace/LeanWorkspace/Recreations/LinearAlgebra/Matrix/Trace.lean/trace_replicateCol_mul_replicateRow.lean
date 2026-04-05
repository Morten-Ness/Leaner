import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem trace_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] [NonUnitalNonAssocSemiring R]
    (a b : n → R) : Matrix.trace (replicateCol ι a * replicateRow ι b) = a ⬝ᵥ b := by
  apply Finset.sum_congr rfl
  simp [mul_apply]

