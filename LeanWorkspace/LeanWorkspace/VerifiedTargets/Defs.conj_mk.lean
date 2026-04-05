import Mathlib

variable {S M G : Type*}

variable [Group G]

theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]

