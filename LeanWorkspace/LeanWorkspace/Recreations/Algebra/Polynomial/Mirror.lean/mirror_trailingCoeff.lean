import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, trailingCoeff, Polynomial.mirror_natTrailingDegree, Polynomial.coeff_mirror,
    revAt_le (Nat.le_add_left _ _), add_tsub_cancel_right]

