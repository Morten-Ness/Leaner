import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← Polynomial.mirror_mirror p, Polynomial.mirror_trailingCoeff, Polynomial.mirror_mirror p]

