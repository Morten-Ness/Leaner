import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_mul {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff ≠ 0) :
    Polynomial.reverse (f * g) = Polynomial.reverse f * Polynomial.reverse g := by
  unfold Polynomial.reverse
  rw [natDegree_mul' fg, Polynomial.reflect_mul f g rfl.le rfl.le]

