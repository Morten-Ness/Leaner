import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_eraseLead_add_one (h : f.nextCoeff ≠ 0) :
    f.eraseLead.natDegree + 1 = f.natDegree := by
  rw [Polynomial.natDegree_eraseLead h, tsub_add_cancel_of_le]
  exact natDegree_pos_of_nextCoeff_ne_zero h

