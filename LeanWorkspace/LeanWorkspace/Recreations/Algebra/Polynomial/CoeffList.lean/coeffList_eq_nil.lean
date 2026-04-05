import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem coeffList_eq_nil {P : R[X]} : P.coeffList = [] ↔ P = 0 := by
  simp [Polynomial.coeffList]

