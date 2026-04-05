import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem coeffList_zero : (0 : R[X]).coeffList = [] := by
  simp [Polynomial.coeffList]

