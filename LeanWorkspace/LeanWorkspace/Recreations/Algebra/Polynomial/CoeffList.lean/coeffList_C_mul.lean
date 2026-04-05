import Mathlib

variable {R : Type*}

variable [Semiring R] [NoZeroDivisors R] (P : R[X])

theorem coeffList_C_mul {x : R} (hx : x ≠ 0) : (C x * P).coeffList = P.coeffList.map (x * ·) := by
  by_cases hp : P = 0
  · simp [hp]
  · simp [Polynomial.coeffList, Polynomial.degree_C hx]

