import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem coeffList_C {x : R} (h : x ≠ 0) : (C x).coeffList = [x] := by
  simp [Polynomial.coeffList, List.range_succ, degree_eq_natDegree (C_ne_zero.mpr h)]

