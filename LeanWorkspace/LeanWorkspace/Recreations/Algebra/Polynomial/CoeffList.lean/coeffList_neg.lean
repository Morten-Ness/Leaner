import Mathlib

variable {R : Type*}

variable [Ring R] (P : R[X])

theorem coeffList_neg : (-P).coeffList = P.coeffList.map (-·) := by
  by_cases hp : P = 0
  · rw [hp, Polynomial.coeffList_zero, neg_zero, Polynomial.coeffList_zero, List.map_nil]
  · simp [Polynomial.coeffList]

