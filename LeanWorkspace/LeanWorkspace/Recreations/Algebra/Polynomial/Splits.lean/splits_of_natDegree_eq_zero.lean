import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem splits_of_natDegree_eq_zero {f : R[X]} (hf : natDegree f = 0) :
    Polynomial.Splits f := by
  rw [← (natDegree_eq_zero.mp hf).choose_spec]; aesop

