import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem _root_.IsUnit.splits [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f) : Polynomial.Splits f := Polynomial.splits_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hf)

