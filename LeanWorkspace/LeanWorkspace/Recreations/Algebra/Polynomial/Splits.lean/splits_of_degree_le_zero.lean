import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem splits_of_degree_le_zero {f : R[X]} (hf : degree f ≤ 0) :
    Polynomial.Splits f := Polynomial.splits_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

