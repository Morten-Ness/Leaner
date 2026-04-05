import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem splits_of_degree_le_one_of_invertible {f : R[X]}
    (hf : f.degree ≤ 1) (h : Invertible f.leadingCoeff) : f.Splits := Polynomial.splits_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hf) h

