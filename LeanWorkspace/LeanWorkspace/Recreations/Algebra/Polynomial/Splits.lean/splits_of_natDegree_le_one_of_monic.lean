import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem splits_of_natDegree_le_one_of_monic {f : R[X]} (hf : f.natDegree ≤ 1) (h : Monic f) :
    f.Splits := Polynomial.splits_of_natDegree_le_one_of_invertible hf (h.leadingCoeff ▸ invertibleOne)

