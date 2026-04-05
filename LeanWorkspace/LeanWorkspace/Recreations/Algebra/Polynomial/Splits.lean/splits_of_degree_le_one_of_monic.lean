import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem splits_of_degree_le_one_of_monic {f : R[X]} (hf : f.degree ≤ 1) (h : Monic f) :
    f.Splits := Polynomial.splits_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hf) h

