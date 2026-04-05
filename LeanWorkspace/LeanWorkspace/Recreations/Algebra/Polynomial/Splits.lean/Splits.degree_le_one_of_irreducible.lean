import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.degree_le_one_of_irreducible {f : R[X]} (hf : Polynomial.Splits f)
    (h : Irreducible f) : degree f ≤ 1 := degree_le_of_natDegree_le (hf.natDegree_le_one_of_irreducible h)

