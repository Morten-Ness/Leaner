import Mathlib

variable {R : Type*}

variable [DivisionSemiring R]

theorem Splits.of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Polynomial.Splits f := of_natDegree_le_one (natDegree_le_of_degree_le hf)

