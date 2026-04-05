import Mathlib

variable {R : Type*}

variable [DivisionSemiring R]

theorem Splits.of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Polynomial.Splits f := of_natDegree_le_one hf.le

