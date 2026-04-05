import Mathlib

variable {R : Type*}

variable [DivisionSemiring R]

theorem Splits.of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Polynomial.Splits f := of_degree_le_one hf.le

