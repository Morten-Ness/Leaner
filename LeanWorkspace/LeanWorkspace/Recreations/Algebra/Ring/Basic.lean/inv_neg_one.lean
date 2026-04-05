import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem inv_neg_one : (-1 : R)⁻¹ = -1 := by rw [← neg_inv, inv_one]

