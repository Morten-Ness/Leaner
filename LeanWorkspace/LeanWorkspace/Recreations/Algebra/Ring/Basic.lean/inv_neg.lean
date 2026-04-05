import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]

