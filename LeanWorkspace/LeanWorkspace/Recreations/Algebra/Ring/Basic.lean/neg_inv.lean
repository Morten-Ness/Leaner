import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

