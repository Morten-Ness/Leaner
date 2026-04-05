import Mathlib

variable {G M S : Type*}

variable [DivisionMonoid G] {a b : G}

theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [Commute.eq hab, mul_inv_rev]

