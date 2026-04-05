import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b : G}

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := DivisionMonoid.mul_inv_rev _ _

