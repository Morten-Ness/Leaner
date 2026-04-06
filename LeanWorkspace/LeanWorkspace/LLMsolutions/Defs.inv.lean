FAIL
import Mathlib

variable {G M S : Type*}

variable [DivisionMonoid G] {a b : G}

theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  exact hab.mul_inv_rev.symm
