import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b c d : G}

theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ := SemiconjBy.inv_inv_symm

