import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b c d : G}

theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b := SemiconjBy.inv_inv_symm_iff

