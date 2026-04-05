import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b := SemiconjBy.inv_symm_left_iff

