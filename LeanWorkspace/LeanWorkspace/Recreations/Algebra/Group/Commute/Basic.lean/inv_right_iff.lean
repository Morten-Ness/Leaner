import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b := SemiconjBy.inv_right_iff

