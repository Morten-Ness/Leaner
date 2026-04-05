import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem conj_iff (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b := SemiconjBy.conj_iff

