import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem conj (comm : Commute a b) (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) := (Commute.conj_iff h).mpr comm

