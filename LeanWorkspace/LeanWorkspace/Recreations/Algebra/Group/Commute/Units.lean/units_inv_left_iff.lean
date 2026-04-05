import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a := SemiconjBy.units_inv_symm_left_iff

