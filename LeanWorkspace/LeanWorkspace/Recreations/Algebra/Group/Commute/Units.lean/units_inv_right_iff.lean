import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u := SemiconjBy.units_inv_right_iff

