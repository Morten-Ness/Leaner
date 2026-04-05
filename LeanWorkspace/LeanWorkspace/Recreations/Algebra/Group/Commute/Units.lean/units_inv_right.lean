import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ := SemiconjBy.units_inv_right

