import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a := SemiconjBy.units_inv_symm_left

