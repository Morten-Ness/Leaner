import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem Commute.units_zpow_right (h : Commute a u) (m : ℤ) : Commute a ↑(u ^ m) := SemiconjBy.units_zpow_right h m

