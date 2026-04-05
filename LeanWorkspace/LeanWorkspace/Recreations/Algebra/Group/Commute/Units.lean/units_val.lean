import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem units_val : Commute u₁ u₂ → Commute (u₁ : M) u₂ := SemiconjBy.units_val

