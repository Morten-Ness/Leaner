import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem Commute.units_zpow_left (h : Commute ↑u a) (m : ℤ) : Commute ↑(u ^ m) a := (h.symm.units_zpow_right m).symm

