import Mathlib

variable {M : Type*}

theorem Associated.isUnit_iff [Monoid M] {a b : M} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b := ⟨h.isUnit, Associated.symm h.isUnit⟩

