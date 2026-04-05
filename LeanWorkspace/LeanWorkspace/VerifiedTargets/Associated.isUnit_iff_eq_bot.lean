import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem isUnit_iff_eq_bot {a : Associates M} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one, Associates.bot_eq_one]

