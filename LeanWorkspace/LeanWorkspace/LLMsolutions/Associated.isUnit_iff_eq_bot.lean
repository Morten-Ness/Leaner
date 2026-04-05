import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem isUnit_iff_eq_bot {a : Associates M} : IsUnit a ↔ a = ⊥ := by
  simpa using Associates.isUnit_iff_eq_bot (a := a)
