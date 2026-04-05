import Mathlib

variable {M : Type*}

variable [Monoid M] [Subsingleton Mˣ]

theorem associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y := by
  simp [Associated, Units.eq_one]

