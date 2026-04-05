import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem dvd_eq_le : ((· ∣ ·) : Associates M → Associates M → Prop) = (· ≤ ·) := Associated.rfl

