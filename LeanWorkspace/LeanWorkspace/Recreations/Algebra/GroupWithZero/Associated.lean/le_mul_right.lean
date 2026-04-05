import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem le_mul_right {a b : Associates M} : a ≤ a * b := ⟨b, Associated.rfl⟩

