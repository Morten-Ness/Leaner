import Mathlib

variable {M : Type*}

theorem bot_eq_one [Monoid M] : (⊥ : Associates M) = 1 := Associated.rfl

