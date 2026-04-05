import Mathlib

variable {M : Type*}

variable [MulOneClass M]

theorem bot_def : (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥ := rfl

