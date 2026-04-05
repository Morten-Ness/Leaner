import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mem_bot_iff {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  simp_rw [SaturatedSubmonoid.bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

