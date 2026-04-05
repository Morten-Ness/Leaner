import Mathlib

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

theorem killingForm_restrict_range_ad [Module.Finite R L] :
    (killingForm R 𝔻).restrict 𝕀 = killingForm R 𝕀 := by
  rw [← (ad_isIdealMorphism R L).eq, ← LieIdeal.killingForm_eq]
  rfl

