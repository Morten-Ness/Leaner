FAIL
import Mathlib

variable {M : Type*}

variable [MulOneClass M]

theorem gc_saturation : GaloisConnection (Submonoid.saturation (M := M)) SaturatedSubmonoid.toSubmonoid := by
  intro s t
  constructor
  · intro h
    exact Submonoid.saturation_le.2 h
  · intro h
    exact Submonoid.le_saturation.2 h
